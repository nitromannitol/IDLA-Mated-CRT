import MatedCRT.FirstPass.Derived.RevuzIntervalShift
import MatedCRT.FirstPass.Derived.PlanarGaussianLowerBound

/-!
# The expected clock integral of a set of positive Revuz measure is infinite

Let `A` be a positive continuous additive functional of planar Brownian motion and `g ≥ 0` a measurable function
with `∫ g dμ_A > 0`, where `μ_A` is the Revuz measure of `A` with respect to Lebesgue measure. Then for every
starting point `x`,
`E_x ∫_{(0, ∞)} g(B_s) dA_s = ∞`.

This is the expectation form of the Harris recurrence of the time-changed process (Revuz–Yor (1999), Chapter X,
§3; Fukushima–Oshima–Takeda (2011), §6.2). The proof is short:

* by the additivity of `A` on the window `(t, t + 1]` and the simple Markov property at time `t`,
  `E_x ∫_{(t, t+1]} g(B_s) dA_s = E_x φ(B_t)` with `φ(y) = E_y ∫_{(0,1]} g(B_s) dA_s`;
* `∫ φ dy = ∫ g dμ_A > 0`, so `φ` has positive integral over some disc `{|y| ≤ R}`;
* the planar Gaussian density at time `t ≥ 1` is at least `(2πt)⁻¹ exp(-(R + |x|)²)` on that disc, and
  `∑_{k ≥ 1} 1/k = ∞`.

## Main results

* `lintegral_setLIntegral_Ioc_eq_lintegral_shift`: the window `(t, t + 1]` as an expectation of the shifted path;
* `ofReal_mul_setLIntegral_le_lintegral_setLIntegral_Ioc`: the Gaussian lower bound for one window;
* `exists_setLIntegral_closedBall_ne_zero`: a disc on which `φ` has positive integral;
* `lintegral_setLIntegral_Ioi_eq_top`: `E_x ∫_{(0, ∞)} g(B_s) dA_s = ∞`.
-/

open MeasureTheory Set Filter Metric Real
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- **The clock integral over a unit window is an expectation of the shifted path.** For a positive continuous
additive functional `A`, `E_x ∫_{(t, t+1]} g(B_s) dA_s = E_x Φ(θ_t B)`, where `Φ(ω)` is the integral of `g`
against the occupation measure of `ω` on `(0, 1]` for the regularized clock. -/
theorem lintegral_setLIntegral_Ioc_eq_lintegral_shift {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (x : ℂ) (t : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ s in Ioc (t : ℝ) (t + 1), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x =
      ∫⁻ ω, ∫⁻ y, g y ∂occupationMeasure (fun u => regularize A u (ContinuousPath.shift t ω))
        (ContinuousPath.shift t ω) ∂planarLaw x := by
  refine lintegral_congr_ae ((ae_setLIntegral_Ioc_shift_eq_occupationMeasure hA x t hg).mono fun ω hω => ?_)
  have hs : LatticeProb.pathShift ω t = ContinuousPath.shift t ω := congrFun (pathShift_eq_shift t) ω
  dsimp only
  rw [hω, hs]

/-- The clock integral over a unit window is almost everywhere measurable in the path. -/
theorem aemeasurable_setLIntegral_Ioc {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A)
    (x : ℂ) (t : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    AEMeasurable (fun ω : ContinuousPath ℂ => ∫⁻ s in Ioc (t : ℝ) (t + 1), g (ω s.toNNReal)
      ∂(stieltjesOfNNReal fun u => A u ω).measure) (planarLaw x) := by
  have hΦ : Measurable fun ω' : ContinuousPath ℂ =>
      ∫⁻ y, g y ∂occupationMeasure (fun u => regularize A u ω') ω' :=
    (Measure.measurable_lintegral hg).comp (measurable_occupationMeasure_regularize hA.meas)
  exact (hΦ.comp (measurable_pathShift_const t)).aemeasurable.congr
    ((ae_setLIntegral_Ioc_shift_eq_occupationMeasure hA x t hg).mono fun ω h => h.symm)

/-- **Gaussian lower bound for the clock integral over one window.** For `t > 0` and `R`,
`E_x ∫_{(t, t+1]} g(B_s) dA_s ≥ (2πt)⁻¹ exp(-(R + |x|)²/t) ∫_{|y| ≤ R} φ(y) dy`, where
`φ(y) = E_y ∫ g d(occupation measure of the regularized clock on (0, 1])`. -/
theorem ofReal_mul_setLIntegral_le_lintegral_setLIntegral_Ioc {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (x : ℂ) {t : ℝ≥0} (ht : t ≠ 0) (R : ℝ) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ENNReal.ofReal ((2 * π * t)⁻¹ * Real.exp (-(R + ‖x‖) ^ 2 / t)) *
        ∫⁻ y in closedBall 0 R, ∫⁻ ω, ∫⁻ z, g z ∂occupationMeasure (fun u => regularize A u ω) ω
          ∂planarLaw y ≤
      ∫⁻ ω, ∫⁻ s in Ioc (t : ℝ) (t + 1), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x := by
  rw [lintegral_setLIntegral_Ioc_eq_lintegral_shift hA x t hg]
  exact ofReal_mul_setLIntegral_le_lintegral_shift x ht R
    ((Measure.measurable_lintegral hg).comp (measurable_occupationMeasure_regularize hA.meas))

/-- **A disc carrying positive mass.** If `∫ g dμ_A ≠ 0`, then for some `n` the function
`φ(y) = E_y ∫ g d(occupation measure of the regularized clock on (0, 1])` has nonzero integral over the closed
disc of radius `n`. -/
theorem exists_setLIntegral_closedBall_ne_zero {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hpos : ∫⁻ y, g y ∂revuz planarLaw A ≠ 0) :
    ∃ n : ℕ, ∫⁻ y in closedBall (0 : ℂ) n,
      ∫⁻ ω, ∫⁻ z, g z ∂occupationMeasure (fun u => regularize A u ω) ω ∂planarLaw y ≠ 0 := by
  rw [lintegral_revuz measurable_planarLaw hA.meas hg] at hpos
  by_contra h
  simp only [not_exists, not_not] at h
  refine hpos (le_antisymm ?_ zero_le)
  calc ∫⁻ y, ∫⁻ ω, ∫⁻ z, g z ∂occupationMeasure (fun u => regularize A u ω) ω ∂planarLaw y
      = ∫⁻ y in ⋃ n : ℕ, closedBall (0 : ℂ) n,
          ∫⁻ ω, ∫⁻ z, g z ∂occupationMeasure (fun u => regularize A u ω) ω ∂planarLaw y := by
        rw [iUnion_closedBall_nat, Measure.restrict_univ]
    _ ≤ ∑' n : ℕ, ∫⁻ y in closedBall (0 : ℂ) n,
          ∫⁻ ω, ∫⁻ z, g z ∂occupationMeasure (fun u => regularize A u ω) ω ∂planarLaw y :=
        lintegral_iUnion_le _ _
    _ = 0 := by simp only [h, tsum_zero]

/-- The harmonic series with a positive factor diverges in `ℝ≥0∞`. -/
theorem tsum_ofReal_div_nat_add_one_eq_top {c : ℝ} (hc : 0 < c) :
    ∑' k : ℕ, ENNReal.ofReal (c / ((k : ℝ) + 1)) = ∞ := by
  by_contra h
  have hs : Summable fun k : ℕ => ((Real.toNNReal (c / ((k : ℝ) + 1)) : ℝ≥0) : ℝ) :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.1 h
  have he : (fun k : ℕ => ((Real.toNNReal (c / ((k : ℝ) + 1)) : ℝ≥0) : ℝ)) =
      fun k : ℕ => c * (1 / ((k + 1 : ℕ) : ℝ)) := by
    funext k
    rw [Real.coe_toNNReal _ (by positivity)]
    push_cast
    ring
  rw [he, summable_mul_left_iff hc.ne'] at hs
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ)) 1).1 hs)

/-- **The expected clock integral of a function of positive Revuz mass is infinite** (expectation form of the
Harris recurrence of the time change; Revuz–Yor (1999), Chapter X, §3). For a positive continuous additive
functional `A` of planar Brownian motion and a measurable `g ≥ 0` with `∫ g dμ_A ≠ 0`, for every starting point
`x`, `E_x ∫_{(0, ∞)} g(B_s) dA_s = ∞`. -/
theorem lintegral_setLIntegral_Ioi_eq_top {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hpos : ∫⁻ y, g y ∂revuz planarLaw A ≠ 0) (x : ℂ) :
    ∫⁻ ω, ∫⁻ s in Ioi (0 : ℝ), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x = ∞ := by
  obtain ⟨n, hn⟩ := exists_setLIntegral_closedBall_ne_zero hA hg hpos
  set m := ∫⁻ y in closedBall (0 : ℂ) n,
    ∫⁻ ω, ∫⁻ z, g z ∂occupationMeasure (fun u => regularize A u ω) ω ∂planarLaw y with hm
  set c : ℝ := (2 * π)⁻¹ * Real.exp (-((n : ℝ) + ‖x‖) ^ 2) with hc_def
  have hc : 0 < c := by positivity
  have hcoe : ∀ k : ℕ, (((k : ℝ≥0) + 1 : ℝ≥0) : ℝ) = (k : ℝ) + 1 := fun k => by push_cast; rfl
  have hd : Pairwise (Function.onFun Disjoint fun k : ℕ =>
      Ioc ((((k : ℝ≥0) + 1 : ℝ≥0)) : ℝ) ((((k : ℝ≥0) + 1 : ℝ≥0)) + 1)) := by
    have hlt : ∀ i j : ℕ, i < j → Disjoint (Ioc ((((i : ℝ≥0) + 1 : ℝ≥0)) : ℝ) ((((i : ℝ≥0) + 1 : ℝ≥0)) + 1))
        (Ioc ((((j : ℝ≥0) + 1 : ℝ≥0)) : ℝ) ((((j : ℝ≥0) + 1 : ℝ≥0)) + 1)) := by
      intro i j hij
      apply Ioc_disjoint_Ioc_of_le
      rw [hcoe, hcoe]
      have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      linarith
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlt i j h
    · exact (hlt j i h).symm
  have hsub : (⋃ k : ℕ, Ioc ((((k : ℝ≥0) + 1 : ℝ≥0)) : ℝ) ((((k : ℝ≥0) + 1 : ℝ≥0)) + 1)) ⊆ Ioi 0 := by
    refine iUnion_subset fun k s hs => lt_trans ?_ hs.1
    rw [hcoe]
    positivity
  have hwin : ∀ k : ℕ, ENNReal.ofReal (c / ((k : ℝ) + 1)) * m ≤
      ∫⁻ ω, ∫⁻ s in Ioc ((((k : ℝ≥0) + 1 : ℝ≥0)) : ℝ) ((((k : ℝ≥0) + 1 : ℝ≥0)) + 1), g (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x := by
    intro k
    refine le_trans ?_ (ofReal_mul_setLIntegral_le_lintegral_setLIntegral_Ioc hA x
      (t := (k : ℝ≥0) + 1) (by positivity) n hg)
    gcongr ?_ * _
    apply ENNReal.ofReal_le_ofReal
    rw [hcoe]
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hexp : Real.exp (-((n : ℝ) + ‖x‖) ^ 2) ≤ Real.exp (-((n : ℝ) + ‖x‖) ^ 2 / ((k : ℝ) + 1)) := by
      rw [Real.exp_le_exp, neg_div]
      exact neg_le_neg (div_le_self (sq_nonneg _) hk)
    have heq : c / ((k : ℝ) + 1) = (2 * π * ((k : ℝ) + 1))⁻¹ * Real.exp (-((n : ℝ) + ‖x‖) ^ 2) := by
      rw [hc_def, mul_inv (2 * π) ((k : ℝ) + 1), div_eq_mul_inv]
      ring
    rw [heq]
    gcongr
  have hsum : ∑' k : ℕ, ENNReal.ofReal (c / ((k : ℝ) + 1)) * m = ∞ := by
    rw [ENNReal.tsum_mul_right, tsum_ofReal_div_nat_add_one_eq_top hc, ENNReal.top_mul hn]
  refine eq_top_iff.2 (hsum ▸ ?_)
  calc ∑' k : ℕ, ENNReal.ofReal (c / ((k : ℝ) + 1)) * m
      ≤ ∑' k : ℕ, ∫⁻ ω, ∫⁻ s in Ioc ((((k : ℝ≥0) + 1 : ℝ≥0)) : ℝ) ((((k : ℝ≥0) + 1 : ℝ≥0)) + 1),
          g (ω s.toNNReal) ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x :=
        ENNReal.tsum_le_tsum hwin
    _ = ∫⁻ ω, ∑' k : ℕ, ∫⁻ s in Ioc ((((k : ℝ≥0) + 1 : ℝ≥0)) : ℝ) ((((k : ℝ≥0) + 1 : ℝ≥0)) + 1),
          g (ω s.toNNReal) ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x :=
        (lintegral_tsum fun k => aemeasurable_setLIntegral_Ioc hA x _ hg).symm
    _ ≤ ∫⁻ ω, ∫⁻ s in Ioi (0 : ℝ), g (ω s.toNNReal)
          ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x := by
        refine lintegral_mono fun ω => ?_
        rw [← lintegral_iUnion (fun k => measurableSet_Ioc) hd]
        exact lintegral_mono_set hsub

end MatedCRT
