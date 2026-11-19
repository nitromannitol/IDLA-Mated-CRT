import MatedCRT.FirstPass.Derived.RevuzWeightedRiemannLimit

/-!
# The expected window integral is determined by the Revuz measure

Let `A`, `A'` be positive continuous additive functionals of planar Brownian motion with the same Revuz measure `μ`,
and let `h ≥ 0` with `∫ h dμ < ∞`. We prove that `E_x[∫_{(0,r]} h(B_s) dĀ_s] = E_x[∫_{(0,r]} h(B_s) dĀ'_s]` for
Lebesgue-almost every starting point `x`.

The densities `Φ(x) = E_x[∫_{(0,r]} h dĀ]` and `Φ'` have finite Lebesgue integral `r ∫ h dμ`, so they define finite
measures `Φ dx` and `Φ' dx`. By the Riemann-sum limit these measures give the same integral to every bounded
Lipschitz `g ≥ 0`, in particular to the truncations `g_n = 1 - (n + 1) d(·, F)` of the indicator of a closed set
`F`. Letting `n → ∞` they agree on closed sets, hence (closed sets are a π-system generating the Borel σ-algebra)
they are equal, and so `Φ = Φ'` almost everywhere (Fukushima–Oshima–Takeda (2011), proof of Theorem 5.1.4;
Revuz–Yor (1999), Chapter X, Theorem 2.6).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- Under the path law started at `x`, the start weight `g(B_0)` is the constant `g(x)`. -/
theorem lintegral_eval_zero_mul_eq (g : ℂ → ℝ≥0∞) {F : ContinuousPath ℂ → ℝ≥0∞} (hF : Measurable F) (x : ℂ) :
    ∫⁻ ω, g (ω 0) * F ω ∂planarLaw x = g x * ∫⁻ ω, F ω ∂planarLaw x := by
  rw [← lintegral_const_mul _ hF]
  exact lintegral_congr_ae ((ae_planarLaw_eval_zero x).mono fun ω hω => by simp only [hω])

/-- The Lipschitz truncation `x ↦ 1 - (n + 1) d(x, F)` of the indicator of `F`. -/
noncomputable def closedTruncation (F : Set ℂ) (n : ℕ) (x : ℂ) : ℝ≥0∞ :=
  1 - ((n : ℝ≥0∞) + 1) * Metric.infEDist x F

theorem measurable_closedTruncation (F : Set ℂ) (n : ℕ) : Measurable (closedTruncation F n) := by
  unfold closedTruncation
  exact measurable_const.sub (measurable_const.mul Metric.continuous_infEDist.measurable)

theorem closedTruncation_le_one (F : Set ℂ) (n : ℕ) (x : ℂ) : closedTruncation F n x ≤ 1 :=
  tsub_le_self

/-- The truncation is `(n + 1)`-Lipschitz and bounded by `1`, in the form used by the Riemann-sum limit. -/
theorem closedTruncation_le_add_min (F : Set ℂ) (n : ℕ) (x y : ℂ) :
    closedTruncation F n x ≤ closedTruncation F n y + min (((n : ℝ≥0∞) + 1) * edist x y) 1 := by
  have hb : Metric.infEDist y F ≤ Metric.infEDist x F + edist x y := by
    rw [edist_comm]; exact Metric.infEDist_le_infEDist_add_edist
  unfold closedTruncation
  rw [← min_add_add_left]
  refine le_min ?_ (tsub_le_self.trans le_add_self)
  generalize ((n : ℝ≥0∞) + 1) = K
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) ≤ (1 - K * Metric.infEDist y F) + K * Metric.infEDist y F := le_tsub_add
    _ ≤ (1 - K * Metric.infEDist y F) + (K * Metric.infEDist x F + K * edist x y) := by
        rw [← mul_add]; gcongr
    _ = (1 - K * Metric.infEDist y F) + K * edist x y + K * Metric.infEDist x F := by ring

/-- For a closed set `F`, the truncations converge pointwise to the indicator of `F`. -/
theorem tendsto_closedTruncation {F : Set ℂ} (hF : IsClosed F) (x : ℂ) :
    Tendsto (fun n => closedTruncation F n x) atTop (𝓝 (F.indicator 1 x)) := by
  by_cases hx : x ∈ F
  · simp only [closedTruncation, Metric.infEDist_zero_of_mem hx, mul_zero, tsub_zero,
      indicator_of_mem hx, Pi.one_apply]
    exact tendsto_const_nhds
  · have ha : Metric.infEDist x F ≠ 0 := fun h0 =>
      hx (hF.closure_eq ▸ Metric.mem_closure_iff_infEDist_zero.2 h0)
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_mul_gt ha ENNReal.one_ne_top
    rw [indicator_of_notMem hx]
    refine tendsto_atTop_of_eventually_const (i₀ := m) fun n hn => ?_
    show 1 - ((n : ℝ≥0∞) + 1) * Metric.infEDist x F = 0
    refine tsub_eq_zero_of_le (hm.le.trans ?_)
    gcongr
    exact (Nat.cast_le.2 hn).trans le_self_add

/-- For a finite measure, the integrals of the truncations converge to the measure of the closed set. -/
theorem tendsto_lintegral_closedTruncation (ν : Measure ℂ) [IsFiniteMeasure ν] {F : Set ℂ} (hF : IsClosed F) :
    Tendsto (fun n => ∫⁻ x, closedTruncation F n x ∂ν) atTop (𝓝 (ν F)) := by
  rw [← lintegral_indicator_one (μ := ν) hF.measurableSet]
  exact tendsto_lintegral_of_dominated_convergence (fun _ => 1) (measurable_closedTruncation F)
    (fun n => ae_of_all _ (closedTruncation_le_one F n)) (by simp [measure_ne_top])
    (ae_of_all _ (tendsto_closedTruncation hF))

/-- Finite measures on `ℂ` that agree on the truncations of the indicators of closed sets are equal. -/
theorem measure_eq_of_lintegral_closedTruncation_eq {ν ν' : Measure ℂ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h : ∀ (F : Set ℂ), IsClosed F → ∀ n, ∫⁻ x, closedTruncation F n x ∂ν = ∫⁻ x, closedTruncation F n x ∂ν') :
    ν = ν' := by
  have hcl : ∀ F : Set ℂ, IsClosed F → ν F = ν' F := fun F hF =>
    tendsto_nhds_unique (tendsto_lintegral_closedTruncation ν hF)
      (by simpa only [h F hF] using tendsto_lintegral_closedTruncation ν' hF)
  refine ext_of_generate_finite {s : Set ℂ | IsClosed s} ?_ isPiSystem_isClosed hcl (hcl univ isClosed_univ)
  rw [← borel_eq_generateFrom_isClosed]
  exact BorelSpace.measurable_eq

/-- **The expected window integral is determined by the Revuz measure.** If two positive continuous additive
functionals `A`, `A'` of planar Brownian motion have the same Revuz measure `μ` and `∫ h dμ < ∞`, then
`E_x[∫_{(0,r]} h dĀ] = E_x[∫_{(0,r]} h dĀ']` for Lebesgue-almost every `x`. -/
theorem ae_lintegral_clockWindowIntegral_eq_of_revuz_eq {A A' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hA' : IsPCAF planarLaw A') (hμ : revuz planarLaw A = revuz planarLaw A')
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) (hfin : ∫⁻ y, h y ∂revuz planarLaw A ≠ ∞) (r : ℝ≥0) :
    ∀ᵐ x : ℂ, ∫⁻ ω, clockWindowIntegral A h r ω ∂planarLaw x =
      ∫⁻ ω, clockWindowIntegral A' h r ω ∂planarLaw x := by
  have hfin' : ∫⁻ y, h y ∂revuz planarLaw A' ≠ ∞ := hμ ▸ hfin
  have hΦfin : ∫⁻ x, ∫⁻ ω, clockWindowIntegral A h r ω ∂planarLaw x ≠ ∞ := by
    rw [lintegral_clockWindowIntegral_eq hA hh r.coe_nonneg]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hΦfin' : ∫⁻ x, ∫⁻ ω, clockWindowIntegral A' h r ω ∂planarLaw x ≠ ∞ := by
    rw [lintegral_clockWindowIntegral_eq hA' hh r.coe_nonneg]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin'
  have := isFiniteMeasure_withDensity hΦfin
  have := isFiniteMeasure_withDensity hΦfin'
  have hint : ∀ {B : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}, IsPCAF planarLaw B → ∀ (F : Set ℂ) (n : ℕ),
      ∫⁻ x, closedTruncation F n x ∂(volume : Measure ℂ).withDensity
          (fun x => ∫⁻ ω, clockWindowIntegral B h r ω ∂planarLaw x) =
        ∫⁻ x, ∫⁻ ω, closedTruncation F n (ω 0) * clockWindowIntegral B h r ω ∂planarLaw x := by
    intro B hB F n
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_lintegral_clockWindowIntegral hB.meas hh r)
      (measurable_closedTruncation F n)]
    refine lintegral_congr fun x => ?_
    rw [lintegral_eval_zero_mul_eq (closedTruncation F n) (measurable_clockWindowIntegral hB.meas hh r),
      Pi.mul_apply]
    exact mul_comm _ _
  have hν : (volume : Measure ℂ).withDensity (fun x => ∫⁻ ω, clockWindowIntegral A h r ω ∂planarLaw x) =
      (volume : Measure ℂ).withDensity (fun x => ∫⁻ ω, clockWindowIntegral A' h r ω ∂planarLaw x) := by
    refine measure_eq_of_lintegral_closedTruncation_eq fun F _ n => ?_
    rw [hint hA, hint hA']
    exact lintegral_eval_zero_mul_clockWindowIntegral_eq_of_revuz_eq hA hA' hμ (measurable_closedTruncation F n)
      hh hfin (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩)
      ENNReal.one_ne_top (closedTruncation_le_add_min F n) r
  exact (withDensity_eq_iff (measurable_lintegral_clockWindowIntegral hA.meas hh r).aemeasurable
    (measurable_lintegral_clockWindowIntegral hA'.meas hh r).aemeasurable hΦfin).1 hν

end MatedCRT
