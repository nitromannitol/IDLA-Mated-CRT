import MatedCRT.FirstPass.Derived.LBMApproxDelayDistance

/-!
# The level-`k` estimate for approximate Liouville Brownian paths

Let `A_k = lqgApproxClockPlus γ hε k` be the approximating LQG clock with drift at the dyadic scale
`2^{-k}`, `Φ_k = lbmContinuousPath A_k` the time-changed path map, and for `δ ≥ 0` write
`X̃_k(b) = Φ_k(θ_δ b)` for the approximate path of the path restarted at time `δ`, and
`c_k(b) = A_k(b, δ)`. Let `G` be bounded by `1` and `L`-Lipschitz for the local uniform distance
`dUnif` on paths, and let `ψ` dominate the delay modulus at level `a`:
`dUnif(T_s y, y) ≤ ψ(y)` for `s ≤ a`, where `T_s` is the delay by `s`.

Main statement:

* `abs_integral_sub_integral_lbmContinuousPath_lqgApproxClockPlus_le` (the level-`k` estimate):
  for all starts `z, z₀`,
  `|E^z G(Φ_k b) - E^{z₀} G(Φ_k b)| ≤ m(z) + m(z₀) + 2 P^z(c_k > a) + 2 P^{z₀}(c_k > a)
     + 2 E^{z₀} min(2, L ψ(X̃_k)) + 4 TV(p_δ(z, ·), p_δ(z₀, ·))`,
  where `m(w) = E^w min(2, L dUnif(Φ_k b, T_{c_k} X̃_k))` and `p_δ` is the planar heat kernel.

The proof compares `Φ_k b` with `X̃_k` pathwise at each start (the clock additivity of the
approximants), and compares the laws of `X̃_k` under the two starts through the simple Markov
property at time `δ`, which bounds their total variation distance by that of the heat kernels.

Auxiliary statements: the bounded total variation duality in Bochner-integral form
(`integral_le_integral_add_mul_tvDist`, `abs_integral_sub_integral_le_two_mul_tvDist`), and the
continuity of `dUnif` and of the path delay `(c, y) ↦ T_c y` in the compact-open topology.
-/

open MeasureTheory ProbabilityTheory Set MarkovProcess Filter Topology
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

section TotalVariation

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν]

/-- **Bounded total variation duality.** For a measurable `f` with values in `[0, M]`,
`∫ f dμ ≤ ∫ f dν + M · TV(μ, ν)`. -/
theorem integral_le_integral_add_mul_tvDist {f : α → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0 < M)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ M) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν + M * (QuantumZipper.TV.tvDist μ ν).toReal := by
  set g : α → ℝ := fun x => f x / M with hg
  have hgm : Measurable g := hf.div_const M
  have hg0 : ∀ x, 0 ≤ g x := fun x => div_nonneg (h0 x) hM.le
  have hg1 : ∀ x, g x ≤ 1 := fun x => (div_le_one hM).2 (h1 x)
  have key := QuantumZipper.TV.ofReal_lintegral_le_add_tvDist (μ := μ) (ν := ν) hgm hg0 hg1
  have hfin : ∀ ρ : Measure α, IsProbabilityMeasure ρ → ∫⁻ x, ENNReal.ofReal (g x) ∂ρ ≠ ∞ :=
    fun ρ _ => ne_top_of_le_ne_top (by simp : ∫⁻ _ : α, (1 : ℝ≥0∞) ∂ρ ≠ ∞)
      (lintegral_mono fun x => ENNReal.ofReal_le_one.2 (hg1 x))
  have hTV : QuantumZipper.TV.tvDist μ ν ≠ ∞ := QuantumZipper.TV.tvDist_ne_top
  have hreal : ∫ x, g x ∂μ ≤ ∫ x, g x ∂ν + (QuantumZipper.TV.tvDist μ ν).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgm.aestronglyMeasurable,
      ← ENNReal.toReal_add (hfin ν inferInstance) hTV]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin ν inferInstance, hTV⟩) key
  have hμ : ∫ x, g x ∂μ = (∫ x, f x ∂μ) / M := integral_div M _
  have hν : ∫ x, g x ∂ν = (∫ x, f x ∂ν) / M := integral_div M _
  rw [hμ, hν, div_le_iff₀ hM, add_mul, div_mul_cancel₀ _ hM.ne'] at hreal
  linarith

/-- **Bounded total variation duality, two-sided.** For a measurable `f` with `|f| ≤ 1`,
`|∫ f dμ - ∫ f dν| ≤ 2 TV(μ, ν)`. -/
theorem abs_integral_sub_integral_le_two_mul_tvDist {f : α → ℝ} (hf : Measurable f)
    (h1 : ∀ x, |f x| ≤ 1) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ 2 * (QuantumZipper.TV.tvDist μ ν).toReal := by
  have hint : ∀ ρ : Measure α, IsProbabilityMeasure ρ → Integrable f ρ := fun ρ _ =>
    Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact h1 x)
  have hshift : ∀ ρ : Measure α, IsProbabilityMeasure ρ →
      ∫ x, (f x + 1) ∂ρ = ∫ x, f x ∂ρ + 1 := fun ρ _ => by
    rw [integral_add (hint ρ inferInstance) (integrable_const _)]
    simp
  have hm : Measurable fun x => f x + 1 := hf.add_const 1
  have h0 : ∀ x, 0 ≤ f x + 1 := fun x => by linarith [(abs_le.1 (h1 x)).1]
  have h2 : ∀ x, f x + 1 ≤ 2 := fun x => by linarith [(abs_le.1 (h1 x)).2]
  have hμν := integral_le_integral_add_mul_tvDist (μ := μ) (ν := ν) hm two_pos h0 h2
  have hνμ := integral_le_integral_add_mul_tvDist (μ := ν) (ν := μ) hm two_pos h0 h2
  rw [hshift μ inferInstance, hshift ν inferInstance] at hμν hνμ
  rw [QuantumZipper.TV.tvDist_comm] at hνμ
  rw [abs_sub_le_iff]
  constructor <;> linarith

end TotalVariation

section PathSpace

/-- The local uniform distance `dUnif` is continuous on pairs of paths (compact-open topology). -/
theorem continuous_dUnif_pair :
    Continuous fun p : ContinuousPath ℂ × ContinuousPath ℂ => LatticeProb.dUnif p.1 p.2 := by
  let _ := LatticeProb.dUnifMetricSpace (E := ℂ)
  exact continuous_dist

/-- The path delay `(c, y) ↦ T_c y` is jointly continuous (compact-open topology). -/
theorem continuous_continuousPathDelay :
    Continuous fun p : ℝ≥0 × ContinuousPath ℂ => continuousPathDelay p.1 p.2 :=
  ContinuousMap.continuous_comp'.comp
    (((ContinuousMap.curry ⟨fun q : ℝ≥0 × ℝ≥0 => q.2 - q.1,
      continuous_snd.sub continuous_fst⟩).continuous.comp continuous_fst).prodMk continuous_snd)

/-- For `u, v ≥ 0`, `min 2 (u + v) ≤ min 2 u + min 2 v`. -/
theorem min_two_add_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    min 2 (u + v) ≤ min 2 u + min 2 v := by
  simp only [min_def]
  split_ifs <;> linarith

end PathSpace

section LevelEstimate

variable {γ : ℝ} {hε : ℝ → ℂ → ℝ} {n : ℕ}

/-- **Pathwise comparison with the restarted approximate path.** For `G` bounded by `1` and
`L`-Lipschitz for `dUnif`, and `ψ` dominating the delay modulus up to `a`,
`|G(Φ_n b) - G(Φ_n(θ_δ b))| ≤ min(2, L dUnif(Φ_n b, T_{c} Φ_n(θ_δ b))) + 2·1{c > a}
  + min(2, L ψ(Φ_n(θ_δ b)))` with `c = A_n(b, δ)`. -/
theorem abs_sub_lbmContinuousPath_shift_le {G : ContinuousPath ℂ → ℝ}
    (hG1 : ∀ x, |G x| ≤ 1) {L : ℝ} (hL : 0 ≤ L)
    (hGL : ∀ x y, |G x - G y| ≤ L * LatticeProb.dUnif x y) {ψ : ContinuousPath ℂ → ℝ}
    {δ a : ℝ≥0} (hψ : ∀ y (s : ℝ≥0), s ≤ a → LatticeProb.dUnif (continuousPathDelay s y) y ≤ ψ y)
    (b : ContinuousPath ℂ) :
    |G (lbmContinuousPath (lqgApproxClockPlus γ hε n) b) -
        G (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))| ≤
      min 2 (L * LatticeProb.dUnif (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
        (continuousPathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal
          (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b)))) +
      {b' : ContinuousPath ℂ | (a : ℝ) < lqgApproxClockPlus γ hε n b' δ}.indicator
        (fun _ => (2 : ℝ)) b +
      min 2 (L * ψ (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))) := by
  set X := lbmContinuousPath (lqgApproxClockPlus γ hε n) b
  set Y := lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b)
  set c := (lqgApproxClockPlus γ hε n b δ).toNNReal
  have hψ0 : 0 ≤ ψ Y := (LatticeProb.dUnif_nonneg _ _).trans (hψ Y 0 zero_le)
  have hm1 : 0 ≤ min 2 (L * LatticeProb.dUnif X (continuousPathDelay c Y)) :=
    le_min zero_le_two (mul_nonneg hL (LatticeProb.dUnif_nonneg _ _))
  have hm3 : 0 ≤ min 2 (L * ψ Y) := le_min zero_le_two (mul_nonneg hL hψ0)
  have hG2 : |G X - G Y| ≤ 2 := (abs_sub _ _).trans (by linarith [hG1 X, hG1 Y])
  by_cases hb : (a : ℝ) < lqgApproxClockPlus γ hε n b δ
  · rw [indicator_of_mem (show b ∈ _ from hb)]
    linarith
  · rw [indicator_of_notMem (show b ∉ _ from hb)]
    have hca : c ≤ a := Real.toNNReal_le_iff_le_coe.2 (not_lt.1 hb)
    have htri : LatticeProb.dUnif X Y ≤
        LatticeProb.dUnif X (continuousPathDelay c Y) + ψ Y := by
      have h1 := LatticeProb.dUnif_triangle X (continuousPathDelay c Y) Y
      have h2 := hψ Y c hca
      linarith
    have hmin : |G X - G Y| ≤ min 2 (L * LatticeProb.dUnif X Y) :=
      le_min hG2 (hGL X Y)
    have hsplit := min_two_add_le (mul_nonneg hL (LatticeProb.dUnif_nonneg X
      (continuousPathDelay c Y))) (mul_nonneg hL hψ0)
    have hmono : min 2 (L * LatticeProb.dUnif X Y) ≤
        min 2 (L * LatticeProb.dUnif X (continuousPathDelay c Y) + L * ψ Y) :=
      min_le_min_left _ (by rw [← mul_add]; exact mul_le_mul_of_nonneg_left htri hL)
    linarith

/-- **The level-`k` estimate** (approximate Liouville Brownian paths, two starts). Let `G` be
measurable, bounded by `1` and `L`-Lipschitz for `dUnif`, and let `ψ` be measurable with
`dUnif(T_s y, y) ≤ ψ(y)` for `s ≤ a`. For circle averages continuous at the scale `2^{-n}`, for
all starts `z, z₀` and every `δ`,
`|E^z G(Φ_n b) - E^{z₀} G(Φ_n b)| ≤ m(z) + m(z₀) + 2 P^z(A_n(b, δ) > a) + 2 P^{z₀}(A_n(b, δ) > a)
  + 2 E^{z₀} min(2, L ψ(Φ_n(θ_δ b))) + 4 TV(p_δ(z, ·), p_δ(z₀, ·))`,
with `m(w) = E^w min(2, L dUnif(Φ_n b, T_{A_n(b, δ)} Φ_n(θ_δ b)))`. -/
theorem abs_integral_sub_integral_lbmContinuousPath_lqgApproxClockPlus_le
    (hcont : Continuous (hε (dyadicScale n))) {G : ContinuousPath ℂ → ℝ} (hGm : Measurable G)
    (hG1 : ∀ x, |G x| ≤ 1) {L : ℝ} (hL : 0 ≤ L)
    (hGL : ∀ x y, |G x - G y| ≤ L * LatticeProb.dUnif x y) {ψ : ContinuousPath ℂ → ℝ}
    (hψm : Measurable ψ) {δ a : ℝ≥0}
    (hψ : ∀ y (s : ℝ≥0), s ≤ a → LatticeProb.dUnif (continuousPathDelay s y) y ≤ ψ y)
    (z z0 : ℂ) :
    |∫ b, G (lbmContinuousPath (lqgApproxClockPlus γ hε n) b) ∂planarBrownianMotion z -
        ∫ b, G (lbmContinuousPath (lqgApproxClockPlus γ hε n) b) ∂planarBrownianMotion z0| ≤
      ∫ b, min 2 (L * LatticeProb.dUnif (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
          (continuousPathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal
            (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))))
          ∂planarBrownianMotion z +
        ∫ b, min 2 (L * LatticeProb.dUnif (lbmContinuousPath (lqgApproxClockPlus γ hε n) b)
          (continuousPathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal
            (lbmContinuousPath (lqgApproxClockPlus γ hε n) (ContinuousPath.shift δ b))))
          ∂planarBrownianMotion z0 +
        2 * (planarBrownianMotion z
          {b | (a : ℝ) < lqgApproxClockPlus γ hε n b δ}).toReal +
        2 * (planarBrownianMotion z0
          {b | (a : ℝ) < lqgApproxClockPlus γ hε n b δ}).toReal +
        2 * ∫ b, min 2 (L * ψ (lbmContinuousPath (lqgApproxClockPlus γ hε n)
          (ContinuousPath.shift δ b))) ∂planarBrownianMotion z0 +
        4 * (QuantumZipper.TV.tvDist (planarHeatSemigroup δ z)
          (planarHeatSemigroup δ z0)).toReal := by
  set Φ := lbmContinuousPath (lqgApproxClockPlus γ hε n) with hΦdef
  have hΦ : Continuous Φ := continuous_lbmContinuousPath_lqgApproxClockPlus hcont
  have hsh : Continuous (ContinuousPath.shift δ : ContinuousPath ℂ → ContinuousPath ℂ) :=
    ContinuousPath.continuous_shift_fixed δ
  have hcl : Continuous fun b : ContinuousPath ℂ => lqgApproxClockPlus γ hε n b δ :=
    continuous_lqgApproxClockPlus_apply hcont δ
  set E : Set (ContinuousPath ℂ) := {b | (a : ℝ) < lqgApproxClockPlus γ hε n b δ} with hEdef
  have hE : MeasurableSet E := measurableSet_lt measurable_const hcl.measurable
  -- the three integrands of the pathwise bound
  set f1 : ContinuousPath ℂ → ℝ := fun b => min 2 (L * LatticeProb.dUnif (Φ b)
    (continuousPathDelay (lqgApproxClockPlus γ hε n b δ).toNNReal (Φ (ContinuousPath.shift δ b))))
    with hf1
  set f3 : ContinuousPath ℂ → ℝ := fun b => min 2 (L * ψ (Φ (ContinuousPath.shift δ b)))
    with hf3
  have hf1m : Measurable f1 := by
    refine (continuous_const.min (continuous_const.mul ?_)).measurable
    exact continuous_dUnif_pair.comp (hΦ.prodMk (continuous_continuousPathDelay.comp
      ((continuous_real_toNNReal.comp hcl).prodMk (hΦ.comp hsh))))
  have hψmeas : Measurable fun y => min 2 (L * ψ y) :=
    measurable_const.min (measurable_const.mul hψm)
  have hf3m : Measurable f3 := hψmeas.comp (hΦ.comp hsh).measurable
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y =>
    (LatticeProb.dUnif_nonneg _ _).trans (hψ y 0 zero_le)
  have hf1b : ∀ b, |f1 b| ≤ 2 := fun b => by
    rw [abs_of_nonneg (le_min zero_le_two (mul_nonneg hL (LatticeProb.dUnif_nonneg _ _)))]
    exact min_le_left _ _
  have hf3b : ∀ b, |f3 b| ≤ 2 := fun b => by
    rw [abs_of_nonneg (le_min zero_le_two (mul_nonneg hL (hψ0 _)))]
    exact min_le_left _ _
  have hint : ∀ (w : ℂ) {f : ContinuousPath ℂ → ℝ}, Measurable f → (∀ b, |f b| ≤ 2) →
      Integrable f (planarBrownianMotion w) := fun w f hf hb =>
    Integrable.of_bound hf.aestronglyMeasurable 2 (ae_of_all _ fun b => by
      rw [Real.norm_eq_abs]; exact hb b)
  have hGX : Measurable fun b => G (Φ b) := hGm.comp hΦ.measurable
  have hGY : Measurable fun b => G (Φ (ContinuousPath.shift δ b)) :=
    hGm.comp (hΦ.comp hsh).measurable
  have hG2 : ∀ x, |G x| ≤ 2 := fun x => (hG1 x).trans one_le_two
  have hind : Measurable (E.indicator fun _ => (2 : ℝ)) := measurable_const.indicator hE
  have hindb : ∀ b, |E.indicator (fun _ => (2 : ℝ)) b| ≤ 2 := fun b => by
    by_cases hb : b ∈ E
    · rw [indicator_of_mem hb]; norm_num
    · rw [indicator_of_notMem hb]; norm_num
  -- step 1: pathwise comparison at a fixed start
  have step1 : ∀ w : ℂ, |∫ b, G (Φ b) ∂planarBrownianMotion w -
      ∫ b, G (Φ (ContinuousPath.shift δ b)) ∂planarBrownianMotion w| ≤
      ∫ b, f1 b ∂planarBrownianMotion w + 2 * (planarBrownianMotion w E).toReal +
        ∫ b, f3 b ∂planarBrownianMotion w := fun w => by
    rw [← integral_sub (hint w hGX fun b => hG2 _) (hint w hGY fun b => hG2 _)]
    refine (abs_integral_le_integral_abs).trans ?_
    have hsum : ∫ b, (f1 b + E.indicator (fun _ => (2 : ℝ)) b + f3 b) ∂planarBrownianMotion w =
        ∫ b, f1 b ∂planarBrownianMotion w + 2 * (planarBrownianMotion w E).toReal +
          ∫ b, f3 b ∂planarBrownianMotion w := by
      rw [integral_add (f := fun b => f1 b + E.indicator (fun _ => (2 : ℝ)) b)
        ((hint w hf1m hf1b).add (hint w hind hindb)) (hint w hf3m hf3b),
        integral_add (hint w hf1m hf1b) (hint w hind hindb), integral_indicator_const _ hE]
      simp only [measureReal_def, smul_eq_mul]
      ring
    rw [← hsum]
    refine integral_mono_of_nonneg (ae_of_all _ fun b => abs_nonneg _)
      (((hint w hf1m hf1b).add (hint w hind hindb)).add (hint w hf3m hf3b))
      (ae_of_all _ fun b => ?_)
    exact abs_sub_lbmContinuousPath_shift_le hG1 hL hGL hψ b
  -- the laws of the restarted path under the two starts
  have hmap : ∀ (w : ℂ) {f : ContinuousPath ℂ → ℝ}, Measurable f →
      ∫ b, f (ContinuousPath.shift δ b) ∂planarBrownianMotion w =
        ∫ y, f y ∂((planarBrownianMotion w).map (ContinuousPath.shift δ)) := fun w f hf =>
    (integral_map (ContinuousPath.measurable_shift_fixed δ).aemeasurable
      hf.aestronglyMeasurable).symm
  have hprob : ∀ w : ℂ,
      IsProbabilityMeasure ((planarBrownianMotion w).map (ContinuousPath.shift δ)) := fun w =>
    (Measure.isProbabilityMeasure_map_iff
      (ContinuousPath.measurable_shift_fixed δ).aemeasurable).2 inferInstance
  have hheat : ∀ w : ℂ, IsProbabilityMeasure (planarHeatSemigroup δ w) := fun w =>
    ⟨isConservative_planarHeatSemigroup δ w⟩
  have hTV : (QuantumZipper.TV.tvDist ((planarBrownianMotion z).map (ContinuousPath.shift δ))
        ((planarBrownianMotion z0).map (ContinuousPath.shift δ))).toReal ≤
      (QuantumZipper.TV.tvDist (planarHeatSemigroup δ z) (planarHeatSemigroup δ z0)).toReal :=
    ENNReal.toReal_mono QuantumZipper.TV.tvDist_ne_top
      (tvDist_planarBrownianMotion_map_shift_le z z0 δ)
  -- step 2: the restarted paths under the two starts
  have step2 : |∫ b, G (Φ (ContinuousPath.shift δ b)) ∂planarBrownianMotion z -
      ∫ b, G (Φ (ContinuousPath.shift δ b)) ∂planarBrownianMotion z0| ≤
      2 * (QuantumZipper.TV.tvDist (planarHeatSemigroup δ z) (planarHeatSemigroup δ z0)).toReal := by
    have := hprob z
    have := hprob z0
    have e1 : ∫ b, G (Φ (ContinuousPath.shift δ b)) ∂planarBrownianMotion z =
        ∫ y, G (Φ y) ∂((planarBrownianMotion z).map (ContinuousPath.shift δ)) :=
      hmap z (hGm.comp hΦ.measurable)
    have e2 : ∫ b, G (Φ (ContinuousPath.shift δ b)) ∂planarBrownianMotion z0 =
        ∫ y, G (Φ y) ∂((planarBrownianMotion z0).map (ContinuousPath.shift δ)) :=
      hmap z0 (hGm.comp hΦ.measurable)
    rw [e1, e2]
    exact (abs_integral_sub_integral_le_two_mul_tvDist (hGm.comp hΦ.measurable)
      fun y => hG1 _).trans (by linarith)
  -- step 3: the delay-modulus term under the two starts
  have step3 : ∫ b, f3 b ∂planarBrownianMotion z ≤ ∫ b, f3 b ∂planarBrownianMotion z0 +
      2 * (QuantumZipper.TV.tvDist (planarHeatSemigroup δ z) (planarHeatSemigroup δ z0)).toReal := by
    have := hprob z
    have := hprob z0
    have hcomp : Measurable fun y => min 2 (L * ψ (Φ y)) := hψmeas.comp hΦ.measurable
    have e1 : ∫ b, f3 b ∂planarBrownianMotion z =
        ∫ y, min 2 (L * ψ (Φ y)) ∂((planarBrownianMotion z).map (ContinuousPath.shift δ)) :=
      hmap z hcomp
    have e2 : ∫ b, f3 b ∂planarBrownianMotion z0 =
        ∫ y, min 2 (L * ψ (Φ y)) ∂((planarBrownianMotion z0).map (ContinuousPath.shift δ)) :=
      hmap z0 hcomp
    rw [e1, e2]
    exact (integral_le_integral_add_mul_tvDist hcomp two_pos
      (fun y => le_min zero_le_two (mul_nonneg hL (hψ0 _))) fun y => min_le_left _ _).trans
      (by linarith)
  have h1z := step1 z
  have h1z0 := step1 z0
  have htri := abs_sub_le (∫ b, G (Φ b) ∂planarBrownianMotion z)
    (∫ b, G (Φ (ContinuousPath.shift δ b)) ∂planarBrownianMotion z)
    (∫ b, G (Φ b) ∂planarBrownianMotion z0)
  have htri' := abs_sub_le (∫ b, G (Φ (ContinuousPath.shift δ b)) ∂planarBrownianMotion z)
    (∫ b, G (Φ (ContinuousPath.shift δ b)) ∂planarBrownianMotion z0)
    (∫ b, G (Φ b) ∂planarBrownianMotion z0)
  rw [abs_sub_comm (∫ b, G (Φ (ContinuousPath.shift δ b)) ∂planarBrownianMotion z0)] at htri'
  linarith

end LevelEstimate

end MatedCRT.FirstPass.Derived
