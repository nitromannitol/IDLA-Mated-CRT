import MatedCRT.FirstPass.Derived.ReversibilityPairingDiscrete
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.CutoffPathUniform

/-!
# Bounded Lipschitz path functionals are uniformly continuous for the metric `dUnif`

The path functionals of the random-walk-to-Liouville-Brownian-motion theorem (Berestycki–Gwynne (2020), Thm. 1.2)
are bounded and Lipschitz for the local uniform *series* distance `localUniformDist`
(`IsBoundedLipschitzPathFunctional`), whereas Lévy–Prokhorov distances of laws of continuous paths are taken for
the *integral* metric `dUnif` of Lattice-Probability.  This file transfers the functional from one metric to the
other:

* `exists_dUnif_lt_abs_sub_le_of_isBoundedLipschitzPathFunctional`: for every `η > 0` there is `a > 0` such that
  `dUnif f g < a` implies `|F f - F g| ≤ η` (a modulus of continuity for `dUnif`).  The proof truncates the
  series: `dUnif f g < a` makes `f, g` uniformly close on `[0, K + 1]`
  (`LatticeProb.pathSupDist_lt_of_dUnif_lt`), and then `localUniformDist f g ≤ δ + 2 ^ (-(K + 1))`
  (`localUniformDist_le_add_of_forall_le`).
* `continuous_blPathFunctional`, `blPathFunctionalBCF`: `F` is a bounded continuous function on
  `ContinuousPath ℂ` (compact-open topology, which is the topology of `dUnif`).
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal BoundedContinuousFunction

/-- **A bounded Lipschitz path functional has a modulus of continuity for `dUnif`.** If `F` is bounded by `1` and
Lipschitz for `localUniformDist`, then for every `η > 0` there is `a > 0` with
`|F f - F g| ≤ η` whenever `dUnif f g < a`, for continuous paths `f, g : [0, ∞) → ℂ`. -/
theorem exists_dUnif_lt_abs_sub_le_of_isBoundedLipschitzPathFunctional
    {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F) {η : ℝ} (hη : 0 < η) :
    ∃ a : ℝ, 0 < a ∧ ∀ f g : ContinuousPath ℂ, dUnif f g < a → |F f - F g| ≤ η := by
  obtain ⟨-, L, hL⟩ := hF
  set M : ℝ := max L 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hLM : ∀ f g : ℝ≥0 → ℂ, |F f - F g| ≤ M * localUniformDist f g := fun f g =>
    (hL f g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (localUniformDist_nonneg f g))
  set δ : ℝ := η / (2 * (M + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hMδ : M * δ ≤ η / 2 := by
    have h1 : M * δ = η / 2 * (M / (M + 1)) := by
      rw [hδ]; field_simp
    rw [h1]
    have h2 : M / (M + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    nlinarith [half_pos hη]
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hδ0 (show (2 : ℝ)⁻¹ < 1 by norm_num)
  have hKδ : (2 : ℝ)⁻¹ ^ (K + 1) ≤ δ :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ K)).trans hK.le
  set T0 : ℝ≥0 := ((K + 1 : ℕ) : ℝ≥0) with hT0
  refine ⟨min (Real.exp (-((T0 : ℝ) + 1))) δ, lt_min (Real.exp_pos _) hδ0, fun f g hfg => ?_⟩
  have hsup : pathSupDist T0 f g < δ := pathSupDist_lt_of_dUnif_lt T0 hfg
  have hclose : ∀ t : ℝ≥0, t ≤ ((K + 1 : ℕ) : ℝ≥0) → ‖f t - g t‖ ≤ δ := fun t ht => by
    have := dist_le_pathSupDist f g ht
    rw [dist_eq_norm] at this
    exact this.trans hsup.le
  have hloc := localUniformDist_le_add_of_forall_le (⇑f) (⇑g) K hδ0.le hclose
  calc |F f - F g| ≤ M * localUniformDist f g := hLM f g
    _ ≤ M * (δ + (2 : ℝ)⁻¹ ^ (K + 1)) := mul_le_mul_of_nonneg_left hloc hM0
    _ ≤ M * (δ + δ) := mul_le_mul_of_nonneg_left (by linarith) hM0
    _ = 2 * (M * δ) := by ring
    _ ≤ η := by linarith

/-- A bounded Lipschitz path functional is continuous on `ContinuousPath ℂ` (the topology of `dUnif` is the
compact-open topology). -/
theorem continuous_blPathFunctional {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F) :
    Continuous fun x : ContinuousPath ℂ => F x := by
  let : PseudoMetricSpace (ContinuousPath ℂ) := dUnifPseudoMetric
  refine Metric.continuous_iff.2 fun f η hη => ?_
  obtain ⟨a, ha, h⟩ := exists_dUnif_lt_abs_sub_le_of_isBoundedLipschitzPathFunctional hF (half_pos hη)
  refine ⟨a, ha, fun g hg => ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (h g f (show dUnif g f < a from hg)) (half_lt_self hη)

/-- A bounded Lipschitz path functional as a bounded continuous function on `ContinuousPath ℂ`. -/
noncomputable def blPathFunctionalBCF {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F) :
    ContinuousPath ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    (⟨fun x : ContinuousPath ℂ => F x, continuous_blPathFunctional hF⟩ : C(ContinuousPath ℂ, ℝ)) 2 fun a b => by
    have ha := hF.1 a
    have hb := hF.1 b
    rw [Real.dist_eq, abs_le]
    constructor <;> simp only [ContinuousMap.coe_mk] <;> linarith [abs_le.1 ha, abs_le.1 hb]

theorem blPathFunctionalBCF_apply {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F)
    (x : ContinuousPath ℂ) : blPathFunctionalBCF hF x = F x := rfl

theorem norm_blPathFunctionalBCF_le {F : (ℝ≥0 → ℂ) → ℝ} (hF : IsBoundedLipschitzPathFunctional F) :
    ‖blPathFunctionalBCF hF‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).2 fun x => by
    rw [blPathFunctionalBCF_apply, Real.norm_eq_abs]
    exact hF.1 _

end MatedCRT.FirstPass.Derived
