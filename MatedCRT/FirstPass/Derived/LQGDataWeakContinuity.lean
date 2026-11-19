import MatedCRT.FirstPass.Derived.LQGDataSpace
import LatticeProb.Prob.PairingSymmetricAllTimes
import LatticeProb.Prob.FiniteMeasureLevyProkhorov

/-!
# Weak continuity of the cutoff-weighted measures of `LQGData`

For a continuous, compactly supported cutoff `ψ : ℂ → ℝ`, the finite measure
`6 ψ · d.toMeasure` (`LatticeProb.cutoffWeightedMeasure`) depends continuously on `d : LQGData`
for the topology of weak convergence of finite measures on `ℂ`, and hence also for the
Lévy–Prokhorov metric.

* `exists_nat_forall_mem_ann_eq_zero`: `ψ` vanishes on every annulus `ann R` with `R ≥ N`, for
  some `N`, since `tsupport ψ` is bounded and a point of `ann R` has norm at least `R - 1`.
* `annCutoffTest R hψ g`: the bounded continuous function `x ↦ (6 ψ(x))⁺ g(x)` on the compact
  annulus `ann R`, for `g : ℂ →ᵇ ℝ≥0`.
* `LQGData.lintegral_cutoffWeightedMeasure`:
  `∫⁻ g d(6 ψ · d.toMeasure) = ∑'_R (d R).1 * ∫⁻ annCutoffTest R hψ g d(d R).2`.
* `LQGData.continuous_cutoffWeightedMeasure`: the sum above has only the finitely many nonzero
  terms `R < N`, each continuous in `d` (projections and weak continuity of
  `p ↦ ∫ f dp` on `ProbabilityMeasure (ann R)`), so `d ↦ 6 ψ · d.toMeasure` is continuous by
  `FiniteMeasure.tendsto_iff_forall_lintegral_tendsto`.
* `LQGData.continuous_levyProkhorov_cutoffWeightedMeasure`: the same map into the Lévy–Prokhorov
  metric space of finite measures, through
  `LatticeProb.continuous_levyProkhorov_ofMeasure_finiteMeasure`.
-/

open MeasureTheory Topology Filter
open LatticeProb (cutoffWeightedMeasure coe_cutoffWeightedMeasure
  continuous_levyProkhorov_ofMeasure_finiteMeasure)
open scoped NNReal ENNReal BoundedContinuousFunction

noncomputable section

namespace MatedCRT.FirstPass.Derived

/-- A compactly supported `ψ` vanishes on the annuli `ann R` with `R ≥ N`, for some `N`. -/
theorem exists_nat_forall_mem_ann_eq_zero {ψ : ℂ → ℝ} (hψc : HasCompactSupport ψ) :
    ∃ N : ℕ, ∀ R : ℕ, N ≤ R → ∀ z ∈ ann R, ψ z = 0 := by
  obtain ⟨r, hr⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hψc.isCompact.isBounded
  refine ⟨⌈r⌉₊ + 2, fun R hR z hz => image_eq_zero_of_notMem_tsupport fun hzt => ?_⟩
  have h1 : ‖z‖ ≤ r := mem_closedBall_zero_iff.1 (hr hzt)
  have h2 := le_norm_add_one_of_mem_ann hz
  have h3 : (⌈r⌉₊ : ℝ) + 2 ≤ R := by exact_mod_cast hR
  have h4 := Nat.le_ceil r
  linarith

/-- The bounded continuous test function `x ↦ (6 ψ(x))⁺ g(x)` on the compact annulus `ann R`. -/
def annCutoffTest (R : ℕ) {ψ : ℂ → ℝ} (hψ : Continuous ψ) (g : ℂ →ᵇ ℝ≥0) : ann R →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => (6 * ψ x).toNNReal * g x,
      (continuous_real_toNNReal.comp ((continuous_const.mul hψ).comp continuous_subtype_val)).mul
        (g.continuous.comp continuous_subtype_val)⟩

theorem annCutoffTest_apply (R : ℕ) {ψ : ℂ → ℝ} (hψ : Continuous ψ) (g : ℂ →ᵇ ℝ≥0)
    (x : ann R) : annCutoffTest R hψ g x = (6 * ψ x).toNNReal * g x :=
  rfl

theorem coe_annCutoffTest_apply (R : ℕ) {ψ : ℂ → ℝ} (hψ : Continuous ψ) (g : ℂ →ᵇ ℝ≥0)
    (x : ann R) :
    ((annCutoffTest R hψ g x : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (6 * ψ x) * g x := by
  rw [annCutoffTest_apply]
  exact ENNReal.coe_mul _ _

/-- The integral of `g` against the cutoff-weighted measure `6 ψ · d.toMeasure` as a series over
the annuli: `∑'_R (d R).1 * ∫⁻ (6 ψ)⁺ g d(d R).2`. -/
theorem LQGData.lintegral_cutoffWeightedMeasure (d : LQGData) {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (g : ℂ →ᵇ ℝ≥0) :
    ∫⁻ z, (g z : ℝ≥0∞) ∂(cutoffWeightedMeasure d.toMeasure hψ hψc 6 : Measure ℂ) =
      ∑' R, ((d R).1 : ℝ≥0∞) *
        ∫⁻ x, (annCutoffTest R hψ g x : ℝ≥0∞) ∂((d R).2 : Measure (ann R)) := by
  have hF : Measurable fun z => ENNReal.ofReal (6 * ψ z) :=
    (continuous_const.mul hψ).measurable.ennreal_ofReal
  have hg : Measurable fun z => ((g z : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp g.continuous).measurable
  have hFg : Measurable fun z => ENNReal.ofReal (6 * ψ z) * ((g z : ℝ≥0) : ℝ≥0∞) := hF.mul hg
  rw [coe_cutoffWeightedMeasure, lintegral_withDensity_eq_lintegral_mul _ hF hg]
  simp only [Pi.mul_apply]
  rw [LQGData.toMeasure, lintegral_sum_measure]
  refine tsum_congr fun R => ?_
  rw [lintegral_smul_measure, smul_eq_mul, lintegral_map hFg measurable_subtype_coe]
  simp only [coe_annCutoffTest_apply]

/-- **Weak continuity of the cutoff-weighted measure**: for a continuous, compactly supported
cutoff `ψ`, the finite measure `6 ψ · d.toMeasure` depends continuously on `d : LQGData` for the
topology of weak convergence of finite measures on `ℂ`. (The nonnegativity of `ψ` is not needed.) -/
theorem LQGData.continuous_cutoffWeightedMeasure (ψ : ℂ → ℝ) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (_hψ0 : ∀ z, 0 ≤ ψ z) :
    Continuous fun d : LQGData => cutoffWeightedMeasure (LQGData.toMeasure d) hψ hψc 6 := by
  obtain ⟨N, hN⟩ := exists_nat_forall_mem_ann_eq_zero hψc
  have hT : ∀ (R : ℕ) (p : ProbabilityMeasure (ann R)) (f : ann R →ᵇ ℝ≥0),
      ((p.toFiniteMeasure.testAgainstNN f : ℝ≥0) : ℝ≥0∞) = ∫⁻ x, f x ∂(p : Measure (ann R)) :=
    fun _ _ _ => FiniteMeasure.testAgainstNN_coe_eq
  have hsum : ∀ (d : LQGData) (g : ℂ →ᵇ ℝ≥0),
      ∫⁻ z, (g z : ℝ≥0∞) ∂(cutoffWeightedMeasure d.toMeasure hψ hψc 6 : Measure ℂ) =
        ((∑ R ∈ Finset.range N,
          (d R).1 * (d R).2.toFiniteMeasure.testAgainstNN (annCutoffTest R hψ g) : ℝ≥0) :
            ℝ≥0∞) := by
    intro d g
    have hvan : ∀ R ∉ Finset.range N, ((d R).1 : ℝ≥0∞) *
        ∫⁻ x, (annCutoffTest R hψ g x : ℝ≥0∞) ∂((d R).2 : Measure (ann R)) = 0 := by
      intro R hR
      rw [Finset.mem_range, not_lt] at hR
      have h0 : ∀ x : ann R, ((annCutoffTest R hψ g x : ℝ≥0) : ℝ≥0∞) = 0 := by
        intro x
        rw [coe_annCutoffTest_apply, hN R hR x x.2]
        simp
      rw [lintegral_congr h0, lintegral_zero, mul_zero]
    rw [LQGData.lintegral_cutoffWeightedMeasure d hψ hψc g, tsum_eq_sum hvan,
      ENNReal.ofNNReal_finsetSum]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [ENNReal.coe_mul, hT]
  have hcoord : ∀ R : ℕ, Continuous fun d : LQGData => d R := fun R => continuous_apply R
  have hcont : ∀ g : ℂ →ᵇ ℝ≥0, Continuous fun d : LQGData =>
      ((∑ R ∈ Finset.range N,
        (d R).1 * (d R).2.toFiniteMeasure.testAgainstNN (annCutoffTest R hψ g) : ℝ≥0) :
          ℝ≥0∞) := by
    intro g
    refine ENNReal.continuous_coe.comp (continuous_finsetSum _ fun R _ => ?_)
    exact (hcoord R).fst.mul
      ((ProbabilityMeasure.continuous_testAgainstNN_eval (annCutoffTest R hψ g)).comp
        (hcoord R).snd)
  refine continuous_iff_continuousAt.2 fun d => ?_
  rw [ContinuousAt, FiniteMeasure.tendsto_iff_forall_lintegral_tendsto]
  intro g
  simp only [hsum]
  exact (hcont g).tendsto d

/-- **Lévy–Prokhorov continuity of the cutoff-weighted measure**: for every continuous, compactly
supported `ψ ≥ 0`, `d ↦ 6 ψ · d.toMeasure` is continuous from `LQGData` to the Lévy–Prokhorov
metric space of finite measures on `ℂ`. -/
theorem LQGData.continuous_levyProkhorov_cutoffWeightedMeasure : ∀ (ψ : ℂ → ℝ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ), (∀ z, 0 ≤ ψ z) →
      Continuous fun d : LQGData =>
        LevyProkhorov.ofMeasure (cutoffWeightedMeasure (LQGData.toMeasure d) hψ hψc 6) :=
  fun ψ hψ hψc hψ0 =>
    continuous_levyProkhorov_ofMeasure_finiteMeasure.comp
      (LQGData.continuous_cutoffWeightedMeasure ψ hψ hψc hψ0)

end MatedCRT.FirstPass.Derived

end
