import MatedCRT.FirstPass.Derived.LQGDataSpace
import MatedCRT.FirstPass.Derived.FieldCoordinateCircleAverages
import HarmonicBalls.Defs.LQG

/-!
# Measurability of the dyadic vague-limit relation between field coordinates and LQG data

For field coordinates `x : LQGMetric.CoordJ → ℝ` let `M_k(x) = lqgApprox γ h^x (2^{-k})` be the dyadic
approximation `ε^{γ²/2} e^{γ h^x_ε(z)} dz` of the γ-LQG measure (Duplantier-Sheffield) built from the circle
averages `h^x_ε = coordCircleAverage x ε`. For a countable family `(f_i)` of nonnegative Borel test functions on
`ℂ` (for instance the tents of the closed rectangles with rational corners, which determine a locally finite
measure) and a measure `μ` on `ℂ`, `IsDyadicVagueLimitAlong γ f x μ` says that `∫ f_i dM_k(x) → ∫ f_i dμ` for every
`i`.

The set of pairs `(x, d)` of coordinates and LQG data with `IsDyadicVagueLimitAlong γ f x d.toMeasure` is Borel:
both `x ↦ M_k(x)` and `d ↦ d.toMeasure` are measurable for the Giry σ-algebra, integrals of nonnegative Borel
functions are measurable in the measure, and the convergence set of a sequence of measurable real functions to a
measurable limit is measurable.

## Main statements
* `measurable_integral_of_measurable_of_nonneg`: integrals of a nonnegative Borel function against a measurable
  family of measures are measurable in the parameter.
* `measurable_lqgApprox_of_measurable`: `x ↦ lqgApprox γ (H x) ε` is measurable when `(x, z) ↦ H x ε z` is.
* `LQGData.measurable_toMeasure`: `d ↦ d.toMeasure` is measurable.
* `measurableSet_isDyadicVagueLimitAlong_toMeasure`: the relation set is measurable.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The integral of a nonnegative Borel function against a measurable family of measures is measurable in the
parameter: it is the real part of the lower Lebesgue integral, which is measurable in the measure. -/
theorem measurable_integral_of_measurable_of_nonneg {X α : Type*} [MeasurableSpace X] [MeasurableSpace α]
    {μ : X → Measure α} (hμ : Measurable μ) {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ a, 0 ≤ f a) :
    Measurable fun x => ∫ a, f a ∂(μ x) := by
  have heq : (fun x => ∫ a, f a ∂(μ x)) = fun x => (∫⁻ a, ENNReal.ofReal (f a) ∂(μ x)).toReal := by
    funext x
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hf.aestronglyMeasurable
  rw [heq]
  exact ((Measure.measurable_lintegral hf.ennreal_ofReal).comp hμ).ennreal_toReal

/-- The approximation `ε^{γ²/2} e^{γ h_ε(z)} dz` of the γ-LQG measure of a measurably parametrized field is
measurable in the parameter. -/
theorem measurable_lqgApprox_of_measurable {X : Type*} [MeasurableSpace X] (γ ε : ℝ) {H : X → ℝ → ℂ → ℝ}
    (hH : Measurable fun q : X × ℂ => H q.1 ε q.2) :
    Measurable fun x => HarmonicBalls.lqgApprox γ (H x) ε := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [HarmonicBalls.lqgApprox, withDensity_apply _ hs]
  have hρ : Measurable fun q : X × ℂ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * H q.1 ε q.2)) :=
    (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hH))).ennreal_ofReal
  exact hρ.lintegral_prod_right'

/-- The measure `∑_R (d R).1 • ι_R* (d R).2` encoded by LQG data is measurable in the data. -/
theorem LQGData.measurable_toMeasure : Measurable LQGData.toMeasure := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [LQGData.toMeasure, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_subtype_coe hs]
  refine Measurable.tsum fun R => ?_
  have h1 : Measurable fun d : LQGData => ((d R).1 : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (measurable_fst.comp (measurable_pi_apply R))
  have h2 : Measurable fun d : LQGData => ((d R).2 : Measure (ann R)) (Subtype.val ⁻¹' s) :=
    (Measure.measurable_coe (measurable_subtype_coe hs)).comp
      (measurable_subtype_coe.comp (measurable_snd.comp (measurable_pi_apply R)))
  exact h1.mul h2

/-- **Dyadic vague limit along a test family.** For test functions `f i` on `ℂ`, field coordinates `x` and a
measure `μ` on `ℂ`: for every `i`, `∫ f_i d(lqgApprox γ h^x 2^{-k}) → ∫ f_i dμ` as `k → ∞`, where
`h^x = coordCircleAverage x` is the circle-average process of the coordinates. -/
def IsDyadicVagueLimitAlong {ι : Type*} (γ : ℝ) (f : ι → ℂ → ℝ) (x : LQGMetric.CoordJ → ℝ) (μ : Measure ℂ) :
    Prop :=
  ∀ i, Tendsto (fun k : ℕ =>
      ∫ w, f i w ∂(HarmonicBalls.lqgApprox γ (coordCircleAverage x) (HarmonicBalls.dyadicScale k)))
    atTop (𝓝 (∫ w, f i w ∂μ))

/-- The dyadic approximations of the γ-LQG measure of the circle averages of the coordinates are measurable in
the coordinates. -/
theorem measurable_lqgApprox_coordCircleAverage (γ ε : ℝ) :
    Measurable fun x : LQGMetric.CoordJ → ℝ => HarmonicBalls.lqgApprox γ (coordCircleAverage x) ε := by
  refine measurable_lqgApprox_of_measurable γ ε ?_
  have h := measurable_coordCircleAverage.comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd) :
      Measurable fun q : (LQGMetric.CoordJ → ℝ) × ℂ => (q.1, ε, q.2))
  simp only [Function.comp_def] at h
  exact h

/-- **Measurability of the dyadic vague-limit relation.** For a countable family of nonnegative Borel test
functions, the set of pairs `(x, d)` of field coordinates and LQG data such that the dyadic approximations of the
γ-LQG measure of the circle averages of `x` converge to `d.toMeasure` along every test function is measurable. -/
theorem measurableSet_isDyadicVagueLimitAlong_toMeasure {ι : Type*} [Countable ι] (γ : ℝ) {f : ι → ℂ → ℝ}
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i w, 0 ≤ f i w) :
    MeasurableSet {p : (LQGMetric.CoordJ → ℝ) × LQGData |
      IsDyadicVagueLimitAlong γ f p.1 (LQGData.toMeasure p.2)} := by
  have ha : ∀ i (k : ℕ), Measurable fun p : (LQGMetric.CoordJ → ℝ) × LQGData =>
      ∫ w, f i w ∂(HarmonicBalls.lqgApprox γ (coordCircleAverage p.1) (HarmonicBalls.dyadicScale k)) :=
    fun i k => (measurable_integral_of_measurable_of_nonneg
      (measurable_lqgApprox_coordCircleAverage γ (HarmonicBalls.dyadicScale k)) (hf i) (hf0 i)).comp
        measurable_fst
  have hb : ∀ i, Measurable fun p : (LQGMetric.CoordJ → ℝ) × LQGData =>
      ∫ w, f i w ∂(LQGData.toMeasure p.2) :=
    fun i => (measurable_integral_of_measurable_of_nonneg LQGData.measurable_toMeasure (hf i)
      (hf0 i)).comp measurable_snd
  have hset : {p : (LQGMetric.CoordJ → ℝ) × LQGData |
      IsDyadicVagueLimitAlong γ f p.1 (LQGData.toMeasure p.2)} =
      ⋂ i, {p : (LQGMetric.CoordJ → ℝ) × LQGData | Tendsto (fun k : ℕ =>
        (∫ w, f i w ∂(HarmonicBalls.lqgApprox γ (coordCircleAverage p.1) (HarmonicBalls.dyadicScale k))) -
          ∫ w, f i w ∂(LQGData.toMeasure p.2)) atTop (𝓝 0)} := by
    ext p
    simp only [IsDyadicVagueLimitAlong, Set.mem_ofPred_eq, mem_iInter, tendsto_sub_nhds_zero_iff]
  rw [hset]
  exact MeasurableSet.iInter fun i => measurableSet_tendsto (𝓝 0) fun k => (ha i k).sub (hb i)

end MatedCRT.FirstPass.Derived
