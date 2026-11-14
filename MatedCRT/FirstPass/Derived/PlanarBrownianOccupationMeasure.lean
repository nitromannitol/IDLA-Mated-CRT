import MatedCRT.FirstPass.Derived.PlanarBrownianOccupationGreen
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockBinders

/-!
# The occupation measure of planar Brownian motion killed on exiting a disc

For an open set `D` and `y ∈ ℂ`, the *killed occupation measure* is
`A ↦ E_y ∫_{(0, τ_D]} 1_A(𝓑_t) dt`, the image of `P_y ⊗ Lebesgue`, restricted to
`{(p, t) : 0 < t ≤ τ_D(p)}`, under `(p, t) ↦ p(t)`. For a bounded open `D` it is finite, because
`E_y τ_D < ∞`, and it integrates a bounded measurable `f` to `E_y ∫_{(0, τ_D]} f(𝓑_t) dt` (Fubini).

The *Green occupation measure* is `2 G_D(y, x) dx` on `D`. For the disc `D = B_r(z)` and `y ∈ D` it is
finite, and the two measures integrate every smooth compactly supported test function to the same
value: this is the occupation identity for smooth tests
(`integral_occupation_exitTime_ball_eq_greenFunction`).
-/

open MeasureTheory Set Filter Metric Topology MarkovProcess HarmonicBalls
open scoped ContDiff ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The space-time domain `{(p, t) : 0 < t ≤ τ_D(p)}` of the killed path. -/
def occupationDomain (D : Set ℂ) : Set (ContinuousPath ℂ × ℝ) :=
  {q | q.2 ∈ Ioc (0 : ℝ) (ContinuousPath.exitTime D q.1).toReal}

theorem measurableSet_occupationDomain {D : Set ℂ} (hD : IsOpen D) :
    MeasurableSet (occupationDomain D) := by
  have hτ : Measurable fun q : ContinuousPath ℂ × ℝ => (ContinuousPath.exitTime D q.1).toReal :=
    ((ContinuousPath.measurable_exitTime D hD).comp measurable_fst).ennreal_toReal
  exact (measurableSet_lt measurable_const measurable_snd).inter (measurableSet_le measurable_snd hτ)

/-- Evaluation `(p, t) ↦ p(t⁺)` is measurable on path space times the real line. -/
theorem measurable_eval_toNNReal :
    Measurable fun q : ContinuousPath ℂ × ℝ => q.1 q.2.toNNReal :=
  (ContinuousEval.continuous_eval (F := ContinuousPath ℂ)).measurable.comp
    (measurable_fst.prodMk measurable_snd.real_toNNReal)

/-- The occupation measure of planar Brownian motion from `y`, killed on exiting `D`. -/
noncomputable def killedOccupationMeasure (D : Set ℂ) (y : ℂ) : Measure ℂ :=
  (((planarBrownianMotion y).prod (volume : Measure ℝ)).restrict (occupationDomain D)).map
    fun q => q.1 q.2.toNNReal

/-- The total mass of the killed occupation measure is the expected exit time. -/
theorem killedOccupationMeasure_univ {D : Set ℂ} (hD : IsOpen D) (y : ℂ) :
    killedOccupationMeasure D y univ =
      ∫⁻ p, ENNReal.ofReal (ContinuousPath.exitTime D p).toReal ∂(planarBrownianMotion y) := by
  rw [killedOccupationMeasure, Measure.map_apply measurable_eval_toNNReal MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ,
    Measure.prod_apply (measurableSet_occupationDomain hD)]
  refine lintegral_congr fun p => ?_
  change volume (Ioc (0 : ℝ) (ContinuousPath.exitTime D p).toReal) = _
  rw [Real.volume_Ioc, sub_zero]

theorem isFiniteMeasure_killedOccupationMeasure {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (y : ℂ) : IsFiniteMeasure (killedOccupationMeasure D y) := by
  refine ⟨?_⟩
  rw [killedOccupationMeasure_univ hD y]
  exact (lintegral_mono fun p => ENNReal.ofReal_toReal_le).trans_lt
    (lintegral_exitTime_planarBrownianMotion_lt_top hD hDb y)

/-- Fubini for the killed occupation measure: a bounded measurable `f` integrates to
`E_y ∫_{(0, τ_D]} f(𝓑_t) dt`. -/
theorem integral_killedOccupationMeasure {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    (y : ℂ) {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    ∫ x, f x ∂(killedOccupationMeasure D y) =
      ∫ p, (∫ t in Ioc (0 : ℝ) (ContinuousPath.exitTime D p).toReal, f (p t.toNNReal))
        ∂(planarBrownianMotion y) := by
  have hS := measurableSet_occupationDomain hD
  have hF : Measurable fun q : ContinuousPath ℂ × ℝ => f (q.1 q.2.toNNReal) :=
    hf.comp measurable_eval_toNNReal
  have hfin : IsFiniteMeasure
      (((planarBrownianMotion y).prod (volume : Measure ℝ)).restrict (occupationDomain D)) := by
    refine ⟨?_⟩
    have h2 := (isFiniteMeasure_killedOccupationMeasure hD hDb y).measure_univ_lt_top
    rwa [killedOccupationMeasure, Measure.map_apply measurable_eval_toNNReal MeasurableSet.univ,
      preimage_univ] at h2
  have hint : Integrable (fun q : ContinuousPath ℂ × ℝ => f (q.1 q.2.toNNReal))
      (((planarBrownianMotion y).prod (volume : Measure ℝ)).restrict (occupationDomain D)) :=
    Integrable.of_bound hF.aestronglyMeasurable M
      (Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hM _)
  rw [killedOccupationMeasure, integral_map measurable_eval_toNNReal.aemeasurable
    hf.aestronglyMeasurable, ← integral_indicator hS,
    integral_prod _ ((integrable_indicator_iff hS).2 hint)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  beta_reduce
  rw [← integral_indicator measurableSet_Ioc]
  rfl

/-- The Green occupation measure `2 G_D(y, x) dx` on `D`. -/
noncomputable def greenOccupationMeasure (D : Set ℂ) (y : ℂ) : Measure ℂ :=
  (volume.restrict D).withDensity fun x => ENNReal.ofReal (2 * greenFunction D y x)

theorem isFiniteMeasure_greenOccupationMeasure {z y : ℂ} {r : ℝ} (hy : y ∈ ball z r) :
    IsFiniteMeasure (greenOccupationMeasure (ball z r) y) :=
  isFiniteMeasure_withDensity_ofReal ((integrableOn_greenFunction_ball z y r hy).const_mul 2).2

/-- A bounded measurable `f` integrates against the Green occupation measure of a disc to
`2 ∫_D G_D(y, x) f(x) dx`. -/
theorem integral_greenOccupationMeasure (z y : ℂ) (r : ℝ) (f : ℂ → ℝ) :
    ∫ x, f x ∂(greenOccupationMeasure (ball z r) y) =
      2 * ∫ x in ball z r, greenFunction (ball z r) y x * f x := by
  have hmeas : Measurable fun x => (2 * greenFunction (ball z r) y x).toNNReal :=
    ((measurable_greenFunction isOpen_ball y).const_mul 2).real_toNNReal
  rw [greenOccupationMeasure, ← integral_const_mul]
  refine (integral_withDensity_eq_integral_smul hmeas f).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal _
    (mul_nonneg zero_le_two (greenFunction_nonneg isBounded_ball y x)), mul_assoc]

/-- The two measures agree on smooth compactly supported tests. -/
theorem integral_killedOccupationMeasure_eq_greenOccupationMeasure {z y : ℂ} {r : ℝ}
    (hy : y ∈ ball z r) {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, g x ∂(killedOccupationMeasure (ball z r) y) =
      ∫ x, g x ∂(greenOccupationMeasure (ball z r) y) := by
  obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
  rw [integral_killedOccupationMeasure isOpen_ball isBounded_ball y hg.continuous.measurable
    (M := C) (fun x => by rw [← Real.norm_eq_abs]; exact hC x), integral_greenOccupationMeasure,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [greenFunction_of_notMem_right hx, zero_mul],
    ← integral_occupation_exitTime_ball_eq_greenFunction hy hg hgc]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  beta_reduce
  rw [ENNReal.coe_toNNReal_eq_toReal, intervalIntegral.integral_of_le ENNReal.toReal_nonneg]

end MatedCRT.KilledOccupation
