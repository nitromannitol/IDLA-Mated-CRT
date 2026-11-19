import MatedCRT.FirstPass.Derived.InterpLawProkhorovBound

/-!
# Pushforwards of interpolated laws: Lévy–Prokhorov balls are convex after a measurable map

Let `P̃^ε_z = ∑_k w_k(z) Q^ε(k) / ∑_k w_k(z)` be the interpolated law of a family `Q^ε(k)` of probability measures
(`interpLaw`, `interpLawCMT`).  For a measurable map `F` into a metric space, the image `F_* P̃^ε_z` is the
interpolated law of the images `F_* Q^ε(k)` (`weightedMixture_map`, `interpLaw_map`), hence a Lévy–Prokhorov ball
around a fixed law `μ` contains `F_* P̃^ε_z` as soon as it contains every `F_* Q^ε(k)` with positive weight at `z`
(`levyProkhorovDist_map_interpLaw_le`, `levyProkhorovDist_map_interpWalkLaw_le`).

This is the passage from the comparison of the walk laws from the vertices with Brownian motion, for the stopped
curve classes (curves modulo time parametrization), to the interpolated walk law of Berestycki–Gwynne (2020), Lemma 7.4.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

section Generic

variable {Z : Type*} [PseudoMetricSpace Z] {ι : Type*} {E E' : Type*} [MeasurableSpace E]
  [MeasurableSpace E']

/-- The image of a mixture under a measurable map is the mixture of the images. -/
theorem weightedMixture_map {c : ι → ℝ≥0} (Q : ι → Measure E) {F : E → E'} (hF : Measurable F) :
    (weightedMixture c Q).map F = weightedMixture c fun k => (Q k).map F := by
  unfold weightedMixture
  rw [Measure.map_sum hF.aemeasurable]
  congr 1
  ext1 k
  exact Measure.map_smul _ hF.aemeasurable

/-- The image of the interpolated law under a measurable map is the interpolated law of the images. -/
theorem interpLaw_map {H : ι → Set Z} {ε : ℝ}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E) {F : E → E'}
    (hF : Measurable F) (z : Z) :
    ((interpLaw H ε hloc hpos Q z : ProbabilityMeasure E) : Measure E).map F =
      ((interpLaw H ε hloc hpos (fun k => (Q k).map F) z : ProbabilityMeasure E') :
        Measure E') := by
  unfold interpLaw
  rw [coe_weightedMixturePM, coe_weightedMixturePM, weightedMixture_map _ hF]
  rfl

variable [PseudoMetricSpace E'] [OpensMeasurableSpace E']

/-- **Lévy–Prokhorov balls are convex after a measurable map.**  If `F_* Q k` is within Lévy–Prokhorov distance `δ`
of `μ` for every component with positive interpolation weight at `z`, then so is `F_*` of the interpolated law. -/
theorem levyProkhorovDist_map_interpLaw_le {H : ι → Set Z} {ε : ℝ}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E) {F : E → E'}
    (hF : Measurable F) (μ : ProbabilityMeasure E') (z : Z) {δ : ℝ}
    (hQ : ∀ k, interpWeight H ε k z ≠ 0 →
      levyProkhorovDist ((Q k : Measure E).map F) (μ : Measure E') ≤ δ) :
    levyProkhorovDist (((interpLaw H ε hloc hpos Q z : ProbabilityMeasure E) : Measure E).map F)
      (μ : Measure E') ≤ δ := by
  rw [interpLaw_map hloc hpos Q hF z]
  exact levyProkhorovDist_interpLaw_le_of_weight hloc hpos (fun k => (Q k).map F) μ z
    fun k hk => hQ k hk

end Generic

section Walk

variable {Ω : Type} [MeasurableSpace Ω] {E' : Type*} [MeasurableSpace E'] [PseudoMetricSpace E']
  [OpensMeasurableSpace E']

/-- **The interpolated quenched walk law, after a measurable map.**  For a curve `η' ω` whose interpolation weights
are locally finite and positive, `F_*(P̃^ε_z(ω))` is within Lévy–Prokhorov distance `δ` of `μ` as soon as `F_*` of
the quenched walk law `Q^ε(k)(ω)` of each cell with positive weight at `z` is. -/
theorem levyProkhorovDist_map_interpWalkLaw_le (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} {ω : Ω}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z,
      {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0)
    {F : ContinuousPath ℂ → E'} (hF : Measurable F) (μ : ProbabilityMeasure E') (z : ℂ) {δ : ℝ}
    (hQ : ∀ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0 →
      levyProkhorovDist
        (((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω :
          ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map F)
        (μ : Measure E') ≤ δ) :
    levyProkhorovDist (((interpWalkLaw S η' ε ω z : ProbabilityMeasure (ContinuousPath ℂ)) :
      Measure (ContinuousPath ℂ)).map F) (μ : Measure E') ≤ δ := by
  rw [interpWalkLaw_eq_of_good S η' hloc hpos z]
  exact levyProkhorovDist_map_interpLaw_le hloc hpos _ hF μ z hQ

end Walk

end MatedCRT.FirstPass.Derived
