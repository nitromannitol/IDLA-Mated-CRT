import MatedCRT.FirstPass.Derived.ReversibilityPairingDiscrete

/-!
# Lévy–Prokhorov bounds for interpolated laws from the selected-cell laws

Let `P̃^ε_z = ∑_k w_k(z) Q^ε(k) / ∑_k w_k(z)`, `w_k(z) = (ε - dist(z, H_k))₊`, be the interpolated law of a family
`Q^ε(k)` of probability measures indexed by the cells `H_k` (Lattice-Probability `interpLaw`, `interpLawCMT`).

* `levyProkhorovDist_interpLaw_le_of_weight`, `levyProkhorovDist_interpLawCMT_le`: Lévy–Prokhorov balls are convex:
  if every component `Q k` with positive weight at `z` is within `δ` of `μ`, so is `P̃^ε_z`.
* `levyProkhorovDist_interpLaw_le_add`, `levyProkhorovDist_interpLawCMT_le_add`: the transfer from a selected-cell
  law field `P` (Berestycki–Gwynne (2020), the law `P^ε_z` of the walk started from the vertex whose cell contains
  `z`) to the interpolated law. If each component `Q k` with positive weight at a point `z ∈ K` is the selected law
  `P z'` of a point `z'` with `|z - z'| < 2ε`, then for every law field `L`
  `d_LP(P̃^ε_z, L_z) ≤ sup_{z' ∈ K^{2ε}} d_LP(P_{z'}, L_{z'}) + sup_{z ∈ K, |z - z'| < 2ε} d_LP(L_{z'}, L_z)`.
  No measurable selection of `z'` is involved.
* `pathLevyProkhorovEDist_interpWalkLaw_le_add`: the transfer for the interpolated quenched walk law
  `interpWalkLaw S η' ε ω` of the mated-CRT map, for the Lévy–Prokhorov distance of the local uniform metric on paths.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

section Generic

variable {Z : Type*} [PseudoMetricSpace Z] {ι : Type*} {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]

/-- **Lévy–Prokhorov balls are convex (interpolated law).** If every component `Q k` with positive interpolation
weight at `z` is within Lévy–Prokhorov distance `δ` of `μ`, so is the interpolated law at `z`. -/
theorem levyProkhorovDist_interpLaw_le_of_weight [OpensMeasurableSpace E] {H : ι → Set Z} {ε : ℝ}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E)
    (μ : ProbabilityMeasure E) (z : Z) {δ : ℝ}
    (hQ : ∀ k, interpWeight H ε k z ≠ 0 → levyProkhorovDist (Q k : Measure E) (μ : Measure E) ≤ δ) :
    levyProkhorovDist (interpLaw H ε hloc hpos Q z : Measure E) (μ : Measure E) ≤ δ := by
  obtain ⟨k₀, hk₀⟩ := hpos z
  have hδ : 0 ≤ δ := le_trans (by unfold levyProkhorovDist; exact ENNReal.toReal_nonneg) (hQ k₀ hk₀)
  rw [levyProkhorovDist_comm]
  refine levyProkhorovDist_interpLaw_le hloc hpos Q μ z hδ fun k hk => ?_
  rw [levyProkhorovDist_comm]
  exact hQ k ((interpWeight_ne_zero_iff H ε k z).2 hk)

/-- **Lévy–Prokhorov balls are convex (interpolated law as a continuous map).** Under the local finiteness and
positivity hypotheses of the interpolation weights, if every component `Q k` with positive weight at `z` is within
Lévy–Prokhorov distance `δ` of `μ`, so is `interpLawCMT H ε Q z`. -/
theorem levyProkhorovDist_interpLawCMT_le [BorelSpace E] [Nonempty ι] {H : ι → Set Z} {ε : ℝ}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E)
    (μ : ProbabilityMeasure E) (z : Z) {δ : ℝ}
    (hQ : ∀ k, interpWeight H ε k z ≠ 0 → levyProkhorovDist (Q k : Measure E) (μ : Measure E) ≤ δ) :
    levyProkhorovDist (interpLawCMT H ε Q z : Measure E) (μ : Measure E) ≤ δ := by
  rw [interpLawCMT_of_good hloc hpos Q]
  exact levyProkhorovDist_interpLaw_le_of_weight hloc hpos Q μ z hQ

/-- **Transfer from the selected-cell laws to the interpolated law.** Let `P` be a law field such that every
component `Q k` with positive weight at a point `z ∈ K` is the law `P z'` of some point `z'` with
`dist z z' < 2ε`. If `d_LP(P z', L z') ≤ a` on the `2ε`-thickening of `K` and `d_LP(L z', L z) ≤ b` whenever
`z ∈ K` and `dist z z' < 2ε`, then `d_LP(P̃^ε_z, L z) ≤ a + b` on `K`. -/
theorem levyProkhorovDist_interpLaw_le_add [OpensMeasurableSpace E] {H : ι → Set Z} {ε : ℝ}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E)
    (P L : Z → ProbabilityMeasure E) {K : Set Z} {a b : ℝ}
    (hsel : ∀ z ∈ K, ∀ k, interpWeight H ε k z ≠ 0 → ∃ z', dist z z' < 2 * ε ∧ P z' = Q k)
    (ha : ∀ z' ∈ Metric.thickening (2 * ε) K, levyProkhorovDist (P z' : Measure E) (L z' : Measure E) ≤ a)
    (hb : ∀ z ∈ K, ∀ z', dist z z' < 2 * ε →
      levyProkhorovDist (L z' : Measure E) (L z : Measure E) ≤ b)
    {z : Z} (hz : z ∈ K) :
    levyProkhorovDist (interpLaw H ε hloc hpos Q z : Measure E) (L z : Measure E) ≤ a + b := by
  refine levyProkhorovDist_interpLaw_le_of_weight hloc hpos Q (L z) z fun k hk => ?_
  obtain ⟨z', hzz', hPQ⟩ := hsel z hz k hk
  have hz' : z' ∈ Metric.thickening (2 * ε) K := Metric.mem_thickening_iff.2 ⟨z, hz, by rwa [dist_comm]⟩
  have htri : levyProkhorovDist (P z' : Measure E) (L z : Measure E) ≤
      levyProkhorovDist (P z' : Measure E) (L z' : Measure E) +
        levyProkhorovDist (L z' : Measure E) (L z : Measure E) := by
    apply levyProkhorovDist_triangle
  rw [← hPQ]
  exact htri.trans (add_le_add (ha z' hz') (hb z hz z' hzz'))

/-- **Transfer from the selected-cell laws to the interpolated law (continuous map form).** The bound of
`levyProkhorovDist_interpLaw_le_add` for `interpLawCMT H ε Q`, under the local finiteness and positivity
hypotheses of the interpolation weights. -/
theorem levyProkhorovDist_interpLawCMT_le_add [BorelSpace E] [Nonempty ι] {H : ι → Set Z} {ε : ℝ}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E)
    (P L : Z → ProbabilityMeasure E) {K : Set Z} {a b : ℝ}
    (hsel : ∀ z ∈ K, ∀ k, interpWeight H ε k z ≠ 0 → ∃ z', dist z z' < 2 * ε ∧ P z' = Q k)
    (ha : ∀ z' ∈ Metric.thickening (2 * ε) K, levyProkhorovDist (P z' : Measure E) (L z' : Measure E) ≤ a)
    (hb : ∀ z ∈ K, ∀ z', dist z z' < 2 * ε →
      levyProkhorovDist (L z' : Measure E) (L z : Measure E) ≤ b)
    {z : Z} (hz : z ∈ K) :
    levyProkhorovDist (interpLawCMT H ε Q z : Measure E) (L z : Measure E) ≤ a + b := by
  rw [interpLawCMT_of_good hloc hpos Q]
  exact levyProkhorovDist_interpLaw_le_add hloc hpos Q P L hsel ha hb hz

end Generic

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Transfer from the selected-cell walk laws to the interpolated quenched walk law** (Berestycki–Gwynne (2020),
Theorem 1.2 for `P̃^ε`). For a curve `η' ω` whose interpolation weights are locally finite and positive, let `P`
be a law field such that the quenched path law `Q^ε(k)(ω)` of every cell `H_k` with positive weight at a point
`z ∈ K` is `P z'` for some `z'` with `|z - z'| < 2ε`. Then, in the Lévy–Prokhorov distance of the local uniform
metric on paths, `d(P̃^ε_z(ω), L z) ≤ a + b` on `K` whenever `d(P z', L z') ≤ a` on the `2ε`-thickening of `K`
and `d(L z', L z) ≤ b` for `z ∈ K`, `|z - z'| < 2ε`. -/
theorem pathLevyProkhorovEDist_interpWalkLaw_le_add (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} {ω : Ω}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0)
    (P L : ℂ → ProbabilityMeasure (ContinuousPath ℂ)) {K : Set ℂ} {a b : ℝ≥0∞}
    (hsel : ∀ z ∈ K, ∀ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0 →
      ∃ z', dist z z' < 2 * ε ∧
        P z' = walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
    (ha : ∀ z' ∈ Metric.thickening (2 * ε) K, pathLevyProkhorovEDist (P z') (L z') ≤ a)
    (hb : ∀ z ∈ K, ∀ z', dist z z' < 2 * ε → pathLevyProkhorovEDist (L z') (L z) ≤ b)
    {z : ℂ} (hz : z ∈ K) :
    pathLevyProkhorovEDist (interpWalkLaw S η' ε ω z) (L z) ≤ a + b := by
  rcases eq_or_ne a ⊤ with rfl | ha'
  · simp
  rcases eq_or_ne b ⊤ with rfl | hb'
  · simp
  let : PseudoMetricSpace (ContinuousPath ℂ) := dUnifPseudoMetric
  have hOMS : @OpensMeasurableSpace (ContinuousPath ℂ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _ ‹_›)) _ :=
    opensMeasurableSpace_dUnif
  have h := levyProkhorovDist_interpLaw_le_add hloc hpos
    (fun k => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω) P L
    (a := a.toReal) (b := b.toReal) hsel
    (fun z' hz' => ENNReal.toReal_mono ha' (ha z' hz'))
    (fun z₀ hz₀ z' hzz' => ENNReal.toReal_mono hb' (hb z₀ hz₀ z' hzz')) hz
  rw [interpWalkLaw_eq_of_good S η' hloc hpos z]
  show levyProkhorovEDist _ _ ≤ _
  rw [← ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
  refine (ENNReal.ofReal_le_ofReal h).trans_eq ?_
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha',
    ENNReal.ofReal_toReal hb']

end MatedCRT.FirstPass.Derived
