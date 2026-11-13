import MatedCRT.FirstPass.Derived.InterpolatedLawWiring
import MatedCRT.Proofs.Sec4.SubsequentialProperties.ObstacleApproximation
import LatticeProb.Prob.InterpolatedLawRandom
import LatticeProb.Prob.ProbabilityMeasureBorel

/-!
# The interpolated quenched walk law as a random continuous map (Theorem 2.11, BG20 Theorem 1.2)

For a measurable version `η'` of the curve of a valid environment `S`, a cell size `ε > 0` and the
quenched laws `Q^ε(k)(ω)` of the interpolated embedded walks (`walkPathLaw`, with the vertex positions
`vertexPoint ε (η' ω)` and the time scaling `m_ε`), `interpWalkLaw S η' ε ω` is the interpolated law
`P̃^ε_z = ∑_k w_k(z) Q^ε(k) / ∑_k w_k(z)`, `w_k(z) = (ε − dist(z, H_k))₊`, `H_k = cell ε (η' ω) k`, as a
continuous map `ℂ → Prob(ContinuousPath ℂ)` (Lattice-Probability `interpLawCMT`).

* `aemeasurable_interpWalkLaw`: `ω ↦ P̃^ε(ω)` is almost everywhere measurable for the Borel structure of
  `C(ℂ, Prob(ContinuousPath ℂ))`.
* `interpWalkLaw_eq_of_good`: on the almost sure event on which `η' ω` is proper and onto, `P̃^ε(ω)` is the
  interpolated law of Lattice-Probability (`interpLaw`), whence its Lévy–Prokhorov estimates
  (`levyProkhorovDist_interpLaw_le`) once a metric on path space is fixed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

namespace MatedCRT

variable {Ω : Type} [MeasurableSpace Ω]

/-- The interpolated quenched walk law `P̃^ε(ω) : ℂ → Prob(ContinuousPath ℂ)`, built from the cells of the
curve `η' ω` and the quenched path laws `Q^ε(k)(ω)` of the walk on the mated-CRT map. -/
noncomputable def interpWalkLaw (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (ε : ℝ) (ω : Ω) :
    C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) :=
  interpLawCMT (ι := ℤ) (fun k => cell ε (⇑(η' ω)) k) ε
    (fun k => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)

/-- The vertex positions `k ↦ η'(ε k)` are a measurable function of the environment. -/
theorem measurable_vertexPoint_curve {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (ε : ℝ) :
    Measurable fun ω => vertexPoint ε (⇑(η' ω)) :=
  measurable_pi_iff.2 fun k =>
    (continuous_eval_const (ε * (k : ℝ))).measurable.comp hη'

/-- For a proper onto curve and `ε > 0`, the interpolation weights are locally finite and positive. -/
theorem interpWeight_good_of_proper_surjective {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ}
    (hη : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hsurj : Function.Surjective η) :
    (∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε η k) ε k y ≠ 0}.Finite) ∧
      ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε η k) ε k z ≠ 0 := by
  obtain ⟨hne, hcov, hfin⟩ := cell_cover_finite_of_proper_surjective hε hη hsurj
  exact ⟨fun z => interpWeight_locallyFinite hne ε hfin z, fun z => exists_interpWeight_ne_zero hε hcov z⟩

/-- Almost surely the curve is proper and onto, so the interpolation weights are locally finite and
positive for the measurable version `η'`. -/
theorem MatedCRTEnv.IsValid.ae_interpWeight_good {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P,
      (∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite) ∧
        ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0 := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hae] with ω hap hcoc hω
  rw [hω]
  exact interpWeight_good_of_proper_surjective hε hcoc hap.2.2.1

/-- The interpolated quenched walk law is an almost everywhere measurable random element of
`C(ℂ, Prob(ContinuousPath ℂ))`. -/
theorem aemeasurable_interpWalkLaw {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℝ} (hε : 0 < ε) : AEMeasurable (interpWalkLaw S η' ε) S.P :=
  aemeasurable_interpLawCMT (H := fun ω k => cell ε (⇑(η' ω)) k)
    (fun k z => measurable_infDist_cell hη' hε k z) (hS.ae_interpWeight_good hae hε)
    (Q := fun k ω => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
    (fun k => measurable_walkPathLaw hS (measurable_vertexPoint_curve hη' ε) (S.mε_nonneg ε) ε k)

/-- On the good event, `P̃^ε(ω)` is the interpolated law of Lattice-Probability. -/
theorem interpWalkLaw_eq_of_good (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} {ω : Ω}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0) (z : ℂ) :
    interpWalkLaw S η' ε ω z =
      interpLaw (fun k => cell ε (⇑(η' ω)) k) ε hloc hpos
        (fun k => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω) z := by
  unfold interpWalkLaw
  rw [interpLawCMT_of_good hloc hpos]
  rfl

end MatedCRT
