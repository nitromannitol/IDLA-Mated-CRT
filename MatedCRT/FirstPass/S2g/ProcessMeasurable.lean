import MatedCRT.FirstPass.S2g

/-! # Measurable version of the canonical cone family process (q1, fp-S2g helper)

The Section 6 consumers of Lemma 2.4 (`MatedCRTEnv.IsValid.exists_measurable_familyProcess`,
`Proofs/Measurability/BoundaryLayer.lean:369`) take the Draft statement `ConeHarmonicBallsUpToFixedTimeStmt`, whose
unprinted clause `T' = T` is not part of the corrected Lemma 2.4. They use it only to obtain a.s. a stopped family and a
measurable version of its space-time process. This file gives the second part from the canonical statement
`ConeHarmonicBallsUpToFixedTimeCanonicalStmt` alone: an `AEMeasurable` map into the function space `ℝ × ℂ → Prop`
(product σ-algebra) has a measurable version which agrees with it almost surely as a whole function. -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls

/-- **Measurable version of a Prop-valued space-time process.** If `F : Ω → (ℝ × ℂ → Prop)` is a.e. measurable for the
product σ-algebra, there is `X` whose coordinates `ω ↦ X ω p` are all measurable and with `X ω = F ω` almost surely
(as whole functions, so one null set serves every point of `ℝ × ℂ`). -/
theorem exists_measurable_coordinates_of_aemeasurable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {F : Ω → ℝ × ℂ → Prop} (hF : AEMeasurable F P) :
    ∃ X : Ω → ℝ × ℂ → Prop, (∀ p, Measurable fun ω => X ω p) ∧ ∀ᵐ ω ∂P, F ω = X ω :=
  ⟨hF.mk F, fun p => (measurable_pi_apply p).comp hF.measurable_mk, hF.ae_eq_mk.mono fun _ h => h⟩

/-- **Measurable family process from the canonical Lemma 2.4.** For a cone field, the canonical family
`Λ` of `ConeHarmonicBallsUpToFixedTimeCanonicalStmt` at the canonical time `halfBallTime (μ ω)` has a space-time process
`X` with measurable coordinates, and almost surely `X ω (t, x) ↔ t ∈ (0, T) ∧ x ∈ Λ_t` for a stopped family
`(T, Λ_t)` of harmonic balls. This is the conclusion of `MatedCRTEnv.IsValid.exists_measurable_familyProcess`
(`Proofs/Measurability/BoundaryLayer.lean:369`), obtained without the unprinted clause `T' = T` of the Draft Lemma 2.4. -/
theorem exists_measurable_familyProcess_of_canonical {Ω : Type} [MeasurableSpace Ω] {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hcan : ConeHarmonicBallsUpToFixedTimeCanonicalStmt)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) :
    ∃ X : Ω → ℝ × ℂ → Prop, (∀ p, Measurable fun ω => X ω p) ∧ ∀ᵐ ω ∂P, ∃ (T : ℝ) (Λ' : ℝ → Set ℂ),
      0 < T ∧ IsConeHarmonicBallFamilyOn (μ ω) Λ' T ∧ IsStoppedAtHalfBall Λ' T ∧
        ∀ (t : ℝ) (x : ℂ), X ω (t, x) ↔ t ∈ Ioo 0 T ∧ x ∈ Λ' t := by
  obtain ⟨_, Λ, hAE, hae⟩ := hcan γ hγ0 hγ2 Ω P hC hcirc μ hcone
  obtain ⟨X, hXm, hX⟩ := exists_measurable_coordinates_of_aemeasurable
    (P := P) (F := fun ω => familyProcess (Λ ω) (halfBallTime (μ ω))) hAE.snd
  refine ⟨X, hXm, ?_⟩
  filter_upwards [hX, hae] with ω hω hω'
  refine ⟨halfBallTime (μ ω), Λ ω, hω'.1, hω'.2.1.1, hω'.2.2, fun t x => ?_⟩
  rw [← hω]
  rfl

end MatedCRT
