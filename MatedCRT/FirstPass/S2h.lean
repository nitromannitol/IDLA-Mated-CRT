import MatedCRT.FirstPass.S2g.Family
import MatedCRT.FirstPass.Frozen.S1c
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Cone bad null hull: reduction to two measurable null hulls (fp-S2h, z1)

Owner: z1 (task fp-S2h-cone-bad-null-hull). Target: `ConeBadNullHullStep` (FirstPass/S2g/Family.lean) and
`ConeClosureGoodMeasureLawStep` (FirstPass/S2f.lean).

The bad set of `BadMeasureNullHull` is the union of two sets of measures:
* `{ν | HasRatPlateauCert ν}` (certificate part; written argument: notes/fp-gaps/CHATGPT-cone-good-set.md
  Sections 1-3, 5, 6);
* `{ν | ¬ LeastSuperOK ν}` (least-supersolution part; NO measure-level written argument, see
  `ConeLeastSuperNullHullStep`).

This file proves the code bridge `nullHull_of_analytic_code` (a Lusin-type code set gives a measurable null hull on
`Measure ℂ`) and the union lemma, and reduces `ConeBadNullHullStep` and `ConeClosureGoodMeasureLawStep` to the two
open steps. Nothing here is frozen; the open steps are NEW.
-/

namespace MatedCRT

open MeasureTheory Set Filter

/-- A union of two measurable null hulls is a measurable null hull. -/
theorem nullHull_union {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    {A₁ A₂ : Set (Measure ℂ)}
    (h₁ : ∃ N : Set (Measure ℂ), MeasurableSet N ∧ A₁ ⊆ N ∧ P (μ ⁻¹' N) = 0)
    (h₂ : ∃ N : Set (Measure ℂ), MeasurableSet N ∧ A₂ ⊆ N ∧ P (μ ⁻¹' N) = 0) :
    ∃ N : Set (Measure ℂ), MeasurableSet N ∧ A₁ ∪ A₂ ⊆ N ∧ P (μ ⁻¹' N) = 0 := by
  obtain ⟨N₁, hN₁, hs₁, h₀₁⟩ := h₁
  obtain ⟨N₂, hN₂, hs₂, h₀₂⟩ := h₂
  refine ⟨N₁ ∪ N₂, hN₁.union hN₂, Set.union_subset_union hs₁ hs₂, ?_⟩
  rw [Set.preimage_union]
  exact measure_union_null h₀₁ h₀₂

/-- **Code bridge (fp-S2h).** Let `f` be a measurable code of measures with values in `ℕ → ℝ`, and let `A` be a set
of measures whose codes lie in an analytic set `B` of codes. Suppose the code event `{ω | f (μ ω) ∈ B}` lies in a
measurable `P`-null set `M`. Then `A` has a measurable null hull on `Measure ℂ`. The proof uses Lusin's theorem
(`FrozenUniversalMeasurabilityOfAnalytic`: an analytic set is null-measurable for every finite measure) for the law
of the codes: `B` agrees a.e. with a measurable `S`, and the discrepancy set `D` is covered by a measurable null set `T`. -/
theorem nullHull_of_analytic_code {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic) (μ : Ω → Measure ℂ) (f : Measure ℂ → (ℕ → ℝ))
    (hf : Measurable f) (hμ : Measurable fun ω => f (μ ω)) (A : Set (Measure ℂ)) (B : Set (ℕ → ℝ))
    (hBa : AnalyticSet B) (hAB : A ⊆ f ⁻¹' B) (M : Set Ω) (hM0 : P M = 0)
    (hcov : ∀ ω, f (μ ω) ∈ B → ω ∈ M) :
    ∃ N : Set (Measure ℂ), MeasurableSet N ∧ A ⊆ N ∧ P (μ ⁻¹' N) = 0 := by
  have : IsProbabilityMeasure (P.map fun ω => f (μ ω)) :=
    (Measure.isProbabilityMeasure_map_iff hμ.aemeasurable).mpr inferInstance
  have hnull : NullMeasurableSet B (P.map fun ω => f (μ ω)) :=
    hF1 (ℕ → ℝ) (P.map fun ω => f (μ ω)) inferInstance B hBa
  obtain ⟨S, hS, hBS⟩ := hnull
  have hD : (P.map fun ω => f (μ ω)) {x | ¬ (x ∈ B ↔ x ∈ S)} = 0 := by
    refine measure_mono_null (fun x hx => fun heq => hx (eq_iff_iff.mp heq)) (ae_iff.1 hBS)
  have hT : P ((fun ω => f (μ ω)) ⁻¹' toMeasurable (P.map fun ω => f (μ ω)) {x | ¬ (x ∈ B ↔ x ∈ S)}) = 0 := by
    rw [← Measure.map_apply hμ (measurableSet_toMeasurable _ _), measure_toMeasurable]
    exact hD
  refine ⟨f ⁻¹' (S ∪ toMeasurable (P.map fun ω => f (μ ω)) {x | ¬ (x ∈ B ↔ x ∈ S)}),
    hf (hS.union (measurableSet_toMeasurable _ _)), ?_, ?_⟩
  · intro ν hν
    have hBν : f ν ∈ B := hAB hν
    by_cases hSν : f ν ∈ S
    · exact Or.inl hSν
    · exact Or.inr (subset_toMeasurable _ _ (fun hiff => hSν (hiff.mp hBν)))
  · refine measure_mono_null ?_ (measure_union_null hM0 hT)
    intro ω hω
    by_cases hB : f (μ ω) ∈ B
    · exact Or.inl (hcov ω hB)
    · refine Or.inr ?_
      have h' : f (μ ω) ∈ S ∪ toMeasurable (P.map fun ω => f (μ ω)) {x | ¬ (x ∈ B ↔ x ∈ S)} := hω
      rcases h' with h | h
      · exact subset_toMeasurable _ _ (show f (μ ω) ∈ {x | ¬ (x ∈ B ↔ x ∈ S)} from fun hiff => hB (hiff.mpr h))
      · exact h

/-- **OPEN (NEW; z1, fp-S2h).** The certificate part of the bad set has a measurable null hull for every cone field:
the measures with a rational plateau pair of certificates are covered by a measurable set of `Measure ℂ` whose
preimage under the field is `P`-null. Written argument: notes/fp-gaps/CHATGPT-cone-good-set.md Sections 1-3 (Borel
relation of certificate codes, analytic projection), 5 (plateau radii, Tonelli, scaling, zero law), 5.4 (transfer to
the cone), 6 (null hull). Not proved here. -/
def ConeCertificateNullHullStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∃ N : Set (Measure ℂ), MeasurableSet N ∧ {ν | HasRatPlateauCert ν} ⊆ N ∧ P (μ ⁻¹' N) = 0

/-- **OPEN (NEW, NO WRITTEN MEASURE-LEVEL ARGUMENT; z1, fp-S2h).** The least-supersolution part of the bad set has a
measurable null hull for every cone field: the measures `ν` for which `leastSupersolution ν (3/4) 0 s` is not a
supersolution for some `s > 0` are covered by a measurable set of `Measure ℂ` with `P`-null preimage. The source
(HB Draft `LeastSupersolutionMemStmt`, harmonic-balls-lqg `HarmonicBalls/Draft/Section3.lean:47`) is only an
almost-sure statement `∀ᵐ ω, ...` for the LQG measure; an almost-sure property of `μ ω` does not give a measurable
superset in `Measure ℂ` (CHATGPT-cone-good-set.md Section 8, bullet "almost-sure closure theorem alone"). Not proved. -/
def ConeLeastSuperNullHullStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∃ N : Set (Measure ℂ), MeasurableSet N ∧ {ν | ¬ LeastSuperOK ν} ⊆ N ∧ P (μ ⁻¹' N) = 0

/-- **Reduction (fp-S2h).** The two open parts give the bad null hull `ConeBadNullHullStep`. -/
theorem coneBadNullHull_of_parts (hc : ConeCertificateNullHullStep) (hl : ConeLeastSuperNullHullStep) :
    ConeBadNullHullStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  have h := nullHull_union P μ (hc γ hγ hγ2 Ω P hC hcirc μ hcone) (hl γ hγ hγ2 Ω P hC hcirc μ hcone)
  unfold BadMeasureNullHull
  rw [Set.ofPred_or]
  exact h

/-- **Reduction (fp-S2h).** `ConeClosureGoodMeasureLawStep` (FirstPass/S2f.lean) from the two open parts. -/
theorem coneClosureGoodMeasureLawStep_of_parts (hpole : FrozenGreenDiscPole) (hc : ConeCertificateNullHullStep)
    (hl : ConeLeastSuperNullHullStep) : ConeClosureGoodMeasureLawStep :=
  coneClosureGoodMeasureLawStep_of_badNullHull hpole (coneBadNullHull_of_parts hc hl)

end MatedCRT
