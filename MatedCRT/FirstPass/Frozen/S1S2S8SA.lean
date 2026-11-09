import MatedCRT.Defs.Setting
import MatedCRT.Defs.Map

/-!
# First-pass frozen external inputs for IDLA paper Sections 1, 2, 8 and Appendix A

Each `def` below is an external input of the first-pass formalization (operator note 2026-11-09 16:40 UTC, "freeze ALL
the external inputs and focus on formalizing the NEW stuff"). A frozen `Prop` is used only as an explicit hypothesis of
a `firstPass_…` theorem in `MatedCRT/FirstPass/S1S2S8SA.lean`. Nothing here is proved.
-/

namespace MatedCRT

open MeasureTheory HarmonicBalls

/-- FIRST-PASS FROZEN. Almost surely, for every `ε > 0`, two vertices joined by an edge of the map of Definition 1.1
have intersecting cells `η([a - ε, a])`, `η([b - ε, b])`. Source: the mating-of-trees fact of Duplantier-Miller-Sheffield
(DMS14, Lemma 8.8 with the identification of Definitions 1.1 and 1.2, DMS14 Theorem 1.9); standard; locator pending.
Same statement as the Step `AdjacentCellsMeetAeStep` (Steps/Infra/MatingOfTrees.lean:30).
Used by: firstPass_2_13. -/
def FrozenAdjacentCellsMeetAe (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty

/-- FIRST-PASS FROZEN. Harmonic balls depend locally on the field: for each `γ ∈ (0, 2)` there is a measurable functional
`Φ` such that, for every continuous circle average process `c` with LQG limit `ν` and every family `Λ` of harmonic
balls of `ν` (Theorem 2.3 properties), the global family process of `Λ` is `Φ` applied to the circle process of `c`.
Source: HB22 = [bou2022harmonic], Proposition 1.3 (locality of harmonic balls), cited at the paper's line 542 (proof of
Lemma 2.4) and used in the proof of Lemma 2.6; locator pending. Same statement as the Step
`ConeHarmonicBallFunctionalStep` (Steps/Sec2/ConeScaleInvariance.lean:27).
RETIRED (NOT-EXTERNAL, truth check 2026-11-09): the all-time locality of harmonic balls with a measurable functional `Φ`
asserts more than any printed HB22 result, so it is not an admissible hypothesis. Kept, not deleted. Former use:
firstPass_2_6 (no longer FirstPass-admissible; to be re-proved from the HB Draft statements and ConeFamilyAEMeasurableStep). -/
def FrozenConeHarmonicBallFunctional : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ Φ : (Set.Ioi (0 : ℝ) × ℂ → ℝ) → ℝ × ℂ → Prop,
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ → AEMeasurable Φ (P.map fun ω => circleProcess (hcirc ω))) ∧
    ∀ c : ℝ → ℂ → ℝ, ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) → ∀ ν : Measure ℂ,
      IsLQGLimit γ c ν → ∀ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamily ν Λ → globalFamilyProcess Λ = Φ (circleProcess c)

end MatedCRT
