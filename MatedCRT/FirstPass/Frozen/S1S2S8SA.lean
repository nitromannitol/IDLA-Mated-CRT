import MatedCRT.Defs.Setting
import MatedCRT.Defs.Map

/-!
# First-pass frozen external inputs for IDLA paper Sections 1, 2, 8 and Appendix A

Each `def` below is an external input of the first-pass formalization (operator note 2026-11-09 16:40 UTC, "freeze ALL
the external inputs and focus on formalizing the NEW stuff"). A frozen `Prop` is used only as an explicit hypothesis of
a `firstPass_…` theorem in `MatedCRT/FirstPass/S1S2S8SA.lean`. Nothing here is proved.
-/

namespace MatedCRT

open MeasureTheory

/-- FIRST-PASS FROZEN. Almost surely, for every `ε > 0`, two vertices joined by an edge of the map of Definition 1.1
have intersecting cells `η([a - ε, a])`, `η([b - ε, b])`. Source: the mating-of-trees fact of Duplantier-Miller-Sheffield
(DMS14, Lemma 8.8 with the identification of Definitions 1.1 and 1.2, DMS14 Theorem 1.9); standard; locator pending.
Same statement as the Step `AdjacentCellsMeetAeStep` (Steps/Infra/MatingOfTrees.lean:30).
Used by: firstPass_2_13. -/
def FrozenAdjacentCellsMeetAe (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty

end MatedCRT
