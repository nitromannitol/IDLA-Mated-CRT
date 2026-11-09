import MatedCRT.Defs.Setting

/-!
# FIRST PASS frozen inputs of Lemma 5.3 (q3): the first-hit property of the space-filling SLE

Frozen by the operator ruling of 2026-11-09 20:12 UTC (item (b)): freeze the first-hit property as an EXTERNAL SLE input.
It is a property of the whole-plane space-filling SLE, not of this paper's clusters or harmonic balls.
-/

namespace MatedCRT

/-- **FIRST-PASS FROZEN.** First-hit property of the whole-plane space-filling SLE (operator ruling 2026-11-09 20:12 UTC, item
(b); checked TRUE, including the quantifier order a.s. omega then for all x, notes/fp-gaps/CHATGPT-frozen-truth-2145.md). For `0 < γ < 2` and a valid mated-CRT
environment `S`, almost surely, for every `x ∈ ℂ` the set of times `s` at which the curve `η` visits `x` is bounded below. This
makes the smallest vertex `a^ε_x = sInf {a | x ∈ H^ε_a}` of paper line 637 well defined (Defs/Map.lean `vertexOf`).
Source: Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma 8.11, p. 144. Used by: firstPass_5_3 via `mem_cell_vertexOf_of_first_hit` (FirstPass/S5c/CellFirstHit.lean),
which gives the hypothesis `hmemcell` of `core_subset_fillCells_eventually` (FirstPass/S5c/CoverEventually.lean). -/
def FPFirstHitVisits (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ∀ x : ℂ, BddBelow {s : ℝ | S.η ω s = x}

end MatedCRT
