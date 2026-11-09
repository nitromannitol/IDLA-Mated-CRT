import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Proofs.Sec5.MeanValueInequality.CellRepresentative
import MatedCRT.FirstPass.S5c.CellFirstHit
import MatedCRT.FirstPass.Frozen.S5c

/-!
# FIRST PASS, Lemma 5.3: almost-sure cell facts of a valid mated-CRT environment (hmemcell and hx, a.s.)

For a valid environment `S` (`S.IsValid 𝒮 γ`), almost surely the curve `η(ω)` is area parametrized (surjective,
IsValid.isAreaParametrized) and proper (`Tendsto η (cocompact ℝ) (cocompact ℂ)`, `IsValid.ae_tendsto_cocompact`,
Proofs/Infra/MatingOfTrees.lean). Together with the frozen first-hit property `FPFirstHitVisits` (Frozen/S5c.lean):
* every point lies in the cell of its smallest vertex, for every mesh (`mem_cell_vertexOf_of_first_hit`, the hypothesis `hmemcell`
  of `core_subset_fillCells_eventually`);
* every vertex `a` has a cell point with smallest vertex `a` (`exists_vertexOf_eq_of_area_parametrized`, the hypothesis `hx` of
  `surplus_eventually_of_threshold`).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology

/-- **Almost-sure cell facts of a valid environment** (hmemcell and hx): see the module docstring. -/
theorem ae_cell_facts {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (hfirst : ∀ᵐ ω ∂S.P, ∀ x : ℂ, BddBelow {s : ℝ | S.η ω s = x}) :
    ∀ᵐ ω ∂S.P, (∀ ε : ℝ, 0 < ε → ∀ x : ℂ, x ∈ cell ε (S.η ω) (vertexOf ε (S.η ω) x)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ a : ℤ, ∃ x ∈ cell ε (S.η ω) a, vertexOf ε (S.η ω) x = a) := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact, hfirst] with ω hap hprop hf
  refine ⟨fun ε hε x => ?_, fun ε hε a => ?_⟩
  · exact mem_cell_vertexOf_of_first_hit hε hap.2.2.1 hf x
  · exact exists_vertexOf_eq_of_area_parametrized hap hprop hε a

end MatedCRT.S5c
