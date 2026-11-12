import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.FirstPass.S4S6c.TraceInputs68

/-!
# Almost-sure inputs of the deterministic Harnack step

For a valid environment the following hold on one almost-sure event, for every mesh size `ε > 0`: the embedding `η`
is continuous, the mated-CRT map is locally finite, consecutive vertices are adjacent, adjacent vertices have
intersecting cells, and the killing domains `V(B_R) \ V(∂B_R)` have finitely many vertices.  These are the
qualitative hypotheses of the deterministic step (`greenKernel_le_inv_mul_of_ringEvents`) of Berestycki–Gwynne (2020),
Proposition 3.8.
-/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Metric

/-- **Qualitative almost-sure inputs of the Harnack step.** -/
theorem MatedCRTEnv.IsValid.ae_harnack_inputs {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧ ∀ ε : ℝ, 0 < ε →
      IsLocallyFiniteMult (S.mult ε ω) ∧ (∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0) ∧
      (∀ j k : ℤ, S.mult ε ω j k ≠ 0 → (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty) ∧
      ∀ R : ℝ, (interiorCellVertices ε (S.η ω) (ball (0 : ℂ) R)).Finite := by
  filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
    hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮),
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hap hp hlf hmeet
  refine ⟨hap.1, fun ε hε => ⟨hlf ε hε, fun k => S.mult_succ_ne_zero hε.le ω k, hmeet ε hε, fun R => ?_⟩⟩
  exact (TraceInputs68.cellVertices_finite_of_tendsto hε hp (Metric.isBounded_ball)).subset Set.sdiff_subset

end MatedCRT
