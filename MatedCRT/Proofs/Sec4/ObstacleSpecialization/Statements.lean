import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Escape

/-!
# Section 4: Lemmas 4.3-4.5 from `AdjacentCellsMeetAeStep` alone (ESCALATIONS E-c1-1, E-c1-2)

Almost surely, for all `ε > 0`, the mated-CRT map of Definition 1.1 has the deterministic properties
`IsRegularMatedMap` (`ae_isRegularMatedMap`): `η` is continuous (`IsValid.isAreaParametrized`) and proper
(`IsValid.ae_tendsto_cocompact`), the edge multiplicity is symmetric and loopless with `εk ∼ ε(k+1)`
(`MatedCRTEnv.mult_symm`, `mult_self`, `mult_succ_ne_zero`), and adjacent cells meet (`AdjacentCellsMeetAeStep`).
Lemmas 4.3-4.5 then follow from the fixed-scale results of MatedCRT/Proofs/Sec4/ObstacleSpecialization/Escape.lean,
which apply Appendix A to the connected component of the origin in `V^ε(B_ρ) \ V^ε(∂B_ρ)`. Neither
`BallInteriorConnectedStep` nor `MatedObstacleSettingStep` is used; the Green's function identities are the proved
`greenKernelLaplacianStep` and `normExitTimeLaplacianStep`.
-/

namespace MatedCRT

open MeasureTheory

/-- Almost surely, for all `ε > 0`, the mated-CRT map at scale `ε` satisfies `IsRegularMatedMap`. -/
theorem ae_isRegularMatedMap {𝒮 : SpaceFillingSLEModel} (hcell : AdjacentCellsMeetAeStep 𝒮) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → IsRegularMatedMap (S.mult ε ω) ε (S.η ω) := by
  filter_upwards [hS.ae_tendsto_cocompact, hS.isAreaParametrized, hcell γ hγ hγ2 Ω S hS] with ω hp hη hmeet
  intro ε hε
  exact ⟨hη.1, hp, hε, S.mult_symm ε ω, S.mult_self ε ω, fun k => S.mult_succ_ne_zero hε.le ω k, hmeet ε hε⟩

/-- **Lemma 4.3** (lemma:discrete-basic-properties, line 1679), from `AdjacentCellsMeetAeStep` only. -/
theorem discreteBasicProperties_of_escape {𝒮 : SpaceFillingSLEModel} (hcell : AdjacentCellsMeetAeStep 𝒮) :
    DiscreteBasicPropertiesStmt 𝒮 := by
  intro γ hγ hγ2 ρ _ _ Ω _ S hS
  filter_upwards [ae_isRegularMatedMap hcell hγ hγ2 hS] with ω hd
  intro t ε ht hε
  exact matedBasicProperties_of_regular (hd ε hε) ht

/-- **Lemma 4.4** (lemma:discrete-laplacian-bound, line 1697), corrected (E-c1-1: the origin claim needs
`0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`), from `AdjacentCellsMeetAeStep` only. -/
theorem discreteLaplacianBoundCorrected_of_escape {𝒮 : SpaceFillingSLEModel} (hcell : AdjacentCellsMeetAeStep 𝒮) :
    DiscreteLaplacianBoundCorrectedStmt 𝒮 := by
  intro γ hγ hγ2 ρ _ _ Ω _ S hS
  filter_upwards [ae_isRegularMatedMap hcell hγ hγ2 hS] with ω hd
  intro t ε ht hε
  exact matedLaplacianBound_of_regular (hd ε hε) ht

/-- **Lemma 4.5** (lemma:discrete-conservation-of-mass, line 1705), corrected (E-c1-1: the mass identity needs
`0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`), from `AdjacentCellsMeetAeStep` only. -/
theorem discreteConservationOfMassCorrected_of_escape {𝒮 : SpaceFillingSLEModel}
    (hcell : AdjacentCellsMeetAeStep 𝒮) : DiscreteConservationOfMassCorrectedStmt 𝒮 := by
  intro γ hγ hγ2 ρ _ _ Ω _ S hS
  filter_upwards [ae_isRegularMatedMap hcell hγ hγ2 hS] with ω hd
  intro t ε ht hε
  exact matedConservationOfMass_of_regular (hd ε hε) ht

end MatedCRT
