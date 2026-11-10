import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity
import MatedCRT.Proofs.Sec7.CrudeUpperBound.PolyHighProb
import MatedCRT.Steps.Infra.MatingOfTrees
import MatedCRT.Draft.Section2
import MatedCRT.FirstPass.Frozen.S5BG56

/-!
# Section 5, first pass: from the canonical Berestycki–Gwynne Lemma 5.6 to the IDLA Lemma 2.15
(fp-S5-G2-canonical-and-2-7, z10)

* `greenInterior_le_greenCellVertices` (Armitage–Gardiner domain monotonicity of the killed Green function): the walk
  killed on the interior vertex set `V^ε(D) \ V^ε(∂D)` has no more visits than the walk killed on `V^ε(D)`, since it
  leaves the smaller set no later. Proved from the finite-domain first-step equations (`greenFn_mono_of_firstStep`).
* `greenFunctionCrudeBound_of_canonical`: `FrozenBG20GreenCrudeCanonical 𝒮` implies `GreenFunctionCrudeBoundStmt 𝒮`.

Volume growth (IDLA Lemma 2.7, `VolumeGrowthStmt`) is not re-proved here: an existing provider is
`volumeGrowthStmt_of_berestyckiGwynne` (MatedCRT/Proofs/Sec3/ConeBallMass.lean:17), whose input is
`BerestyckiGwynneConeBallMassStmt`, definitionally `FrozenBerestyckiGwynneConeBallMass` (FirstPass/Frozen/S5Cited.lean:35).
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter
open _root_.HarmonicBalls

/-- The cell vertices of a ball `B(x, r)` are finite, by properness of the curve `η` (Armitage–Gardiner: the killing
set is a finite domain). -/
theorem cellVertices_ball_finite_of_proper {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (x : ℂ) (r : ℝ) :
    (cellVertices ε η (ball x r)).Finite := by
  refine (cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall x r)).subset ?_
  intro k hk
  obtain ⟨z, hz, hzD⟩ := hk
  exact ⟨z, hz, ball_subset_closedBall hzD⟩

/-- Domain comparison of the crude Green bound: killing on the interior vertex set `V^ε(D) \ V^ε(∂D)` gives a Green
function at most the one killed on `V^ε(D)`. The same simple random walk is used; the walk killed on the smaller set
exits no later, so it makes no more visits to `b` (Armitage–Gardiner, domain monotonicity). -/
theorem greenInterior_le_greenCellVertices {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε : ℝ} (hε : 0 < ε) (ω : Ω) (hlf : IsLocallyFiniteMult (S.mult ε ω)) (D : Set ℂ)
    (hfin : (cellVertices ε (S.η ω) D).Finite) (a b : ℤ) :
    greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a b ≤
      greenFn (S.mult ε ω) (cellVertices ε (S.η ω) D) a b := by
  have hsub : interiorCellVertices ε (S.η ω) D ⊆ cellVertices ε (S.η ω) D := by
    unfold interiorCellVertices
    exact Set.sdiff_subset
  have hA : (interiorCellVertices ε (S.η ω) D).Finite := hfin.subset hsub
  have hcons : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := fun k => S.mult_succ_ne_zero hε.le ω k
  exact greenFn_mono_of_firstStep hlf hcons hA hsub
    (fun c => WalkPotential.mLaplacian_greenFn hlf hcons hA c)
    (fun c => WalkPotential.mLaplacian_greenFn hlf hcons hfin c) a b

/-- **Lemma 2.15 from the canonical BG20 form.** The frozen canonical Berestycki–Gwynne Lemma 5.6
(`FrozenBG20GreenCrudeCanonical 𝒮`, killing set `V^ε(B_ρ)`) gives the IDLA crude bound (killing set
`V^ε(B_ρ) \ V^ε(∂B_ρ)`) by domain monotonicity (`greenInterior_le_greenCellVertices`).
Extra input `hcell : AdjacentCellsMeetAeStep 𝒮` (MatedCRT/Steps/Infra/MatingOfTrees.lean:30): it gives, almost surely,
the local finiteness of the edge multiplicity needed for the finite-domain first-step equations, and the continuity and
properness of `η` (`IsValid.isAreaParametrized`, `IsValid.ae_tendsto_cocompact`). -/
theorem greenFunctionCrudeBound_of_canonical (𝒮 : SpaceFillingSLEModel)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮) :
    GreenFunctionCrudeBoundStmt 𝒮 := by
  intro γ hγ0 hγ2 ρ ζ hρ0 hρ1 hζ0 hζ1 Ω _ S hS
  have hC := hcanon γ hγ0 hγ2 ρ ζ hρ0 hρ1 hζ0 hζ1 Ω S hS
  have hq : ∀ᵐ ω ∂S.P, (Continuous (S.η ω) ∧ Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)) ∧
      ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω) := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      MatedCRTEnv.IsValid.ae_isLocallyFiniteMult hγ0 hγ2 hS hcell] with ω hap hp hlf
    exact ⟨⟨hap.1, hp⟩, hlf⟩
  refine polyHighProb_mono_ae hC hq ?_
  intro ε hε ω hω hqω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hfin := cellVertices_ball_finite_of_proper hqω.1.1 hqω.1.2 hε 0 ρ
  intro a ha b hb
  exact (greenInterior_le_greenCellVertices S hε ω (hqω.2 ε hε) (ball 0 ρ) hfin a b).trans (hω a ha b hb)

end MatedCRT
