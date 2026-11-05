import MatedCRT.Steps.Sec4.ObstacleSpecialization
import MatedCRT.Steps.Sec7.MassBoundOdometer
import MatedCRT.Steps.Sec7.CrudeUpperBound
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells

/-!
# Lemmas 7.2 (corrected), 7.3 and 7.4 from the corrected Lemma 4.4

The Draft Lemma 4.4 (`DiscreteLaplacianBoundStmt`) is false (ESCALATIONS E-c1-1;
`Audit.CorrectedForms.not_discreteLaplacianBoundStmt`). Lemmas 7.2 (above the cell scale, E-c3-2), 7.3 and 7.4 use
only its first conjunct, `Δ^ε w̃^ε_t = (deg^ε)⁻¹` on `Λ^ε_t` (eq:laplacian-of-uteps away from the origin), which the
corrected form `DiscreteLaplacianBoundCorrectedStmt` keeps verbatim. This file reroutes them through the corrected
form: `stoppedOdometerLaplacianStep_of_corrected` is the proof of `stoppedOdometerLaplacianStep_of_steps`
(MatedCRT/Steps/Sec7/OdometerBoundMass.lean) with the corrected Lemma 4.4 in place of the Draft; the three results then
follow from the step reductions of MatedCRT/Steps/Sec7. The same derivations are recorded by worker A in
MatedCRT/Audit/CorrectedForms.lean (namespace `MatedCRT.Audit.CorrectedForms`); these are the owned copies that the
assembly (MatedCRT/Assembly/Main.lean) uses.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

variable {𝒮 : SpaceFillingSLEModel}

/-- `StoppedOdometerLaplacianStep` (eq:laplacian-of-uteps away from the origin) from the **corrected** Lemma 4.4. Off
`B_ρ`'s interior vertices the least supersolution is the obstacle, so a vertex of `Λ^ε_t` is interior; there the Green
kernel term of `w̃^ε_t` is harmonic away from the origin and the corrected Lemma 4.4 gives `Δ^ε w̃^ε_t = (deg^ε)⁻¹`. -/
theorem stoppedOdometerLaplacianStep_of_corrected (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) : StoppedOdometerLaplacianStep 𝒮 := by
  have hstr := matedMapStructureStep_of_adjacentCellsMeet 𝒮 hcell
  have hgreen := greenKernelHarmonicStep_of_steps 𝒮 hstr
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [hstr γ hγ hγ2 Ω S hS, h44 γ hγ hγ2 ρ hρ hρ1 Ω S hS, hgreen γ hγ hγ2 ρ hρ hρ1 Ω S hS]
    with ω hω h4 hg
  intro ε t hε ht a ha ha0
  obtain ⟨hlf, -⟩ := hω ε hε
  have haΛ : a ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧
      matedObstacle (S.mult ε ω) ε (S.η ω) ρ t a < matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a := ha
  have haV : a ∈ ballInterior ε (S.η ω) ρ := by
    by_contra hV
    have haW : a ∈ cellVertices ε (S.η ω) (closedBall 0 ρ) := Sec7.cellVertices_mono ball_subset_closedBall haΛ.1
    have h1 := Sec7.matedLeastSupersolution_le_obstacle_of_not_mem_ballInterior (m := S.mult ε ω) hε ht haW hV
    linarith [haΛ.2]
  have hw : mLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a =
      ((mdeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹ := (h4 t ε ht hε).1 a ha
  have hgr : mLaplacian (S.mult ε ω) (greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0) a =
      0 := hg ε hε a haV ha0
  show mLaplacian (S.mult ε ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) a = ((mdeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹
  rw [Sec7.mLaplacian_stoppedOdometer hε ht hlf, hw, hgr, mul_zero, add_zero]

/-- **Lemma 7.2 (corrected, E-c3-2: `s ≥ ε^β`)** from Lemmas 2.16, 2.8 (cited) and the **corrected** Lemma 4.4. -/
theorem massBoundOdometerAboveScale_of_corrected (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) :
    MassBoundOdometerAboveScaleStmt 𝒮 :=
  massBoundOdometerAboveScale_of_inputs 𝒮 h216 h28
    (matedMapStructureStep_of_adjacentCellsMeet 𝒮 (adjacentCellsMeetAeStep 𝒮))
    (stoppedOdometerLaplacianStep_of_corrected h44 (adjacentCellsMeetAeStep 𝒮)) (adjacentCellsMeetAeStep 𝒮)

/-- **Lemma 7.3** from the **corrected** Lemma 4.4. -/
theorem odometerBoundMass_of_corrected (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) : OdometerBoundMassStmt 𝒮 :=
  odometerBoundMass_of_steps 𝒮 (matedMapStructureStep_of_adjacentCellsMeet 𝒮 (adjacentCellsMeetAeStep 𝒮))
    (stoppedOdometerLaplacianStep_of_corrected h44 (adjacentCellsMeetAeStep 𝒮))

/-- **Lemma 7.4** (the Λ-version of review-S (S4), E-c3-1) from the **corrected** Lemma 4.4 and the degree bound
(`DegreeBoundInput`, GMS19 Lemma 2.6). -/
theorem crudeUpperBound_of_corrected (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (hdeg : DegreeBoundInput 𝒮) :
    CrudeUpperBoundStmt 𝒮 :=
  crudeUpperBound_of_mapSteps 𝒮 (matedMapStructureStep_of_adjacentCellsMeet 𝒮 (adjacentCellsMeetAeStep 𝒮))
    (stoppedOdometerLaplacianStep_of_corrected h44 (adjacentCellsMeetAeStep 𝒮)) hdeg

end MatedCRT
