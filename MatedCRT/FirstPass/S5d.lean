import MatedCRT.Proofs.IDLA.JointDiscreteLowerBound
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Draft.Section5
import MatedCRT.Steps.Sec5.IDLALowerBound
import MatedCRT.FirstPass.S5d.StoppedReduction
import MatedCRT.FirstPass.S5d.ClusterInner

/-!
# Proposition 5.1 (`firstPass_5_1`, task fp-S5d-5-1-stopped-repair)

`IDLALowerBoundStmt` (Draft/Section5.lean:27) is assembled from:
* the relaxed Lemma 5.2 (no origin or connectivity condition on the target; proved in the repository by
  `generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize` from Lemma 2.7 and Lemma 2.8);
* Lemma 5.3 (`MeanValueInequalityStmt`) and Lemma 5.4 (`LLowerBoundStmt`), Draft statements used as hypotheses;
* NEW steps that are not yet proved (referee notes/fp-gaps/CHATGPT-5-1-gaps-referee.md):
  - `StrictClusterCompactContainmentStep` (G1c, referee §3 eq. (3.1): `B⁻_s(Λ_t)` lies in the fill of the strict cluster
    `matedDiscreteCluster` w.h.p.; `S5d/ClusterInner.lean` gives `DiscreteClusterInnerBoundStep` from it and Lemma 2.8);
  - `StoppedFirstGreenStep`, `StoppedSecondGreenStep` (the two Green inequalities of the stopped clause, referee §5),
    from which `IDLALowerBoundStoppedStep` follows (`MatedCRT/FirstPass/S5d/StoppedReduction.lean`).

Hence `firstPass_5_1_of_steps` is a conditional reduction, not a `PROVED-FP` theorem.
-/

namespace MatedCRT

/-- **Proposition 5.1 from its open steps.** The unstopped conjunct uses only `hK` and `h28`; the stopped conjunct is
`iDLALowerBoundStopped_of_greenSteps` (killing set `V^ε(Λ_t) ∩ S^ε`, targets `V^ε(B⁻_δ(Λ_t)) ∪ {0}`), from the two
open Green steps `hG1`, `hG2` and the cone-family inputs `hfam`, `h24`. -/
theorem firstPass_5_1_of_steps (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h53 : MeanValueInequalityStmt 𝒮) (h54 : LLowerBoundStmt 𝒮)
    (hK : StrictClusterCompactContainmentStep 𝒮) (hfam : ConeFamilyAEMeasurableStep)
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt) (hG1 : StoppedFirstGreenStep 𝒮) (hG2 : StoppedSecondGreenStep 𝒮) :
    IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_of_steps 𝒮 (generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize 𝒮 h27 h28) h53 h54 h28
    (discreteClusterInnerBound_of_compactContainment 𝒮 h28 hK)
    (iDLALowerBoundStopped_of_greenSteps 𝒮 (generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize 𝒮 h27 h28)
      hfam h24 hG1 hG2)

end MatedCRT
