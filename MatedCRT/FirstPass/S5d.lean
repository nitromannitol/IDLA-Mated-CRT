import MatedCRT.Proofs.IDLA.JointDiscreteLowerBound
import MatedCRT.Proofs.Measurability.EnvSigma
import MatedCRT.Draft.Section5
import MatedCRT.Steps.Sec5.IDLALowerBound

/-!
# Proposition 5.1 (`firstPass_5_1`, task fp-S5d-5-1-stopped-repair)

`IDLALowerBoundStmt` (Draft/Section5.lean:27) is assembled from:
* the relaxed Lemma 5.2 (no origin or connectivity condition on the target; proved in the repository by
  `generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize` from Lemma 2.7 and Lemma 2.8);
* Lemma 5.3 (`MeanValueInequalityStmt`) and Lemma 5.4 (`LLowerBoundStmt`), Draft statements used as hypotheses;
* two NEW steps that are not yet proved (referee notes/fp-gaps/CHATGPT-5-1-gaps-referee.md):
  - `DiscreteClusterInnerBoundStep` (G1c: `B⁻_δ(Λ_t)` lies in the fill of the strict cluster `matedDiscreteCluster`;
    referee §3 and §4);
  - `IDLALowerBoundStoppedStep` (the stopped clause, walkers stopped upon exiting `V^ε(Λ_t)`; referee §5).

Hence `firstPass_5_1_of_steps` is a conditional reduction, not a `PROVED-FP` theorem.
-/

namespace MatedCRT

/-- **Proposition 5.1 from its two open steps.** The unstopped conjunct uses only `hI`; the stopped conjunct is `hstop`. -/
theorem firstPass_5_1_of_steps (𝒮 : SpaceFillingSLEModel) (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (h53 : MeanValueInequalityStmt 𝒮) (h54 : LLowerBoundStmt 𝒮)
    (hI : DiscreteClusterInnerBoundStep 𝒮) (hstop : IDLALowerBoundStoppedStep 𝒮) :
    IDLALowerBoundStmt 𝒮 :=
  iDLALowerBound_of_steps 𝒮 (generalIDLALowerBoundRelaxed_of_volumeGrowth_cellSize 𝒮 h27 h28) h53 h54 h28 hI hstop

end MatedCRT
