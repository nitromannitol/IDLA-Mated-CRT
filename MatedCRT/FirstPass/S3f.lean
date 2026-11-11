import MatedCRT.FirstPass.S3S4
import MatedCRT.Draft.Section3DirichletCorrected
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CorrectedPreparedCompactness
import MatedCRT.Steps.Sec2.BoundedExitTimeRV

/-!
# First pass: Lemma 3.7 with the corrected discrete Dirichlet input

`firstPass_3_7` (MatedCRT/FirstPass/S3S4.lean) takes the printed Lemma 3.5 `DiscreteDirichletProblemStmt`, which is
obsolete after the correction [C13] (boundary datum evaluated at the projected cell representative `π_D(η(b))`, Hölder
datum `φ` on the closed disk `cl(B_r(z))`). `firstPass_3_7_corrected` has the same conclusion and the same other
hypotheses; only the Dirichlet hypothesis is replaced by `DiscreteDirichletProblemCorrectedStmt`.

Proof: the corrected prepared route `convergenceNormalizedExitTime_of_corrected_prepared_estimates`
(MatedCRT/Proofs/Sec3/ConvergenceNormalizedExitTime/CorrectedPreparedCompactness.lean). Its interior step and boundary
estimates use only the corrected Dirichlet input; the printed `DiscreteDirichletProblemStmt` is not used there. Its
tightness input is the prepared corrected Lemma 3.1 (`discretePotentialTightnessPrepared_of_inputs`), built from the
same inputs `hm`, `BoundedExitTimeRVStmt` (Lemma 2.17 from Lemma 2.7) and `ExitTimeUpperBoundStmt` (Lemma 2.18), and
the corrected discrete Hölder estimate `FrozenDiscreteHolderContinuityCorrected`.
-/

namespace MatedCRT.FirstPass37

/-- **Lemma 3.7** (lemma:convergence-of-the-normalized-exit-time), with the corrected Lemma 3.5 hypothesis
`DiscreteDirichletProblemCorrectedStmt` in place of the printed `DiscreteDirichletProblemStmt` of `firstPass_3_7`.
Hypotheses: Lemma 2.7 (`VolumeGrowthStmt`), Lemma 2.18 (`ExitTimeUpperBoundStmt`), `MepsScalingInput` (External),
the frozen corrected Lemma 3.2 (`FrozenDiscreteHolderContinuityCorrected`), Lemma 3.3 (`UniformConvergenceGreenKernelStmt`)
and the corrected Lemma 3.5 (`DiscreteDirichletProblemCorrectedStmt`). Lemma 2.17 is `boundedExitTimeRV_of_steps`. -/
theorem firstPass_3_7_corrected {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hm : MepsScalingInput 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35c : DiscreteDirichletProblemCorrectedStmt 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 :=
  convergenceNormalizedExitTime_of_corrected_prepared_estimates 𝒮 hm h33 h35c
    (boundedExitTimeRV_of_steps h27) h218 h32

end MatedCRT.FirstPass37

#print axioms MatedCRT.FirstPass37.firstPass_3_7_corrected
