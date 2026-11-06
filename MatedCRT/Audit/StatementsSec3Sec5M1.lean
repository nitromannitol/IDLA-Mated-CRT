import MatedCRT.Audit.Refutations
import MatedCRT.Audit.CorrectedForms

/-! Checks of relations used in the partial Sections 3 and 5 audit. These do not certify source fidelity. -/

namespace MatedCRT.Audit.StatementsSec3Sec5M1

example {𝒮 : SpaceFillingSLEModel} (h : DiscreteHolderContinuityStmt 𝒮) :
    DiscreteHolderContinuityCorrectedStep 𝒮 :=
  CorrectedForms.discreteHolderContinuityCorrected_of_draft h

example (𝒮 : SpaceFillingSLEModel) (h : GeneralIDLALowerBoundRelaxedStep 𝒮) :
    GeneralIDLALowerBoundStmt 𝒮 :=
  generalIDLALowerBound_of_relaxed 𝒮 h

example {𝒮 : SpaceFillingSLEModel} (h : DiscretePotentialTightnessCorrectedStmt 𝒮) :
    CorrectedForms.DiscretePotentialTightnessOnOpenStmt 𝒮 :=
  CorrectedForms.discretePotentialTightnessOnOpen_of_corrected h

end MatedCRT.Audit.StatementsSec3Sec5M1
