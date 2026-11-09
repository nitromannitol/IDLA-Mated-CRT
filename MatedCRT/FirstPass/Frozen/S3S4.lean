import MatedCRT.Steps.Sec3.DiscretePotentialTightness

/-!
# First pass: frozen external inputs of Sections 3 and 4 (q2, task fp-S3S4)

Each `def` below is an EXTERNAL input of the first pass (general mathematics or a cited result of the paper), used as
an explicit hypothesis. Nothing here is a claim about this paper's clusters, odometers, harmonic balls or IDLA
processes beyond the cited statement itself.
-/

namespace MatedCRT

/-- FIRST-PASS FROZEN. Lemma 3.2 (lemma:discrete-holder-continuity, paper line 1018), corrected form, cited from
\cite{gwynne2019harmonic} Theorem 3.9 (bibliographic locator to be confirmed; the paper's citation is "Theorem 3.9").
The printed Draft `DiscreteHolderContinuityStmt` is FALSE (review-L32 F1, docs/campaign/CORRECTED-FORMS.md, entry 3.2);
this is the corrected statement `DiscreteHolderContinuityCorrectedStep` of Steps/Sec3/DiscretePotentialTightness.lean:71.
Used by: firstPass_3_1_corrected. -/
def FrozenDiscreteHolderContinuityCorrected (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteHolderContinuityCorrectedStep 𝒮

end MatedCRT
