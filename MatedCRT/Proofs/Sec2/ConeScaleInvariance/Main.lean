import MatedCRT.Steps.Sec2.ConeScaleInvariance
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Main

/-!
# Lemma 2.6 from its inputs

The deterministic scaling step is proved (`coneHarmonicBallFamilyOnScalingStep`) and `ConeLQGScalingStep` is derived
from Fact 2.2 and `R_b > 0` (`coneLQGScalingStep_of_steps`).
-/

namespace MatedCRT

/-- **Lemma 2.6** from its inputs. -/
theorem coneScaleInvariance_of_inputs (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (hpos : ConeScaleRadiusPosStep) (hmeasb : ConeRescaledCircleAEMeasurableStep)
    (hfun : ConeHarmonicBallFunctionalStep) : ConeScaleInvarianceStmt :=
  coneScaleInvariance_of_steps hscale (coneLQGScalingStep_of_steps h22 hpos) hmeasb hfun
    coneHarmonicBallFamilyOnScalingStep

end MatedCRT
