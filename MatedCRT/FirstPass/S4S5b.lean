import MatedCRT.FirstPass.Frozen.S4S5b
import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section4
import MatedCRT.Draft.Section5

/-!
# FIRST PASS, strict obstacle gap and Proposition 4.2 / Lemmas 5.1, 5.3 of arXiv:2211.04891 (corrected draft)

* `firstPass_strictObstacleGap`: the strict obstacle gap `HarmonicBallStrictObstacleGapStep` (eq:strictly-above-in-interior,
  corrected.tex 1913-1925) from the frozen cone and whole-plane inputs (`Frozen/S4S5b.lean`) and cited harmonic-ball
  statements of the other paper (`ClusterOpenLaplacianStmt`, `VeryGoodAnnulusHarnackTypeStmt`,
  `TypicalPointManyGoodScalesStmt`, `LQGVolumeGrowthAllScalesStmt`).
-/

namespace MatedCRT

open MeasureTheory _root_.HarmonicBalls

/-- **Strict obstacle gap** (eq:strictly-above-in-interior, corrected.tex 1913-1925): for `t > 0`, almost surely on
`{t < T}`, the harmonic ball `Λ_t` lies in the unregularized obstacle cluster `HarmonicBalls.cluster (μ) ρ 0 t`.
Proof: the Cameron-Martin route of (countably many regularization defects; a local shift removes a
fixed time), through the conditional assembly `harmonicBallStrictObstacleGapStep_of_restrictedLaw_and_pairingLaws`
(Proofs/Sec4/DivSandpileLowerBound/StrictGapConeAssembly.lean:15), whose restricted-law input is derived from the field
law and the locality functional by `coneWholePlaneRestrictedLQGLawStep_of_inputs`. -/
theorem firstPass_strictObstacleGap (𝒮 : SpaceFillingSLEModel)
    (h32 : ClusterOpenLaplacianStmt.{0}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0}) (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (h27 : VolumeGrowthStmt) (hmodel : FPWholePlaneLQGModel) (hFL : FPConeWholePlaneFieldLaw)
    (hLoc : FPLQGMeasureLocality) (hpair : FPPairingLawIG4) :
    HarmonicBallStrictObstacleGapStep 𝒮 :=
  harmonicBallStrictObstacleGapStep_of_restrictedLaw_and_pairingLaws 𝒮 h32 h611 h82 hI2 h27 hmodel
    (coneWholePlaneRestrictedLQGLawStep_of_inputs hFL hLoc) hpair

end MatedCRT
