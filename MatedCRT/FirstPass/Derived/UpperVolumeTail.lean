import MatedCRT.FirstPass.Derived.LQGMeasureInputs
import MatedCRT.FirstPass.Frozen.S5S6S7
import LatticeProb.LQG.LQGBallMassUpperUniform

/-!
# The uniform upper volume tail of the whole-plane LQG measure

`WholePlaneUpperVolumeTailStep` (`FPWholePlaneUpperVolumeTail`; Rhodes-Vargas 2014, Theorem 2.6; Berestycki-Gwynne,
arXiv:2003.10320, eq. (A.2)): for the γ-LQG measure `μ` of a whole-plane GFF, `0 < γ < 2`, there are `β, q > 0` with
`P(∃ z ∈ B_3, μ(B_s(z)) > s^β) ≤ K s^q` for small `s`. It is the library theorem
`LatticeProb.Gauss.IsWholePlaneGFF.exists_ballMass_le_rpow_on_ball` at `R = 3`, through the definitional bridges
`LPBridge.isWholePlaneGFF_iff` and `LPBridge.isLQGMeasure_iff`. Only the upper tail of the ball masses is used.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory HarmonicBalls

/-- **Uniform upper volume tail of the whole-plane γ-LQG measure on `B_3`** (`WholePlaneUpperVolumeTailStep`) is a
theorem. -/
theorem wholePlaneUpperVolumeTailStep_holds : WholePlaneUpperVolumeTailStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hG hμ
  exact ((LPBridge.isWholePlaneGFF_iff P hC hcirc).1 hG).exists_ballMass_le_rpow_on_ball
    ((LPBridge.isLQGMeasure_iff P γ hcirc μ).1 hμ) hγ hγ2 3

/-- `FPWholePlaneUpperVolumeTail` (binder `hV`) is a theorem. -/
theorem fpWholePlaneUpperVolumeTail_holds : FPWholePlaneUpperVolumeTail :=
  wholePlaneUpperVolumeTailStep_holds

end MatedCRT.FirstPass.Derived
