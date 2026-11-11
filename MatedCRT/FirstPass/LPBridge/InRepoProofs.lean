import MatedCRT.FirstPass.Frozen.S4S5b
import MatedCRT.FirstPass.Frozen.S4S6c
import MatedCRT.Proofs.Measurability.LQGMeasureField
import MatedCRT.Proofs.Sec4.Prop42Closure.LQGMeasureLocalityProof
import MatedCRT.FirstPass.LPBridge.LQGMeasureFieldMeasurableLP
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.FirstPass.LPBridge.PunctureConnected
import MatedCRT.FirstPass.LPBridge.FiniteMeasureStandardBorel
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import HarmonicBalls.Steps.Sec2.GreenFunctionBall
import MatedCRT.FirstPass.HBRewire

/-!
# In-repository proofs of two frozen inputs of the first pass

Two inputs of the (b) class of `docs/campaign/PHASE2-INVENTORY.md` are already proved inside the repository, so they
are discharged here rather than kept as hypotheses:

* `FrozenLQGMeasureFieldMeasurable` (FirstPass/Frozen/S4S6c.lean): the LQG measure agrees almost surely with a
  `σ(h)`-measurable random measure. Proved through the LatticeProb ambient theorem
  `LatticeProb.exists_measurable_version_of_lqgArea_ambient` (LatticeProb/Bonanno/LQGMetric/Field/
  LQGMeasureFieldMeasurableAmbient.lean), by the bridge `frozenLQGMeasureFieldMeasurable_viaLP`
  (FirstPass/LPBridge/LQGMeasureFieldMeasurableLP.lean).
* `FPLQGMeasureLocality` (FirstPass/Frozen/S4S5b.lean): the locality of the `γ`-LQG measure as a measurable functional of
  the restricted field (Duplantier-Sheffield 2011, Proposition 1.1, with local approximations). Its body is
  `LQGMeasureLocalityFunctionalStep` (Proofs/Sec4/Prop42Closure/LQGMeasureFunctional.lean), proved by
  `LQGMeasureLocalityFunctionalStep_proof` (Proofs/Sec4/Prop42Closure/LQGMeasureLocalityProof.lean).
-/

namespace MatedCRT

open MeasureTheory Filter

/-- The almost-sure `σ(h)`-measurability of the LQG measure in the field (`FrozenLQGMeasureFieldMeasurable`), from the
LatticeProb ambient theorem through the bridge `frozenLQGMeasureFieldMeasurable_viaLP`. -/
theorem frozenLQGMeasureFieldMeasurable_holds (𝒮 : SpaceFillingSLEModel) :
    FrozenLQGMeasureFieldMeasurable 𝒮 :=
  frozenLQGMeasureFieldMeasurable_viaLP 𝒮

/-- The locality of the `γ`-LQG measure as a measurable functional of the restricted field
(`FPLQGMeasureLocality`), from the repository proof of `LQGMeasureLocalityFunctionalStep`. -/
theorem fpLQGMeasureLocality_holds : FPLQGMeasureLocality :=
  LQGMeasureLocalityFunctionalStep_proof

/-- The frozen superharmonic minimum principle (`FrozenSuperharmonicMinimumPrinciple`), one-line bridge to the
repository theorem `frozenSuperharmonicMinimumPrinciple_holds` (FirstPass/LPBridge/MinimumPrinciples.lean). -/
theorem frozenSuperharmonicMinimumPrinciple_inRepo : FrozenSuperharmonicMinimumPrinciple :=
  frozenSuperharmonicMinimumPrinciple_holds

/-- The strong minimum principle (`FPStrongMinimumPrinciple`), one-line bridge to `fpStrongMinimumPrinciple_holds`
(FirstPass/LPBridge/MinimumPrinciples.lean). -/
theorem fpStrongMinimumPrinciple_inRepo : FPStrongMinimumPrinciple :=
  fpStrongMinimumPrinciple_holds

/-- The integral measurability input (`FrozenLQGTestIntegralMeasurable`), one-line bridge to
`frozenLQGTestIntegralMeasurable_holds` (FirstPass/LPBridge/LQGTestIntegralMeasurable.lean). -/
theorem frozenLQGTestIntegralMeasurable_inRepo : FrozenLQGTestIntegralMeasurable :=
  frozenLQGTestIntegralMeasurable_holds

/-- Connectedness of the punctured domain (`FrozenPunctureConnected`), one-line bridge to
`frozenPunctureConnected_holds` (FirstPass/LPBridge/PunctureConnected.lean). -/
theorem frozenPunctureConnected_inRepo : FrozenPunctureConnected :=
  frozenPunctureConnected_holds

/-- Standard Borel structure of the finite measures on the disk (`FrozenFiniteMeasureDiskStandardBorel`), one-line
bridge to `frozenFiniteMeasureDiskStandardBorel_holds` (FirstPass/LPBridge/FiniteMeasureStandardBorel.lean). -/
theorem frozenFiniteMeasureDiskStandardBorel_inRepo : FrozenFiniteMeasureDiskStandardBorel :=
  frozenFiniteMeasureDiskStandardBorel_holds

/-- The Harmonic-Balls Draft statement `HarmonicBalls.GreenFunctionBallStmt` (HarmonicBalls/Draft/Section2.lean:68),
one-line bridge to `HarmonicBalls.greenFunctionBall` (Harmonic-Balls-LQG HarmonicBalls/Steps/Sec2/GreenFunctionBall.lean:156). -/
theorem greenFunctionBall_inRepo : HarmonicBalls.GreenFunctionBallStmt :=
  HarmonicBalls.greenFunctionBall

/-- Universal measurability of analytic sets (`FrozenUniversalMeasurabilityOfAnalytic`), one-line bridge to
`frozenUniversalMeasurabilityOfAnalytic_holds` (FirstPass/LPBridge/UniversalMeasurability.lean:18). -/
theorem frozenUniversalMeasurabilityOfAnalytic_inRepo : FrozenUniversalMeasurabilityOfAnalytic :=
  frozenUniversalMeasurabilityOfAnalytic_holds

/-- The disc pole input (`FrozenGreenDiscPole`), one-line bridge to the Harmonic-Balls rewire
`MatedCRT.HBRewire.FrozenGreenDiscPole_of_hb` (FirstPass/HBRewire.lean:41). -/
theorem frozenGreenDiscPole_inRepo : FrozenGreenDiscPole :=
  HBRewire.FrozenGreenDiscPole_of_hb

end MatedCRT
