import MatedCRT.FirstPass.S5e.KillSet
import MatedCRT.FirstPass.S5e.SecondGreenDet
import MatedCRT.FirstPass.S5e.SecondGreenStep

/-!
# FIRST PASS S5e: the stopped second Green inequality (correction [C21], second Green step (5.7))

This umbrella collects the result `MatedCRT.S5e.stoppedSecondGreenStep_of_inputs` (SecondGreenStep.lean), which reduces `StoppedSecondGreenStep`
(FirstPass/S5d/StoppedSteps.lean:73) to the named probabilistic inputs `StoppedFloorHalfStep` and `StoppedMassLowerStep`
(plus the Draft statements 2.8, 2.15, 2.16 and the pathwise inputs). The deterministic core is `secondGreen_pointwise`
(SecondGreenDet.lean). -/
