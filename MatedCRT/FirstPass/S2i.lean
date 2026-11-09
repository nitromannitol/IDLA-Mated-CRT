import MatedCRT.FirstPass.S2i.BorelFactor
import MatedCRT.FirstPass.S2i.CircleCode
import MatedCRT.FirstPass.S2i.FamilyCode
import MatedCRT.FirstPass.S2i.StoppedHorizon
import MatedCRT.FirstPass.S2i.ProcessCode
import MatedCRT.FirstPass.S2i.GraphFactor
import MatedCRT.FirstPass.S2i.CanonicalFactor

/-! # FirstPass S2i (z2): canonical cone factorization (fp-S2i-cone-canonical-global-factor)

Aggregates the modules of `MatedCRT/FirstPass/S2i/`. `coneCanonicalFactor_proved` (`S2i/CanonicalFactor.lean`) proves
`ConeCanonicalFactorStep` (`FirstPass/S2g/Canonical.lean`) from `ConeCanonicalHalfBallStep`, `ConeHalfBallClosureInsideStep`,
`VolumeGrowthStmt` and the frozen externals `ConeCircleLawUniqueStep`, `ConeReferenceExistsStep` (`FirstPass/Frozen/S2i.lean`). -/
