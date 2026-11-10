import MatedCRT.FirstPass.S2i.BorelFactor
import MatedCRT.FirstPass.S2i.CircleCode
import MatedCRT.FirstPass.S2i.FamilyCode
import MatedCRT.FirstPass.S2i.StoppedHorizon
import MatedCRT.FirstPass.S2i.ProcessCode
import MatedCRT.FirstPass.S2i.GraphFactor
import MatedCRT.FirstPass.S2i.CanonicalFactor
import MatedCRT.FirstPass.S2i.ContinuousDecoder
import MatedCRT.FirstPass.S2i.GlobalFactor

/-! # FirstPass S2i (z2): canonical cone factorization and the global family factor (fp-S2i-cone-canonical-global-factor)

Aggregates the modules of MatedCRT/FirstPass/S2i/. coneCanonicalFactor_proved (S2i/CanonicalFactor.lean) proves ConeCanonicalFactorStep (FirstPass/S2g/Canonical.lean); coneGlobalFamilyFactor_proved (S2i/GlobalFactor.lean) proves ConeGlobalFamilyFactorStep (FirstPass/S2g/ScaleInvariance.lean). Externals: FirstPass/Frozen/S2i.lean. -/
