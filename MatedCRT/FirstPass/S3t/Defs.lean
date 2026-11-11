import HarmonicBalls.Defs.LBM

/-!
# Truncated quenched laws: deterministic definitions

Shared definitions for the derivation of `truncatedQuenchedLawsFixedTime_of_inputs` (namespace
`MatedCRT.TruncatedLaws`). This file is the common
base: the other `S3t` modules import it.
-/

open MeasureTheory Set
open scoped ENNReal NNReal
open _root_.HarmonicBalls

namespace MatedCRT.TruncatedLaws

/-- Occupation of the path `w` in the disk `D` up to the truncation time `T`, Duplantier–Sheffield style:
`∫_{(0, min (T, τ_D(w))]} g(w_t) dt`, where `τ_D` is the exit time `pathExitTime D` of `HarmonicBalls.Defs.LBM`.
This is the deterministic path functional `stoppedOccupation D T g` of the truncated-laws answer (section 3). -/
noncomputable def stoppedOccupation (D : Set ℂ) (T : ℝ) (g : ℂ → ℝ) (w : ℝ≥0 → ℂ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) (min (ENNReal.ofReal T) (pathExitTime D w)).toReal, g (w t.toNNReal)

end MatedCRT.TruncatedLaws
