import MatedCRT.FirstPass.Closure.Lemma36FlooredUniform

/-!
# Lemma 3.6 with the uniform floored boundary estimate in place of the one-sided boundary continuity

`closed_3_6_lp_uniform` has the conclusion of `closed_3_6_lp` (`MatedCRT/FirstPass/Closure/CleanSec23LP.lean`):
the convergence clause `CorrectedHarmonicConvergenceStmt 𝒮` and the annealed same-walk clause
`CorrectedHarmonicSameWalkAnnealedStmt 𝒮` of the corrected Lemma 3.6. Its binders are those of `closed_3_6_lp`
with the binder `hBE : FrozenOneSidedBoundaryContinuity 𝒮` replaced by the uniform floored boundary estimate
`hBE : FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮` (`MatedCRT/FirstPass/S3i/LensFloored.lean`).

The Brownian outward excursion binder `hexc` is discharged by `frozenBrownianOutwardExcursionAtExit_holds`
(`MatedCRT/FirstPass/LPBridge/BrownianOutwardExcursion.lean:113`), as in `closed_3_6_lp`. The proof is the
wrapper `closed_3_6_full_floored_uniform_bm` (`MatedCRT/FirstPass/Closure/Lemma36FlooredUniform.lean`).

The binders `_hm : MepsScalingInput 𝒮` and `_h32 : FrozenDiscreteHolderContinuityCorrected 𝒮` are kept with the types
of `closed_3_6_lp` (`hm`, `h32` there). The uniform route does not consume them: it reads the same two Props from the
certified reference model `hC` (`CertifiedReferenceModel.mepsScaling` and
`CertifiedReferenceModel.frozenDiscreteHolderContinuityCorrected`). The underscore marks them as unused.
-/

namespace MatedCRT
open MeasureTheory

open MatedCRT.FirstPass36 in
/-- Corrected Lemma 3.6 (harmonic convergence of the corrected discrete harmonic functions and the annealed
same-walk clause), with the one-sided boundary continuity taken in its uniform floored form
`FrozenOneSidedBoundaryContinuityFlooredUniform` and the Brownian outward excursion discharged by
`frozenBrownianOutwardExcursionAtExit_holds`. The statement is `closed_3_6_lp` with `hBE` replaced. -/
theorem closed_3_6_lp_uniform (𝒮 : SpaceFillingSLEModel) (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (_hm : MepsScalingInput 𝒮)
    (_h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBE : FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  closed_3_6_full_floored_uniform_bm ν hC hBE

end MatedCRT
