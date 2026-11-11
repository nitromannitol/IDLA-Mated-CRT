import MatedCRT.FirstPass.Closure.Lemma36RateFloored
import MatedCRT.FirstPass.S3i.LensFlooredStep

/-!
# Corrected Lemma 3.6 from the uniform floored boundary estimate (no lens-step hypothesis)

The four floored closed forms of Closure/Lemma36RateFloored.lean (`closed_3_6_rate_floored`, `closed_3_6_full_floored`,
and their `_bm` wrappers) take the named hypothesis `hLensFl : FrozenOneSidedBoundaryContinuityFloored 𝒮 → QuenchedLensStep 𝒮`.
Here the boundary input is the uniform floored form `FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮`
(S3i/LensFloored.lean), from which the floored form follows (`frozenOneSidedBoundaryContinuityFloored_of_uniform`) and the
quenched lens step is derived (`quenchedLensStep_of_flooredUniform`, S3i/LensFlooredStep.lean), with the cell-size and
scaling inputs of the certified reference model `hC`. No lens-step hypothesis remains.
-/

open MeasureTheory

namespace MatedCRT

/-- Corrected Lemma 3.6, rate conjunct, from the uniform floored boundary estimate (`closed_3_6_rate_floored` with
`hLensFl` derived). -/
theorem closed_3_6_rate_floored_uniform {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮) :
    MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  closed_3_6_rate_floored (𝒮 := 𝒮) (ν := ν) (hC := hC) (hexc := hexc)
    (hBE := MatedCRT.FirstPass36.frozenOneSidedBoundaryContinuityFloored_of_uniform hBE)
    (hLensFl := fun _ => MatedCRT.FirstPass36.quenchedLensStep_of_flooredUniform hC.cellSizeEstimate hC.mepsScaling hBE)

/-- Corrected Lemma 3.6, both clauses, from the uniform floored boundary estimate (`closed_3_6_full_floored` with
`hLensFl` derived). -/
theorem closed_3_6_full_floored_uniform {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  closed_3_6_full_floored (𝒮 := 𝒮) (ν := ν) (hC := hC) (hexc := hexc)
    (hBE := MatedCRT.FirstPass36.frozenOneSidedBoundaryContinuityFloored_of_uniform hBE)
    (hLensFl := fun _ => MatedCRT.FirstPass36.quenchedLensStep_of_flooredUniform hC.cellSizeEstimate hC.mepsScaling hBE)

/-- Wrapper of `closed_3_6_rate_floored_uniform`: the Brownian exit binder is discharged by
`MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (as in `closed_3_6_rate_floored_bm`). -/
theorem closed_3_6_rate_floored_uniform_bm {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮) :
    MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  closed_3_6_rate_floored_uniform (𝒮 := 𝒮) (ν := ν) (hC := hC) (hexc := frozenBrownianOutwardExcursionAtExit_holds)
    (hBE := hBE)

/-- Wrapper of `closed_3_6_full_floored_uniform`: the Brownian exit binder is discharged by
`MatedCRT.frozenBrownianOutwardExcursionAtExit_holds`. -/
theorem closed_3_6_full_floored_uniform_bm {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFlooredUniform 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  closed_3_6_full_floored_uniform (𝒮 := 𝒮) (ν := ν) (hC := hC) (hexc := frozenBrownianOutwardExcursionAtExit_holds)
    (hBE := hBE)

end MatedCRT

#print axioms MatedCRT.closed_3_6_rate_floored_uniform
#print axioms MatedCRT.closed_3_6_full_floored_uniform
#print axioms MatedCRT.closed_3_6_rate_floored_uniform_bm
#print axioms MatedCRT.closed_3_6_full_floored_uniform_bm
