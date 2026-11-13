import MatedCRT.FirstPass.S5qe
import MatedCRT.FirstPass.Closure.Lemma36RateFloored

/-!
# Floored forms of the corrected Lemma 3.6

The declarations below state the corrected Lemma 3.6 under the floored boundary estimate
`hBEFl : FrozenOneSidedBoundaryContinuityFloored 𝒮` (S3i/FrozenFloored.lean) and the named hypothesis
`hLensFl : FrozenOneSidedBoundaryContinuityFloored 𝒮 → QuenchedLensStep 𝒮`, the floored quenched lens step. `hLensFl` is
NOT a paper result (its truth and the uniform floor exponent are PENDING TRUTH CHECK; see docs/campaign/FROZEN-PROVENANCE.md,
row 82). The quenched bounds `QuenchedBoundsOnGoodStmt` are not a binder here, because `hLensFl` takes the whole
quenched lens step as one input.

The good event `FP36GoodEnv` (S3i/LensDefs.lean:70) and `lensProb_le_of_BE_fp36` (S3i/LensBE.lean:24) use the per-`ω`
event `FP36OneSidedBEAt` (S3i/LensDefs.lean:54, :90); the floored good event is in S3i/LensFlooredGood.lean.
-/

open MeasureTheory

namespace MatedCRT.FirstPass36

open Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Corrected Lemma 3.6, annealed same-walk clause, under the floored boundary estimate.
The body is `annealed_3_6_of_quenchedLensStep` (Closure/Lemma36RateFloored.lean) applied to `hLensFl hBEFl`. -/
theorem firstPass_3_6_annealed_floored {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBEFl : FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : FrozenOneSidedBoundaryContinuityFloored 𝒮 → QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  annealed_3_6_of_quenchedLensStep h211 h28 hm hexc h32 (hLensFl hBEFl)

/-- Corrected Lemma 3.6, annealed clause, floored form. -/
theorem firstPass_3_6_annealed_closed_floored {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBEFl : FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : FrozenOneSidedBoundaryContinuityFloored 𝒮 → QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  firstPass_3_6_annealed_floored h211 h28 hm hexc h32 hBEFl hLensFl

/-- Corrected Lemma 3.6 (both clauses), floored form. -/
theorem firstPass_3_6_closed_floored {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBEFl : FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : FrozenOneSidedBoundaryContinuityFloored 𝒮 → QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  firstPass_3_6_annealed_closed_floored h211 h28 hm hexc h32 hBEFl hLensFl

end MatedCRT.FirstPass36

namespace MatedCRT.FirstPassClosure

/-- Floored core form of corrected Lemma 3.6, with the
certified reference model core `hC`. Same conclusion; `hBE` is replaced by `hBEFl` and `hLensFl` is added. -/
theorem closed_3_6_annealed_core_floored {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hBEFl : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFloored 𝒮 →
      MatedCRT.FirstPass36.QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  MatedCRT.FirstPass36.firstPass_3_6_closed_floored hC.randomWalkToLBM hC.cellSizeEstimate hC.mepsScaling hexc
    hC.frozenDiscreteHolderContinuityCorrected hBEFl hLensFl

end MatedCRT.FirstPassClosure

#print axioms MatedCRT.FirstPass36.firstPass_3_6_annealed_floored
#print axioms MatedCRT.FirstPass36.firstPass_3_6_annealed_closed_floored
#print axioms MatedCRT.FirstPass36.firstPass_3_6_closed_floored
#print axioms MatedCRT.FirstPassClosure.closed_3_6_annealed_core_floored
