import MatedCRT.FirstPass.S5qe
import MatedCRT.FirstPass.Closure.Lemma36RateFloored

/-!
# Floored consumers of the one-sided boundary estimate (audit R2 K1, part (e))

Audit R2, item K1 (`notes/fp-gaps/OPUS-AUDIT-R2.md:33-45`): `FrozenOneSidedBoundaryContinuity` (S3i/Frozen.lean:44)
is false as typed, since its boundary distance has no floor. Its floored form
`FrozenOneSidedBoundaryContinuityFloored` (S3i/FrozenFloored.lean) is pending truth check (MQ-li-7a).

The floored consumers below are the original declarations with the binder `hBE : FrozenOneSidedBoundaryContinuity 𝒮`
replaced by `hBEFl : FrozenOneSidedBoundaryContinuityFloored 𝒮`, and with the named hypothesis
`hLensFl : FrozenOneSidedBoundaryContinuityFloored 𝒮 → QuenchedLensStep 𝒮` added. `hLensFl` is the floored quenched
lens step. It is NOT a paper result (its truth and the uniform floor exponent are filed as MQ-li-9). The lemma `Lemma 7`
binder `hQB : QuenchedBoundsOnGoodStmt` of the original chain is not a binder here, because `hLensFl` takes the whole
quenched lens step as one input. Conclusions are unchanged.

Consumers not floored here, because the same conclusion cannot be kept:
* `fp36_good_core` (S3i/GoodEvent.lean:223) and `commonGood_fp36` (S3i/GoodEvent.lean:336). Their conclusion
  contains `FP36GoodEnv` (S3i/LensDefs.lean:70), whose last clause is the unfloored per-`ω` event
  `FP36OneSidedBEAt` (S3i/LensDefs.lean:54, :90). The floor `max (infDist ..) (ε ^ β)` gives no bound for interior
  vertices with `infDist < ε ^ β`, so the unfloored clause does not follow from the floored Prop.
* `quenchedLensStep_of_BE` (S3i/LensStep.lean:42). It is built from `commonGood_fp36`, so its floored analogue is
  `hLensFl` itself.

Also not floored here: `lensProb_le_of_BE_fp36` (S3i/LensBE.lean:24) and its users. They take the per-`ω` event
`FP36OneSidedBEAt`, not the Prop `FrozenOneSidedBoundaryContinuity`.
-/

open MeasureTheory

namespace MatedCRT.FirstPass36

open Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Corrected Lemma 3.6, annealed same-walk clause, floored form of `firstPass_3_6_annealed` (S3i/Proof.lean:262).
The body is `annealed_3_6_of_quenchedLensStep` (Closure/Lemma36RateFloored.lean) applied to `hLensFl hBEFl`. -/
theorem firstPass_3_6_annealed_floored {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBEFl : FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : FrozenOneSidedBoundaryContinuityFloored 𝒮 → QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  annealed_3_6_of_quenchedLensStep h211 h28 hm hexc h32 (hLensFl hBEFl)

/-- Floored form of `firstPass_3_6_annealed_closed` (S3i/LensStep.lean:60). -/
theorem firstPass_3_6_annealed_closed_floored {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBEFl : FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : FrozenOneSidedBoundaryContinuityFloored 𝒮 → QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  firstPass_3_6_annealed_floored h211 h28 hm hexc h32 hBEFl hLensFl

/-- Corrected Lemma 3.6 (both clauses), floored form of `firstPass_3_6_closed` (S3i/LensClosed.lean:31), the counted
row 3.6 of `docs/campaign/COUNTED.md`. Same conclusion as `firstPass_3_6_closed`. -/
theorem firstPass_3_6_closed_floored {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBEFl : FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : FrozenOneSidedBoundaryContinuityFloored 𝒮 → QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  firstPass_3_6_annealed_closed_floored h211 h28 hm hexc h32 hBEFl hLensFl

end MatedCRT.FirstPass36

namespace MatedCRT.FirstPassClosure

/-- Floored form of `closed_3_6_annealed_core` (FirstPass/S5qe.lean:121), the core form of corrected Lemma 3.6 with the
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
