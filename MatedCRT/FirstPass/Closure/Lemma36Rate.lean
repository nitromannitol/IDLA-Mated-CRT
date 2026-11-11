import MatedCRT.FirstPass.S3i.LensClosed
import MatedCRT.FirstPass.SLERef.Certified

/-!
# Corrected Lemma 3.6: the same-walk rate conjunct, closed for a certified reference model

Corrected Lemma 3.6 (`paper/idla_mated_crt-corrected.tex`, label `lemma:convergence-of-harmonic-functions`, lines 1417-1441;
correction [C13], docs/campaign/CORRECTIONS.md) has two clauses. The first is the convergence clause
`CorrectedHarmonicConvergenceStmt 𝒮` (Draft/Section3HarmonicCorrected.lean:29). The second is its Moreover clause, the
fixed-start annealed same-walk comparison with threshold `q = bχ/2` (tex lines 1431-1441). That clause is the Lean statement
`MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮` (FirstPass/S3i/Statement.lean:39), which is used here as the
rate conjunct. The pointwise clause of the Draft statement `CorrectedHarmonicSameWalkRateStmt`
(Draft/Section3HarmonicCorrected.lean:68) is not used: it was retired by the operator as false (see the header of
FirstPass/S3i/Statement.lean).

Inputs: those of `closed_3_6_corrected` (Closure/Section3.lean), namely the projections of `hC : CertifiedReferenceModel ν 𝒮`
and the frozen `hexc : FrozenBrownianOutwardExcursionAtExit`, together with the one-sided boundary continuity estimate
`hBE : FrozenOneSidedBoundaryContinuity 𝒮` (FirstPass/S3i/Frozen.lean:44), a first-pass frozen cited input from Gwynne-Miller-Sheffield
(arXiv:1807.07511, Theorem 3.9, equation (3.31)). `hBE` is not a conjunct of `CertifiedReferenceModel`.

The proof is `MatedCRT.FirstPass36.firstPass_3_6_closed` (FirstPass/S3i/LensClosed.lean:31), applied to the projections of `hC`.
-/

open MeasureTheory

namespace MatedCRT

/-- Corrected Lemma 3.6, rate conjunct (the fixed-start annealed same-walk clause, tex lines 1431-1441), for a model with
certified reference model `hC`. -/
theorem closed_3_6_rate {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuity 𝒮) :
    MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  (MatedCRT.FirstPass36.firstPass_3_6_closed hC.randomWalkToLBM hC.cellSizeEstimate hC.mepsScaling hexc
    hC.frozenDiscreteHolderContinuityCorrected hBE).2

/-- Corrected Lemma 3.6, both clauses: the convergence clause `CorrectedHarmonicConvergenceStmt` (tex lines 1417-1430)
and the annealed same-walk rate clause `CorrectedHarmonicSameWalkAnnealedStmt` (tex lines 1431-1441), for a model with
certified reference model `hC`. The binders are those of `closed_3_6_rate`. -/
theorem closed_3_6_full {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuity 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  MatedCRT.FirstPass36.firstPass_3_6_closed hC.randomWalkToLBM hC.cellSizeEstimate hC.mepsScaling hexc
    hC.frozenDiscreteHolderContinuityCorrected hBE

end MatedCRT
