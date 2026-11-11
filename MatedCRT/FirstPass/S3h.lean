import MatedCRT.FirstPass.S3e
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.SameWalkAssemblyAe

/-! # First-pass corrected Lemma 3.6, almost-everywhere same-walk rate (FirstPass S3h; closure gap G4)

Corrected Lemma 3.6 (`paper/idla_mated_crt-corrected.tex`, [C13]) is the Draft conjunction `CorrectedLemma36Stmt 𝒮 =
CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkRateStmt 𝒮` (`Draft/Section3HarmonicCorrected.lean`). The
pointwise clause `∀ ω ∈ E ε` of `CorrectedHarmonicSameWalkRateStmt` is false as typed (a null modification of the model changes the pointwise block). The
repaired statement is `CorrectedHarmonicSameWalkRateAeStmt 𝒮`, with the quenched block under `∀ᵐ ω ∂S.P, ω ∈ E ε → …`
(defined in `Proofs/Sec3/ConvergenceHarmonicFunctions/SameWalkRatesAe.lean`, namespace `MatedCRT`, same text as §1; it is
used here under its own name, `MatedCRT.CorrectedHarmonicSameWalkRateAeStmt`, to avoid a duplicate definition).

* The convergence conjunct is `FirstPass36.firstPass_3_6_convergence` (`FirstPass/S3e.lean`) on the printed Draft Lemma 3.2
  (`DiscreteHolderContinuityStmt`, FALSE; kept), or `FirstPass36.firstPass_3_6_convergence_corrected` on the corrected
  `FrozenDiscreteHolderContinuityCorrected` (used by `firstPass_3_6_corrected_ae_corrected`). Other inputs: Draft Lemmas 2.11,
  2.8, External `MepsScalingInput`, FIRST-PASS FROZEN `FrozenBrownianOutwardExcursionAtExit`. No new hypothesis.
* The a.e. same-walk conjunct is `correctedHarmonicSameWalkRateAe_of_cellTarget`
  (`Proofs/…/SameWalkAssemblyAe.lean`). Its two inputs are NAMED STEPS, not Draft statements, and have no Lean provider:
  `CellSizeTargetAeStmt 𝒮` (the uniform-exponent cell-size event, see its docstring) and `UniformSameWalkAeCoreStep 𝒮`
  (the core input: the pointwise a.e. rates, which contain the deterministic same-walk exit geometry of §2 of the answer).
  The Draft Lemma 2.8 (`CellSizeEstimateStmt`, Draft/Section2.lean:131) gives `PolyHighProb`, whose exponent `p` and
  constant `C` depend on the environment `S`, while the statement quantifies `κ` before `Ω S`; so it does not supply
  `CellSizeTargetAeStmt`. -/

namespace MatedCRT.FirstPass36Ae

open MatedCRT

/-- **Corrected Lemma 3.6, a.e. same-walk clause, conditional packaging (FirstPass S3h).** CONDITIONAL on the two named
steps `CellSizeTargetAeStmt 𝒮` and `UniformSameWalkAeCoreStep 𝒮` (not closed). -/
theorem firstPass_3_6_sameWalkRateAe {𝒮 : SpaceFillingSLEModel} (hcell : CellSizeTargetAeStmt 𝒮)
    (hcore : UniformSameWalkAeCoreStep 𝒮) : MatedCRT.CorrectedHarmonicSameWalkRateAeStmt 𝒮 :=
  MatedCRT.correctedHarmonicSameWalkRateAe_of_cellTarget 𝒮 hcore hcell

/-- **Corrected Lemma 3.6 (a.e. form), conditional packaging (FirstPass S3h; NOT a closure of G4).** The convergence
conjunct is proved from the inputs of `FirstPass36.firstPass_3_6_convergence`; the same-walk conjunct is
`firstPass_3_6_sameWalkRateAe`, conditional on the two named steps. RESTS ON THE PRINTED 3.2 (`DiscreteHolderContinuityStmt`),
FALSE (docs/campaign/CORRECTED-FORMS.md, row 3.2): use `firstPass_3_6_corrected_ae_corrected`. Kept unchanged. -/
theorem firstPass_3_6_corrected_ae {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : DiscreteHolderContinuityStmt 𝒮) (hcell : CellSizeTargetAeStmt 𝒮)
    (hcore : UniformSameWalkAeCoreStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ MatedCRT.CorrectedHarmonicSameWalkRateAeStmt 𝒮 :=
  ⟨MatedCRT.FirstPass36.firstPass_3_6_convergence h211 h28 hm hexc h32, firstPass_3_6_sameWalkRateAe hcell hcore⟩

/-- **Corrected Lemma 3.6 (a.e. form) on the corrected Lemma 3.2 (FirstPass S3h; NOT a closure
of G4).** Same statement and named steps as `firstPass_3_6_corrected_ae`, with the Hölder hypothesis `h32` the corrected
`FrozenDiscreteHolderContinuityCorrected 𝒮` (`FirstPass/Frozen/S3S4.lean`) in place of the printed `DiscreteHolderContinuityStmt`.
The convergence conjunct is `FirstPass36.firstPass_3_6_convergence_corrected` (`FirstPass/S3e.lean`); the same-walk
conjunct is `firstPass_3_6_sameWalkRateAe`, conditional on the named steps `hcell` (`CellSizeTargetAeStmt`) and `hcore`
(`UniformSameWalkAeCoreStep`). -/
theorem firstPass_3_6_corrected_ae_corrected {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcell : CellSizeTargetAeStmt 𝒮)
    (hcore : UniformSameWalkAeCoreStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ MatedCRT.CorrectedHarmonicSameWalkRateAeStmt 𝒮 :=
  ⟨MatedCRT.FirstPass36.firstPass_3_6_convergence_corrected h211 h28 hm hexc h32, firstPass_3_6_sameWalkRateAe hcell hcore⟩

end MatedCRT.FirstPass36Ae

#print axioms MatedCRT.FirstPass36Ae.firstPass_3_6_corrected_ae_corrected
#print axioms MatedCRT.FirstPass36Ae.firstPass_3_6_corrected_ae
