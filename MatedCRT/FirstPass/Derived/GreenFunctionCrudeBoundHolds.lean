import MatedCRT.FirstPass.Derived.Counted
import MatedCRT.FirstPass.Derived.SegmentReachOfCoupling
import MatedCRT.FirstPass.Derived.DegreeBoundOfLemma25Tail
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd

/-!
# Lemma 2.15 (crude Green function bound) for every model

`greenFunctionCrudeBoundStmt_of_cellSize_of_degreeBound` derives the crude bound
`sup_{a,b ∈ V^ε(B_ρ)} G^ε(a,b) ≤ ε^{-ζ}` with polynomially high probability (Lemma 2.15, after
Berestycki-Gwynne Lemma 5.6) from the cell size estimate (Lemma 2.4) and the degree bound
(Gwynne-Miller-Sheffield Lemma 2.6). Both hold for every space-filling SLE model:
`FirstPass.Derived.cellSizeEstimateStmt_holds` and `degreeBoundInput_holds`. Hence the crude bound
is a theorem for every model, and the counted forms of Theorems 1.4 and 1.6 no longer need it as
an input.
-/

open MeasureTheory

namespace MatedCRT

/-- **Lemma 2.15 holds for every model.** -/
theorem greenFunctionCrudeBoundStmt_holds (𝒮 : SpaceFillingSLEModel) :
    GreenFunctionCrudeBoundStmt 𝒮 :=
  greenFunctionCrudeBoundStmt_of_cellSize_of_degreeBound
    (FirstPass.Derived.cellSizeEstimateStmt_holds 𝒮) (degreeBoundInput_holds 𝒮)

/-- The input `hG15 : FrozenGreenFunctionCrudeBound 𝒮` of the counted forms is a theorem. -/
theorem frozenGreenFunctionCrudeBound_holds (𝒮 : SpaceFillingSLEModel) :
    FrozenGreenFunctionCrudeBound 𝒮 :=
  greenFunctionCrudeBoundStmt_holds 𝒮

/-- The counted form `closed_1_4_lp_noSC_noSup_derivedInputs` of Theorem 1.4 with
`hG15 : FrozenGreenFunctionCrudeBound 𝒮` supplied by `frozenGreenFunctionCrudeBound_holds`.
Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_4_lp_noSC_noSup_derivedInputs_crude
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_lp_noSC_noSup_derivedInputs ν hcore hscale hEnvS
    (frozenGreenFunctionCrudeBound_holds 𝒮)

/-- The counted form `closed_1_6_lp_noSC_noSup_derivedInputs` of Theorem 1.6 with
`hG15 : FrozenGreenFunctionCrudeBound 𝒮` supplied by `frozenGreenFunctionCrudeBound_holds`.
Same conclusion; the remaining binders are copied unchanged. -/
theorem closed_1_6_lp_noSC_noSup_derivedInputs_crude
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hcore : CertifiedReferenceModelCore ν 𝒮)
    (hscale : QuantumConeScalingInput)
    (hEnvS : ConeEnvironmentScalingUnderSLE 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_lp_noSC_noSup_derivedInputs ν hcore hscale hEnvS
    (frozenGreenFunctionCrudeBound_holds 𝒮)

end MatedCRT
