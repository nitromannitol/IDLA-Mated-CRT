import MatedCRT.FirstPass.S4S6c.ShellHoneInst68
import MatedCRT.FirstPass.S4S6c.ShellChainCore68
import MatedCRT.FirstPass.S6r.ShortWindowHV

/-!
# The top assembly of hU (q2, fp-S4S6c-guard-and-core)

`hU_top` proves `UniformConstantOrderLowerBoundStmt 𝒮` (FirstPass/S6d.lean:96) by composing:
* the prevalence input `hprev := ShortWindowHV.hprev_of_shortWindow_noH0V` (S6r/ShortWindowHV.lean, commit 8352cf0),
  whose binders are kept as explicit hypotheses: `hLit` (`LitExistence`), `hBM` (`LitWholePlaneBallMass`),
  `hCC` (`LitCoordChange`), `hB1` (`ConeWholePlaneFieldLawStep`), `hμ` (quantum-cone LQG existence);
* the shell core `hcore := Lemma68ShellHoneInst.shellChainCoreStmt_of_oneTestOrder hOne`, where the one-test
  order input `hOne : ShellOneTestOrderAeStmt 𝒮` (B1, ShellHoneInst68.lean:158) is kept as ONE named hypothesis;
* the Draft inputs `hG hC hE` of `uniformConstantOrderLowerBound_of_chain` (through `hU_of_core`, ShellChainCore68.lean).

This file is new (q2) because ShellHoneInst68 imports ShellChainCore68 and ShellChainCore68 must not import the S6r tree.
Terminology: Armstrong-Kuusi-Mourrat (good annuli, prevalence), Duplantier-Sheffield (LQG measure, coordinate change).
-/

open MeasureTheory Filter Topology Metric HarmonicBalls ProbabilityTheory Set
open scoped ENNReal

namespace MatedCRT
namespace Lemma68ShellTop

/-- **hU from the Draft inputs, the window prevalence (z1) and the one-test order input (B1).** The binders are the
exact remaining inputs: `hG hC hE` (Draft), `hLit hBM hCC hB1 hμ` (the literature and cone steps of
`hprev_of_shortWindow_noH0V`), and `hOne` (B1, `ShellOneTestOrderAeStmt`). -/
theorem hU_top {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : MatedCRT.ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68ChainCore.hU_of_core hG hC hE
    (ShortWindowHV.hprev_of_shortWindow_noH0V hLit hBM hCC hB1 hμ)
    (Lemma68ShellHoneInst.shellChainCoreStmt_of_oneTestOrder hOne)

/-- **hU from the Draft inputs, the window prevalence (z1) and the Eps one-test order input (q2, fp-S4S6c-eps-chain).**
As `hU_top`, with `hOne : ShellOneTestOrderAeEpsStmt 𝒮` (the mesh threshold, the exponent antecedents and the radius cutoff). -/
theorem hU_top_eps {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : MatedCRT.ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeEpsStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68ChainCore.hU_of_core_eps hG hC hE
    (ShortWindowHV.hprev_of_shortWindow_noH0V hLit hBM hCC hB1 hμ)
    (Lemma68ShellHoneInst.shellChainCoreEpsStmt_of_oneTestOrderEps hOne)

/-- **hU from the Draft inputs, the window prevalence (z1) and the CG Eps one-test order input (q2, fp-S4S6c-cg-param).**
As `hU_top_eps`, with `hOne : ShellOneTestOrderAeCGStmt 𝒮` (the ball ratio `c₀(CG)`, the threshold `shellEps0ZCG` and the
sparsity `shellS1CG γ CG`). -/
theorem hU_top_cg {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : MatedCRT.ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68ChainCore.hU_of_core_cg hG hC hE
    (ShortWindowHV.hprev_of_shortWindow_noH0V hLit hBM hCC hB1 hμ)
    (Lemma68ShellHoneInst.shellChainCoreCGStmt_of_oneTestOrderCG hOne)

/-- **hU from the Draft inputs, the window prevalence (z1) and the CG mesh-radius one-test order input (q2,
fp-S4S6c-meshEventR).** As `hU_top_cg`, with the mesh-radius leaf input `hOne : ShellOneTestOrderAeCGRStmt 𝒮` (cell-size
component at `(1 + ρ)/2`, mesh clause `meshEventR`). -/
theorem hU_top_cgR {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : MatedCRT.ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68ChainCore.hU_of_core_cgR hG hC hE
    (ShortWindowHV.hprev_of_shortWindow_noH0V hLit hBM hCC hB1 hμ)
    (Lemma68ShellHoneInst.shellChainCoreCGRStmt_of_oneTestOrderCGR hOne)

/-- **`UniformConstantOrderLowerBoundStmt` (hU) from the counting CG one-test order input (q2, fp-S4S6c-closed-cgrc).** As
`hU_top_cgR`, with the counting form `ShellOneTestOrderAeCGRCStmt` (`hOne`) and the counting input `CountingAtExitAlphaStmt`
(`hK`) in place of the exit-time input `ExitTimeUpperBoundStmt`. -/
theorem hU_top_cgRC {𝒮 : SpaceFillingSLEModel} (hG : GreenKernelLowerBoundStmt 𝒮) (hC : CellSizeEstimateStmt 𝒮)
    (hK : MatedCRT.Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : MatedCRT.ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRCStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68ChainCore.hU_of_core_cgRC hG hC hK
    (ShortWindowHV.hprev_of_shortWindow_noH0V hLit hBM hCC hB1 hμ)
    (Lemma68ShellHoneInst.shellChainCoreCGRCStmt_of_oneTestOrderCGRC hOne)

end Lemma68ShellTop
end MatedCRT

#print axioms MatedCRT.Lemma68ShellTop.hU_top
#print axioms MatedCRT.Lemma68ShellTop.hU_top_cgR
#print axioms MatedCRT.Lemma68ShellTop.hU_top_cgRC
#print axioms MatedCRT.Lemma68ShellTop.hU_top_eps
