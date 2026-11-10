import MatedCRT.FirstPass.S4S6c.ShellTop68
import MatedCRT.FirstPass.S5qe
import MatedCRT.FirstPass.Frozen.S4S5b
import MatedCRT.FirstPass.S6d

/-!
# Closed Lemmas 6.7, 6.8, 6.9 from the top assembly `hU_top` (q2, fp-S4S6c-closed-6x)

Each theorem is the faithful Section 6 header of `firstPass_6_x_faithful` (FirstPass/S6d.lean) applied to the uniform
input `hU_top` (ShellTop68.lean, f10d512). The model enters only through the core certified reference model
`hC : CertifiedReferenceModelCore ν 𝒮` (FirstPass/S5qe.lean:33, the seventeen conjuncts of `CertifiedReferenceModel`
other than `FrozenTruncatedQuenchedLawsFixedTime`), whose projections give the Draft inputs `hG` (`greenKernelLowerBound`),
`h28` (`cellSizeEstimate`, the cell-size estimate of 6.8) and `hE` (`exitTimeUpperBound`), as in `closed_6_10`
(FirstPass/Closure/Section6.lean:30).

Binder status (the same in the three theorems; a binder not used by a theorem is omitted there):
* `hC : CertifiedReferenceModelCore ν 𝒮`: certified (projections for `hG`, `hE`, `h28`).
* `hB1 : FPConeWholePlaneFieldLaw`: certified (S4S5b.lean:43, defeq `ConeWholePlaneFieldLawStep`).
* `hLit : LitExistence`, `hBM : LitWholePlaneBallMass`, `hCC : LitCoordChange`: cited, pending request 60c.
* `hμ`: quantum-cone LQG existence for every `γ ∈ (0,2)`: pending request 60b.
* `h27 : VolumeGrowthStmt` (6.8 only, Draft Section 2): named input.
* `hOne : ShellOneTestOrderAeStmt 𝒮` (B1, ShellHoneInst68.lean:158): named input, proof by q1 (B1Assembly68).
* Eps route (`closed_6_7_hU_eps`, `closed_6_8_hU_eps`, `closed_6_9_hU_eps`, `closed_6_x_hU_eps`; q2, fp-S4S6c-eps-closures):
  the same binders with `hOne : ShellOneTestOrderAeEpsStmt 𝒮` (ShellHoneInst68.lean:233: mesh threshold `ε ≤ shellEps0`,
  exponent antecedents, radius cutoff). B1 in the old form gives it by `shellOneTestOrderAeEpsStmt_of_old` (ShellHoneInst68).

Terminology: Armstrong-Kuusi-Mourrat (good annuli, shell order), Duplantier-Sheffield (quantum cone, LQG measure),
Berestycki-Powell (LQG measure), Armitage-Gardiner (balls, Green functions).
-/

open MeasureTheory Filter Topology Metric HarmonicBalls ProbabilityTheory Set
open scoped ENNReal

namespace MatedCRT

/-- **Lemma 6.7 (faithful header), closed from the top assembly.** Binders: `hC` certified (core), `hB1` certified,
`hLit hBM hCC` cited (60c), `hμ` pending (60b), `hOne` B1 (q1). Conclusion: `firstPass_6_7_faithful` (S6d.lean:160). -/
theorem closed_6_7_hU {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (Lemma68ShellTop.hU_top hC.greenKernelLowerBound hC.cellSizeEstimate hC.exitTimeUpperBound hLit hBM hCC hB1 hμ hOne)

/-- **Lemma 6.8 (faithful header, localized form), closed from the top assembly.** Binders: `hC` certified (core; its
`cellSizeEstimate` is the `h28` of 6.8), `hB1` certified, `hLit hBM hCC` cited (60c), `hμ` pending (60b), `h27`
`VolumeGrowthStmt` named, `hOne` B1 (q1). Conclusion: `firstPass_6_8_faithful` (S6d.lean:195). -/
theorem closed_6_8_hU {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (h27 : VolumeGrowthStmt)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (Lemma68ShellTop.hU_top hC.greenKernelLowerBound hC.cellSizeEstimate hC.exitTimeUpperBound hLit hBM hCC hB1 hμ hOne)
    h27 hC.cellSizeEstimate

/-- **Lemma 6.9 (faithful header), closed from the top assembly.** Binders: `hC` certified (core), `hB1` certified,
`hLit hBM hCC` cited (60c), `hμ` pending (60b), `hOne` B1 (q1). Conclusion: `firstPass_6_9_faithful` (S6d.lean:114). -/
theorem closed_6_9_hU {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (Lemma68ShellTop.hU_top hC.greenKernelLowerBound hC.cellSizeEstimate hC.exitTimeUpperBound hLit hBM hCC hB1 hμ hOne)

/-- **Lemma 6.x, uniform constant-order lower bound (hU), closed from the Eps top assembly (q2, fp-S4S6c-eps-chain).**
Binders as `closed_6_7_hU`, with `hOne` the Eps form `ShellOneTestOrderAeEpsStmt` (threshold `ε ≤ shellEps0`, exponents
`2ω₀β⁻ < α`, `2ω₀ < 2/(2+γ)² - ζ`, radius cutoff). Conclusion: `UniformConstantOrderLowerBoundStmt 𝒮` (the hU that
`firstPass_6_x_faithful` consumes). -/
theorem closed_6_x_hU_eps {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeEpsStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68ShellTop.hU_top_eps hC.greenKernelLowerBound hC.cellSizeEstimate hC.exitTimeUpperBound hLit hBM hCC hB1 hμ hOne

/-- **Lemma 6.7 (faithful header), Eps route, closed from the top assembly.** As `closed_6_7_hU` (same binders
`hC hLit hBM hCC hB1 hμ`), with `hOne` the Eps form `ShellOneTestOrderAeEpsStmt` (ShellHoneInst68.lean:233).
Conclusion: `firstPass_6_7_faithful` (S6d.lean:160) applied to `hU_top_eps` (ShellTop68.lean). -/
theorem closed_6_7_hU_eps {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeEpsStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (Lemma68ShellTop.hU_top_eps hC.greenKernelLowerBound hC.cellSizeEstimate hC.exitTimeUpperBound hLit hBM hCC hB1 hμ hOne)

/-- **Lemma 6.8 (faithful header, localized form), Eps route, closed from the top assembly.** As `closed_6_8_hU`
(same binders `hC hLit hBM hCC hB1 hμ h27`), with `hOne` the Eps form `ShellOneTestOrderAeEpsStmt`. Conclusion:
`firstPass_6_8_faithful` (S6d.lean:195) applied to `hU_top_eps`, `h27` and the cell-size estimate `hC.cellSizeEstimate`. -/
theorem closed_6_8_hU_eps {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (h27 : VolumeGrowthStmt)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeEpsStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (Lemma68ShellTop.hU_top_eps hC.greenKernelLowerBound hC.cellSizeEstimate hC.exitTimeUpperBound hLit hBM hCC hB1 hμ hOne)
    h27 hC.cellSizeEstimate

/-- **Lemma 6.9 (faithful header), Eps route, closed from the top assembly.** As `closed_6_9_hU` (same binders
`hC hLit hBM hCC hB1 hμ`), with `hOne` the Eps form `ShellOneTestOrderAeEpsStmt`. Conclusion:
`firstPass_6_9_faithful` (S6d.lean:114) applied to `hU_top_eps`. -/
theorem closed_6_9_hU_eps {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModelCore ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hcone : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hcone hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeEpsStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (Lemma68ShellTop.hU_top_eps hC.greenKernelLowerBound hC.cellSizeEstimate hC.exitTimeUpperBound hLit hBM hCC hB1 hμ hOne)

end MatedCRT

#print axioms MatedCRT.closed_6_x_hU_eps
#print axioms MatedCRT.closed_6_7_hU_eps
#print axioms MatedCRT.closed_6_8_hU_eps
#print axioms MatedCRT.closed_6_9_hU_eps
