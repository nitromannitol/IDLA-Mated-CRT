import MatedCRT.FirstPass.S4S6c.CountingExitAlpha68
import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.FirstPass.S4S6c.ShellTop68
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.FirstPass.S4S6c.LitConeLQG68
import MatedCRT.FirstPass.S5qe
import MatedCRT.FirstPass.Frozen.S4S5b
import MatedCRT.FirstPass.S6d
import MatedCRT.FirstPass.Frozen.S5Cited

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

/-! ### Named-field variants (q2, fp-S4S6c-cg-param, addendum items (i)-(iii); chat 246 Q4)

The three theorems below replace, in the Eps route only, (i) the certified core `hC : CertifiedReferenceModelCore ν 𝒮`
by its three used fields as separate binders `hG hE h28`; (ii) the inline `hμ` by the named Prop
`MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence` (S4S6c/LitConeLQG68.lean, PENDING TRUTH CHECK). The 6.8 variant also
(iii) discharges `h27 : VolumeGrowthStmt` through `volumeGrowthStmt_of_berestyckiGwynne` (Proofs/Sec3/ConeBallMass.lean:17)
from the named binder `hBG : BerestyckiGwynneConeBallMassStmt` (Proposed/BerestyckiGwynne.lean:23), as in
`FirstPass/Closure/Theorem14d.lean` (its `hBG`). The old theorems `closed_6_7/8/9_hU_eps` are kept unchanged. -/

/-- **Lemma 6.7 (faithful header), Eps route, named-field variant.** Binders: the Draft inputs `hG` (Lemma 2.16),
`h28` (Lemma 2.8) and `hE` (Lemma 2.18) as separate binders; `hLit hBM hCC` cited (60c); `hB1` certified; `hμ` named
(LitConeLQG68, pending truth check); `hOne` the Eps form (ShellHoneInst68.lean:233). Conclusion: `firstPass_6_7_faithful`. -/
theorem closed_6_7_hU_eps_fields {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeEpsStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (Lemma68ShellTop.hU_top_eps hG h28 hE hLit hBM hCC hB1 hμ hOne)

/-- **Lemma 6.8 (faithful header, localized form), Eps route, named-field variant.** Binders as `closed_6_7_hU_eps_fields`,
with `hBG : BerestyckiGwynneConeBallMassStmt` in place of `h27`: `h27` is `volumeGrowthStmt_of_berestyckiGwynne hBG`, and
the cell-size estimate of 6.8 is `h28`. Conclusion: `firstPass_6_8_faithful`. -/
theorem closed_6_8_hU_eps_fields {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : BerestyckiGwynneConeBallMassStmt)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeEpsStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (Lemma68ShellTop.hU_top_eps hG h28 hE hLit hBM hCC hB1 hμ hOne)
    (volumeGrowthStmt_of_berestyckiGwynne hBG) h28

/-- **Lemma 6.9 (faithful header), Eps route, named-field variant.** Binders as `closed_6_7_hU_eps_fields`.
Conclusion: `firstPass_6_9_faithful`. -/
theorem closed_6_9_hU_eps_fields {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeEpsStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (Lemma68ShellTop.hU_top_eps hG h28 hE hLit hBM hCC hB1 hμ hOne)

/-! ### CG route (q2, fp-S4S6c-cg-param): the Eps route at the Green constant `CG`, with `c₀ = exp(-2CG)/32`.

The binders are those of the named-field variants `closed_6_x_hU_eps_fields` (`hG h28 hE` separate; `hμ` named; `hBG` for
6.8), with `hOne : ShellOneTestOrderAeCGStmt 𝒮` (ShellHoneInst68.lean: the CG Eps form at `c₀(CG)`). The CG-free Eps
theorems above are kept unchanged. -/

/-- **Lemma 6.7 (faithful header), CG route.** Binders as `closed_6_7_hU_eps_fields`, with `hOne` the CG form. -/
theorem closed_6_7_hU_cg {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (Lemma68ShellTop.hU_top_cg hG h28 hE hLit hBM hCC hB1 hμ hOne)

/-- **Lemma 6.8 (faithful header, localized form), CG route.** As `closed_6_8_hU_eps_fields`, with `hOne` the CG form. -/
theorem closed_6_8_hU_cg {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (Lemma68ShellTop.hU_top_cg hG h28 hE hLit hBM hCC hB1 hμ hOne)
    (volumeGrowthStmt_of_berestyckiGwynne hBG) h28

/-- **Lemma 6.9 (faithful header), CG route.** Binders as `closed_6_7_hU_cg`. -/
theorem closed_6_9_hU_cg {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (Lemma68ShellTop.hU_top_cg hG h28 hE hLit hBM hCC hB1 hμ hOne)

/-- **Lemma 6.x, uniform constant-order lower bound (hU), CG route.** Binders as `closed_6_7_hU_cg`. -/
theorem closed_6_x_hU_cg {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68ShellTop.hU_top_cg hG h28 hE hLit hBM hCC hB1 hμ hOne

/-! ### CG mesh-radius route (q2, fp-S4S6c-meshEventR): the CG route with `meshEventR` (cell-size component at `(1+ρ)/2`).

Chat 252 §1: the mesh event is `meshEventR` (Guard68S10.lean), and the leaf input is `hOne : ShellOneTestOrderAeCGRStmt 𝒮`
(ShellHoneInst68.lean). The binders are those of the CG route, with `hBG : FrozenBerestyckiGwynneConeBallMass`
(Frozen/S5Cited.lean:35; definitionally `BerestyckiGwynneConeBallMassStmt`, TRUE by chat 249) in 6.8. The CG route above is kept. -/

/-- **Lemma 6.7 (faithful header), CG mesh-radius route.** Binders as `closed_6_7_hU_cg`, with `hOne` the `meshEventR` form. -/
theorem closed_6_7_hU_cgR {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (Lemma68ShellTop.hU_top_cgR hG h28 hE hLit hBM hCC hB1 hμ hOne)

/-- **Lemma 6.8 (faithful header, localized form), CG mesh-radius route.** As `closed_6_8_hU_cg`, with `hOne` the
`meshEventR` form and `hBG : FrozenBerestyckiGwynneConeBallMass`. -/
theorem closed_6_8_hU_cgR {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (Lemma68ShellTop.hU_top_cgR hG h28 hE hLit hBM hCC hB1 hμ hOne)
    (volumeGrowthStmt_of_berestyckiGwynne hBG) h28

/-- **Lemma 6.9 (faithful header), CG mesh-radius route.** Binders as `closed_6_7_hU_cgR`. -/
theorem closed_6_9_hU_cgR {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (Lemma68ShellTop.hU_top_cgR hG h28 hE hLit hBM hCC hB1 hμ hOne)

/-- **Lemma 6.x, uniform constant-order lower bound (hU), CG mesh-radius route.** Binders as `closed_6_7_hU_cgR`. -/
theorem closed_6_x_hU_cgR {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮) (hE : ExitTimeUpperBoundStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68ShellTop.hU_top_cgR hG h28 hE hLit hBM hCC hB1 hμ hOne

/-! ### Counting CG mesh-radius route (q2, fp-S4S6c-closed-cgrc): `ShellOneTestOrderAeCGRCStmt` (the counting event
`countingMeshEventR`) and `CountingAtExitAlphaStmt` (one exponent for the exit and counting events, Guard68S10.lean). The
exit-time input `hE` of the CG-R closures is not needed: the exit event at the counting exponent comes from `hK`. -/

/-- **Lemma 6.7 (faithful header), counting CG mesh-radius route.** Binders as `closed_6_7_hU_cgR`, with `hOne` the counting
form and `hK` the counting input of `CountingAtExitAlphaStmt`; `hE` is dropped. -/
theorem closed_6_7_hU_cgRC {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRCStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  firstPass_6_7_faithful 𝒮
    (Lemma68ShellTop.hU_top_cgRC hG h28 hK hLit hBM hCC hB1 hμ hOne)

/-- **Lemma 6.8 (faithful header, localized form), counting CG mesh-radius route.** As `closed_6_8_hU_cgR`, with `hOne` the
counting form and `hK` the counting input; `hBG : FrozenBerestyckiGwynneConeBallMass` as before. -/
theorem closed_6_8_hU_cgRC {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRCStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  firstPass_6_8_faithful 𝒮
    (Lemma68ShellTop.hU_top_cgRC hG h28 hK hLit hBM hCC hB1 hμ hOne)
    (volumeGrowthStmt_of_berestyckiGwynne hBG) h28

/-- **Lemma 6.9 (faithful header), counting CG mesh-radius route.** Binders as `closed_6_7_hU_cgRC`. -/
theorem closed_6_9_hU_cgRC {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRCStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  firstPass_6_9_faithful 𝒮
    (Lemma68ShellTop.hU_top_cgRC hG h28 hK hLit hBM hCC hB1 hμ hOne)

/-- **Lemma 6.x, uniform constant-order lower bound (hU), counting CG mesh-radius route.** Binders as `closed_6_7_hU_cgRC`. -/
theorem closed_6_x_hU_cgRC {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLowerBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hK : Lemma68Guard10.CountingAtExitAlphaStmt 𝒮)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRCStmt 𝒮) :
    UniformConstantOrderLowerBoundStmt 𝒮 :=
  Lemma68ShellTop.hU_top_cgRC hG h28 hK hLit hBM hCC hB1 hμ hOne

/-! ### First-pass forms from the certified reference model (q2, fp-S4S6c-closed-cgrc; lead li 17:45 UTC).
The Draft inputs `GreenKernelLowerBoundStmt 𝒮` (Lemma 2.16) and `CellSizeEstimateStmt 𝒮` (Lemma 2.8) are the projections
`CertifiedReferenceModel.greenKernelLowerBound` (SLERef/Certified.lean:131) and `CertifiedReferenceModel.cellSizeEstimate`
(SLERef/Certified.lean:100) of the certified reference model `hCRM` (a FIRST-PASS FROZEN bundle, Certified.lean:54). The counting
input `CountingAtExitAlphaStmt 𝒮` is `CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM` (CountingExitAlpha68.lean:152).
The only producer binder left is `hOne : ShellOneTestOrderAeCGRCStmt 𝒮` (ShellHoneInst68.lean:414). -/

/-- **Lemma 6.7, first-pass form of the counting CG route.** Binders: `hCRM`, the literature inputs `LitExistence`,
`LitWholePlaneBallMass`, `LitCoordChange`, `LitQuantumConeLQGMeasureExistence`, the frozen `FPConeWholePlaneFieldLaw`, and
the producer `hOne`. -/
theorem firstPass_6_7_of_hOne {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRCStmt 𝒮) :
    FaithfulConstantOrderLowerBoundStmt 𝒮 :=
  closed_6_7_hU_cgRC (CertifiedReferenceModel.greenKernelLowerBound hCRM)
    (CertifiedReferenceModel.cellSizeEstimate hCRM) hLit hBM hCC hB1 hμ
    (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM) hOne

/-- **Lemma 6.8, first-pass form of the counting CG route (localized).** As `firstPass_6_7_of_hOne`, with the frozen
`FrozenBerestyckiGwynneConeBallMass` input `hBG` (Frozen/S5Cited.lean:35). -/
theorem firstPass_6_8_of_hOne {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hBG : FrozenBerestyckiGwynneConeBallMass)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRCStmt 𝒮) :
    FaithfulConstantOrderLowerBoundDivStmt 𝒮 :=
  closed_6_8_hU_cgRC (CertifiedReferenceModel.greenKernelLowerBound hCRM)
    (CertifiedReferenceModel.cellSizeEstimate hCRM) hLit hBM hCC hB1 hμ hBG
    (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM) hOne

/-- **Lemma 6.9, first-pass form of the counting CG route.** Binders as `firstPass_6_7_of_hOne`. -/
theorem firstPass_6_9_of_hOne {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (hCRM : CertifiedReferenceModel ν 𝒮)
    (hLit : MatedCRT.S2VG.LitExistence) (hBM : MatedCRT.S2VG.LitWholePlaneBallMass)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hB1 : FPConeWholePlaneFieldLaw)
    (hμ : MatedCRT.S2VG.LitQuantumConeLQGMeasureExistence)
    (hOne : Lemma68ShellHoneInst.ShellOneTestOrderAeCGRCStmt 𝒮) :
    FaithfulChanceOfBeingAbsorbedStmt 𝒮 :=
  closed_6_9_hU_cgRC (CertifiedReferenceModel.greenKernelLowerBound hCRM)
    (CertifiedReferenceModel.cellSizeEstimate hCRM) hLit hBM hCC hB1 hμ
    (CountingExitAlpha68.countingAtExitAlphaStmt_of_firstPass hCRM) hOne

end MatedCRT

#print axioms MatedCRT.closed_6_x_hU_eps
#print axioms MatedCRT.closed_6_7_hU_eps_fields
#print axioms MatedCRT.closed_6_8_hU_eps_fields
#print axioms MatedCRT.closed_6_9_hU_eps_fields
#print axioms MatedCRT.closed_6_7_hU_eps
#print axioms MatedCRT.closed_6_8_hU_eps
#print axioms MatedCRT.closed_6_9_hU_eps

#print axioms MatedCRT.closed_6_x_hU_cg
#print axioms MatedCRT.closed_6_7_hU_cg
#print axioms MatedCRT.closed_6_8_hU_cg
#print axioms MatedCRT.closed_6_x_hU_cgR
#print axioms MatedCRT.closed_6_7_hU_cgR
#print axioms MatedCRT.closed_6_8_hU_cgR
#print axioms MatedCRT.closed_6_9_hU_cgR
#print axioms MatedCRT.closed_6_x_hU_cgRC
#print axioms MatedCRT.closed_6_7_hU_cgRC
#print axioms MatedCRT.closed_6_8_hU_cgRC
#print axioms MatedCRT.closed_6_9_hU_cgRC
#print axioms MatedCRT.firstPass_6_7_of_hOne
#print axioms MatedCRT.firstPass_6_8_of_hOne
#print axioms MatedCRT.firstPass_6_9_of_hOne
#print axioms MatedCRT.closed_6_9_hU_cg