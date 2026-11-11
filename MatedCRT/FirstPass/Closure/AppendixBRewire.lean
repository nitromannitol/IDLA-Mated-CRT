import MatedCRT.Proofs.Sec3.KilledOccupation.OccupationClosureCone
import MatedCRT.FirstPass.LPBridge.GFFExistence
import MatedCRT.FirstPass.Frozen.S4S5b
import MatedCRT.FirstPass.S5qe

/-!
# The certified core without the occupation identity of Appendix B

Conjunct 9 of `CertifiedReferenceModelCore ν 𝒮` (`MatedCRT/FirstPass/S5qe.lean`) is
`FrozenLBMGreenOccupationRescaled 𝒮`, the occupation identity of the median-rescaled Liouville Brownian motion killed
on exiting a disc (Appendix B of the paper). This file derives it, so that it need not be assumed:

* `coneUnitDiskGFFLaw_of_fieldLaw`: eq:gff in circle-average form (`KilledOccupation.ConeUnitDiskGFFLaw`) follows from
  the field-level law identity `FPConeWholePlaneFieldLaw` on the unit disk (eq:gff for pairings and circle averages)
  and the existence of a whole-plane GFF (`GFFExistence.exists_harmonicBalls_isWholePlaneGFF`), by projection on the
  circle averages;
* `frozenLBMGreenOccupationRescaled_of_fieldLaw`: the occupation identity of Appendix B from `FPConeWholePlaneFieldLaw`
  and the occupation identity `hGFF` of the clock of the field `h^ℂ - γ log|·|`, `h^ℂ` a whole-plane GFF, with an
  independent planar Brownian motion (Garban, Rhodes and Vargas, *Liouville Brownian motion*; Berestycki, *Diffusion
  in planar Liouville quantum gravity*), in the form of `KilledOccupation.frozenLBMGreenOccupationRescaled_of_coneGFFLaw`;
* `CertifiedReferenceModelCoreNoOccupation ν 𝒮`: the sixteen other conjuncts of the certified core, in the same order;
* `CertifiedReferenceModelCoreNoOccupation.toCore_of_fieldLaw`: the certified core from its sixteen other conjuncts,
  `FPConeWholePlaneFieldLaw` and `hGFF`.

No new frozen statement: `CertifiedReferenceModelCoreNoOccupation` has fewer conjuncts than the core, and `hGFF` is the
binder of `KilledOccupation.frozenLBMGreenOccupationRescaled_of_coneGFFLaw`, unchanged.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open _root_.HarmonicBalls

namespace MatedCRT

open KilledOccupation

/-- **eq:gff in circle-average form from the field-level law identity.** If the restriction to the unit disk of the
γ-quantum cone has the law of the restriction of `h^ℂ - γ log|·|`, for every whole-plane GFF `h^ℂ`
(`FPConeWholePlaneFieldLaw`, pairings with test functions and circle averages), then for every valid environment the
circle averages of the cone on the unit disk have the law of those of `h^ℂ - γ log|·|` for some whole-plane GFF
`h^ℂ`. A whole-plane GFF exists (`GFFExistence.exists_harmonicBalls_isWholePlaneGFF`), and the circle averages are a
measurable coordinate of the restricted field. -/
theorem coneUnitDiskGFFLaw_of_fieldLaw (hFL : FPConeWholePlaneFieldLaw) : ConeUnitDiskGFFLaw := by
  intro 𝒮 γ hγ0 hγ2 Ω _ S hS
  obtain ⟨Ω', mΩ', P', hC', hc, hP', hgff⟩ := GFFExistence.exists_harmonicBalls_isWholePlaneGFF
  refine ⟨Ω', mΩ', P', hC', hc, hP', hgff, ?_⟩
  have h := hFL γ hγ0 hγ2 Ω S.P S.hC S.hcirc S.μ
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩ Ω' P' hC' hc hP' hgff
  exact h.comp measurable_snd

/-- The certified reference model core without its conjunct `FrozenLBMGreenOccupationRescaled 𝒮` (conjunct 9 of
`CertifiedReferenceModelCore`, `MatedCRT/FirstPass/S5qe.lean`). The sixteen other conjuncts are in the same order. -/
def CertifiedReferenceModelCoreNoOccupation (ν : ℝ → Measure SLEPathCode) (𝒮 : SpaceFillingSLEModel) : Prop :=
  HasNormalizedSLELaw 𝒮 ν ∧
  SLEModelClosureInput 𝒮 ∧
  MepsScalingInput 𝒮 ∧
  DegreeBoundInput 𝒮 ∧
  CellSizeEstimateStmt 𝒮 ∧
  CountingMeasureConvergenceStmt 𝒮 ∧
  DegreeMeasureConvergenceStmt 𝒮 ∧
  FrozenConeScalingLaw 𝒮 ∧
  HasReferenceEnvironments 𝒮 ∧
  RandomWalkToLBMStmt 𝒮 ∧
  GreenKernelUpperBoundStmt 𝒮 ∧
  GreenKernelLowerBoundStmt 𝒮 ∧
  ExitTimeUpperBoundStmt 𝒮 ∧
  FrozenDiscreteHolderContinuityCorrected 𝒮 ∧
  BG20Prop51 𝒮 ∧
  FPSimilarityTransferCorrected 𝒮

/-- The certified core gives its sixteen conjuncts other than the occupation identity of Appendix B. -/
theorem CertifiedReferenceModelCore.toNoOccupation {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (h : CertifiedReferenceModelCore ν 𝒮) : CertifiedReferenceModelCoreNoOccupation ν 𝒮 := by
  unfold CertifiedReferenceModelCore at h
  unfold CertifiedReferenceModelCoreNoOccupation
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- The certified core from its sixteen other conjuncts and the occupation identity of Appendix B. -/
theorem CertifiedReferenceModelCoreNoOccupation.toCore {ν : ℝ → Measure SLEPathCode} {𝒮 : SpaceFillingSLEModel}
    (h : CertifiedReferenceModelCoreNoOccupation ν 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮) :
    CertifiedReferenceModelCore ν 𝒮 := by
  unfold CertifiedReferenceModelCoreNoOccupation at h
  unfold CertifiedReferenceModelCore
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, hrevuz, h10, h11, h12, h13, h14, h15, h16, h17⟩

section FieldLaw

variable (hFL : FPConeWholePlaneFieldLaw)
  (hGFF : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (r : ℝ) (z y : ℂ), 0 < r →
    ball z r ⊆ ball 0 ρ → y ∈ ball z r →
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
    (hc : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' → HarmonicBalls.IsWholePlaneGFF P' hC' hc →
    ∀ n : ℕ → ℕ, StrictMono n → dyadicScale (n 0) < 1 - ρ →
    (∀ k : ℕ, clockAnnealedLaw P' (fun ω' => fieldCircleAverage γ (hc ω')) y
      {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) <
        clockGapFun γ (exitNN z r) (dyadicScale (n k)) (dyadicScale (n (k + 1))) x}
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) →
    ∀ C : Set (Set ℂ), C.Countable → (∀ A ∈ C, MeasurableSet A ∧ A ⊆ ball z r) →
      ∀ᵐ ω' ∂P', clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω' ∈
        occupationAgreementEvent
          (limClockOccupationMeasure γ (fun k => dyadicScale (n k)) z r (planarBrownianMotion y))
          (gmcGreenMeasure γ ρ ((1 + ρ) / 2) z y r) (ball z r) C)

include hFL hGFF

/-- **Occupation identity of the median-rescaled Liouville Brownian motion on the γ-quantum cone** (Appendix B of the
paper) from the field-level law identity eq:gff on the unit disk (`hFL`) and the occupation identity of the clock of
the field `h^ℂ - γ log|·|`, `h^ℂ` a whole-plane GFF, with an independent planar Brownian motion (`hGFF`, the binder of
`KilledOccupation.frozenLBMGreenOccupationRescaled_of_coneGFFLaw`). -/
theorem frozenLBMGreenOccupationRescaled_of_fieldLaw (𝒮 : SpaceFillingSLEModel) :
    FrozenLBMGreenOccupationRescaled 𝒮 :=
  frozenLBMGreenOccupationRescaled_of_coneGFFLaw 𝒮 (coneUnitDiskGFFLaw_of_fieldLaw hFL) hGFF

/-- The certified core from its sixteen conjuncts other than the occupation identity of Appendix B, the field-level
law identity eq:gff on the unit disk and the occupation identity of the clock of the whole-plane GFF with the
logarithmic singularity. -/
theorem CertifiedReferenceModelCoreNoOccupation.toCore_of_fieldLaw {ν : ℝ → Measure SLEPathCode}
    {𝒮 : SpaceFillingSLEModel} (h : CertifiedReferenceModelCoreNoOccupation ν 𝒮) :
    CertifiedReferenceModelCore ν 𝒮 :=
  h.toCore (frozenLBMGreenOccupationRescaled_of_fieldLaw hFL hGFF 𝒮)

end FieldLaw

end MatedCRT
