import MatedCRT.FirstPass.Derived.ProductShiftedGeneralEnvironmentLaw
import LatticeProb.LQG.CouplingSupportedPhaseEmbedding

/-! # General environment laws with an independent phase -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter Topology ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- Supported absolutely continuous phases give a general environment law and
selected walk marginal. -/
theorem exists_prod_shiftedAreaCellConfig_generalEnvironmentLaw_selectedWalkLaw_of_supported_phase
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (x : Ω × ℝ → ℂ)
    (hη : Measurable η) (hbm : Measurable bm) (hx : Measurable x)
    (hcurve : ∀ᵐ ω ∂P, Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      Function.Surjective (η ω))
    (hQ : Q ≪ volume) (hsupport : ∀ᵐ c ∂Q, c ∈ Icc (0 : ℝ) ε) :
    ∃ (H : Ω × ℝ → CellConfig)
      (Z : Ω × ℝ → ReflectedGMS.Code.RawCode × Measure C(ℝ≥0, ℂ))
      (ν : Measure ReflectedGMS.Code.EnvGeneral),
      Measurable Z ∧ IsProbabilityMeasure ν ∧
      ν.map Subtype.val = (P.prod Q).map (fun p => (Z p).1) ∧
      ∀ᵐ p ∂P.prod Q,
        (∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1),
          H p = shiftedAreaCellConfig h hε (p.2 / ε)
            (bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
              (fun t => (bm p.1 (t + p.2)).2)) ∧
          (H p).IsCellConfiguration ∧ (H p).LineConnected) ∧
        Z p = ((H p).code, shiftedSelectedWalkLaw ε m p.2 (x p) (η p.1) (bm p.1)) ∧
        (Z p).1 ∈ goodCodes := by
  apply exists_prod_shiftedAreaCellConfig_generalEnvironmentLaw_selectedWalkLaw
    D hγ hε m Q x hη hbm hx hcurve
  exact ae_prod_shifted_cellularEmbedding_of_supported_phase D hε Q hQ hsupport

/-- Uniform phases give a general environment law and selected walk marginal. -/
theorem exists_prod_shiftedAreaCellConfig_generalEnvironmentLaw_selectedWalkLaw_uniformIco
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (x : Ω × ℝ → ℂ)
    (hη : Measurable η) (hbm : Measurable bm) (hx : Measurable x)
    (hcurve : ∀ᵐ ω ∂P, Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      Function.Surjective (η ω)) :
    ∃ (H : Ω × ℝ → CellConfig)
      (Z : Ω × ℝ → ReflectedGMS.Code.RawCode × Measure C(ℝ≥0, ℂ))
      (ν : Measure ReflectedGMS.Code.EnvGeneral),
      Measurable Z ∧ IsProbabilityMeasure ν ∧
      ν.map Subtype.val = (P.prod (LatticeProb.uniformIco ε)).map (fun p => (Z p).1) ∧
      ∀ᵐ p ∂P.prod (LatticeProb.uniformIco ε),
        (∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1),
          H p = shiftedAreaCellConfig h hε (p.2 / ε)
            (bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
              (fun t => (bm p.1 (t + p.2)).2)) ∧
          (H p).IsCellConfiguration ∧ (H p).LineConnected) ∧
        Z p = ((H p).code, shiftedSelectedWalkLaw ε m p.2 (x p) (η p.1) (bm p.1)) ∧
        (Z p).1 ∈ goodCodes := by
  let : IsProbabilityMeasure (LatticeProb.uniformIco ε) :=
    LatticeProb.isProbabilityMeasure_uniformIco hε
  apply exists_prod_shiftedAreaCellConfig_generalEnvironmentLaw_selectedWalkLaw
    D hγ hε m (LatticeProb.uniformIco ε) x hη hbm hx hcurve
  exact ae_prod_shifted_cellularEmbedding_uniformIco D hε

end MatedCRT
end
