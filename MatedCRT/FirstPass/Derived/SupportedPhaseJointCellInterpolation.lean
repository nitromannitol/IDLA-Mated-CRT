import MatedCRT.FirstPass.Derived.CouplingJointCellInterpolation
import LatticeProb.LQG.CouplingSupportedPhaseEmbedding

/-! # Joint environment and interpolated walks with an independent phase -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- A supported absolutely continuous phase gives a joint environment and
interpolated cell walk on the product space. -/
theorem exists_prod_jointEnvironment_interpolatedCellWalk_of_supported_phase
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (x : Ω × ℝ → ℂ)
    (hx : Measurable x)
    (hQ : Q ≪ volume) (hsupport : ∀ᵐ c ∂Q, c ∈ Icc (0 : ℝ) ε) :
    ∃ (H : Ω × ℝ → CellConfig)
      (Z : Ω × ℝ → ReflectedGMS.Code.RawCode × Measure C(ℝ≥0, ℂ))
      (E : Ω × ℝ → ReflectedGMS.Code.EnvGeneral),
      Measurable Z ∧ Measurable E ∧
      (P.prod Q).map (fun p => ((E p).val, (Z p).2)) = (P.prod Q).map Z ∧
      ∀ᵐ p ∂P.prod Q,
        ∃ (h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1))
          (_hlf : IsLocallyFinite ε ⟨fun t => bm p.1 (t + p.2),
            (bm p.1).continuous.comp (by fun_prop)⟩),
          H p = shiftedAreaCellConfig h hε (p.2 / ε)
            (bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
              (fun t => (bm p.1 (t + p.2)).2)) ∧
          (H p).IsCellConfiguration ∧ (H p).LineConnected ∧
          (Z p).1 = (H p).code ∧ (Z p).1 ∈ goodCodes ∧ (E p).val = (Z p).1 ∧
          let M := bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
            (fun t => (bm p.1 (t + p.2)).2)
          let C := shiftedAreaCellConfig h hε (p.2 / ε) M
          (∀ a : ℤ, C.IsSRWLaw (shiftedEuclideanCellEquiv h hε (p.2 / ε) a)
            ((srwLaw M a).map (fun path n =>
              shiftedEuclideanCellEquiv h hε (p.2 / ε) (path n)))) ∧
          ∀ (R : Measure (ℕ → C.cells)),
            C.IsSRWLaw (shiftedEuclideanCellEquiv h hε (p.2 / ε)
              (vertexOf ε (fun t => η p.1 (t + p.2)) (x p))) R →
            (Z p).2 = R.map (fun path =>
              interpPathCM (vertexPoint ε (fun t => η p.1 (t + p.2))) m.coe_nonneg
                (fun n => (shiftedEuclideanCellEquiv h hε (p.2 / ε)).symm (path n))) := by
  apply exists_prod_jointEnvironment_interpolatedCellWalk_of_coupling D hγ hε m Q x hx
  exact ae_prod_shifted_cellularEmbedding_of_supported_phase D hε Q hQ hsupport

/-- The joint environment and interpolated cell walk for a uniform mesh phase. -/
theorem exists_prod_jointEnvironment_interpolatedCellWalk_uniformIco
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (x : Ω × ℝ → ℂ)
    (hx : Measurable x) :
    ∃ (H : Ω × ℝ → CellConfig)
      (Z : Ω × ℝ → ReflectedGMS.Code.RawCode × Measure C(ℝ≥0, ℂ))
      (E : Ω × ℝ → ReflectedGMS.Code.EnvGeneral),
      Measurable Z ∧ Measurable E ∧
      (P.prod (LatticeProb.uniformIco ε)).map (fun p => ((E p).val, (Z p).2)) =
        (P.prod (LatticeProb.uniformIco ε)).map Z ∧
      ∀ᵐ p ∂P.prod (LatticeProb.uniformIco ε),
        ∃ (h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1))
          (_hlf : IsLocallyFinite ε ⟨fun t => bm p.1 (t + p.2),
            (bm p.1).continuous.comp (by fun_prop)⟩),
          H p = shiftedAreaCellConfig h hε (p.2 / ε)
            (bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
              (fun t => (bm p.1 (t + p.2)).2)) ∧
          (H p).IsCellConfiguration ∧ (H p).LineConnected ∧
          (Z p).1 = (H p).code ∧ (Z p).1 ∈ goodCodes ∧ (E p).val = (Z p).1 ∧
          let M := bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
            (fun t => (bm p.1 (t + p.2)).2)
          let C := shiftedAreaCellConfig h hε (p.2 / ε) M
          (∀ a : ℤ, C.IsSRWLaw (shiftedEuclideanCellEquiv h hε (p.2 / ε) a)
            ((srwLaw M a).map (fun path n =>
              shiftedEuclideanCellEquiv h hε (p.2 / ε) (path n)))) ∧
          ∀ (R : Measure (ℕ → C.cells)),
            C.IsSRWLaw (shiftedEuclideanCellEquiv h hε (p.2 / ε)
              (vertexOf ε (fun t => η p.1 (t + p.2)) (x p))) R →
            (Z p).2 = R.map (fun path =>
              interpPathCM (vertexPoint ε (fun t => η p.1 (t + p.2))) m.coe_nonneg
                (fun n => (shiftedEuclideanCellEquiv h hε (p.2 / ε)).symm (path n))) := by
  let : IsProbabilityMeasure (LatticeProb.uniformIco ε) :=
    LatticeProb.isProbabilityMeasure_uniformIco hε
  apply exists_prod_jointEnvironment_interpolatedCellWalk_of_coupling
    D hγ hε m (LatticeProb.uniformIco ε) x hx
  exact ae_prod_shifted_cellularEmbedding_uniformIco D hε

end MatedCRT
end
