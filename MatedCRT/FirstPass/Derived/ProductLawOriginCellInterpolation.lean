import MatedCRT.FirstPass.Derived.SupportedPhaseOriginCellInterpolation

/-! # Origin cell walks under a product-law realization -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- A measurable realization of the coupling and phase with their product law
inherits the joint origin-cell walk event and its environment-walk law. -/
theorem exists_jointEnvironment_originCellWalk_of_product_law
    {γ : ℝ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {R : Measure Ξ}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q ≪ volume) (hsupport : ∀ᵐ c ∂Q, c ∈ Icc (0 : ℝ) ε)
    (S : Ξ → Ω) (T : Ξ → ℝ) (hS : Measurable S) (hT : Measurable T)
    (hlaw : R.map (fun ξ => (S ξ, T ξ)) = P.prod Q) :
    ∃ (H : Ξ → CellConfig)
      (Z : Ξ → ReflectedGMS.Code.RawCode × Measure C(ℝ≥0, ℂ))
      (E : Ξ → ReflectedGMS.Code.EnvGeneral),
      Measurable Z ∧ Measurable E ∧
      R.map (fun p => ((E p).val, (Z p).2)) = R.map Z ∧
      (∃ Z₀ : Ω × ℝ → ReflectedGMS.Code.RawCode × Measure C(ℝ≥0, ℂ),
        Measurable Z₀ ∧ (∀ ξ, Z ξ = Z₀ (S ξ, T ξ)) ∧
        R.map Z = (P.prod Q).map Z₀) ∧
      ∀ᵐ p ∂(R),
        ∃ (h : IsAreaParametrized ((cellModelOfCoupling D hγ).area (S p)) (η (S p)))
          (_hlf : IsLocallyFinite ε ⟨fun t => bm (S p) (t + (T p)),
            (bm (S p)).continuous.comp (by fun_prop)⟩),
          H p = shiftedAreaCellConfig h hε ((T p) / ε)
            (bmEdgeCount ε (fun t => (bm (S p) (t + (T p))).1)
              (fun t => (bm (S p) (t + (T p))).2)) ∧
          (H p).IsCellConfiguration ∧ (H p).LineConnected ∧
          (Z p).1 = (H p).code ∧ (Z p).1 ∈ goodCodes ∧ (E p).val = (Z p).1 ∧
          vertexOf ε (fun t => η (S p) (t + (T p))) 0 = 0 ∧
          let M := bmEdgeCount ε (fun t => (bm (S p) (t + (T p))).1)
            (fun t => (bm (S p) (t + (T p))).2)
          let C := shiftedAreaCellConfig h hε ((T p) / ε) M
          (∀ a : ℤ, C.IsSRWLaw (shiftedEuclideanCellEquiv h hε ((T p) / ε) a)
            ((srwLaw M a).map (fun path n =>
              shiftedEuclideanCellEquiv h hε ((T p) / ε) (path n)))) ∧
          ∀ (R : Measure (ℕ → C.cells)),
            C.IsSRWLaw (shiftedEuclideanCellEquiv h hε ((T p) / ε)
              0) R →
            (Z p).2 = R.map (fun path =>
              interpPathCM (vertexPoint ε (fun t => η (S p) (t + (T p)))) m.coe_nonneg
                (fun n => (shiftedEuclideanCellEquiv h hε ((T p) / ε)).symm (path n))) := by
  obtain ⟨H₀, Z₀, E₀, hZ₀, hE₀, _, hevent⟩ :=
    exists_prod_jointEnvironment_originCellWalk_of_supported_phase D hγ hε m Q hQ hsupport
  let F : Ξ → Ω × ℝ := fun ξ => (S ξ, T ξ)
  have hF : Measurable F := hS.prodMk hT
  have hFae : Measure.QuasiMeasurePreserving F R (P.prod Q) := by
    refine ⟨hF, ?_⟩
    rw [hlaw]
  have hevent' := hFae.ae hevent
  refine ⟨H₀ ∘ F, Z₀ ∘ F, E₀ ∘ F, hZ₀.comp hF, hE₀.comp hF, ?_, ?_, ?_⟩
  · apply Measure.map_congr
    filter_upwards [hevent'] with p hp
    obtain ⟨_, _, _, _, _, _, _, he, _⟩ := hp
    exact Prod.ext he rfl
  · refine ⟨Z₀, hZ₀, fun _ => rfl, ?_⟩
    rw [← Measure.map_map hZ₀ hF, hlaw]
  · exact hevent'

end MatedCRT
end
