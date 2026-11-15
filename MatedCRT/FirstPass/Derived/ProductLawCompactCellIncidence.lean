import MatedCRT.FirstPass.Derived.ProductLawOriginCellInterpolation
import MatedCRT.FirstPass.Derived.ShiftedAreaCellFiniteLabels

/-! # Compact incidence under a product-law realization -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- The product-law origin-cell walk realization has finitely many shifted
cell labels meeting any compact set, on the same almost-sure event. -/
theorem exists_jointEnvironment_originCellWalk_compactIncidence_of_product_law
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
          (∀ K : Set ReflectedGMS.Plane, IsCompact K →
            {a : ℤ | (((LatticeProb.shiftedCompactCell
              ((⟨Complex.orthonormalBasisOneI.repr,
                Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp (η (S p)))
              ε ((T p) / ε) a) : Set ReflectedGMS.Plane) ∩ K).Nonempty}.Finite) ∧
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
  obtain ⟨H, Z, E, hZ, hE, hlawE, hZ₀, hevent⟩ :=
    exists_jointEnvironment_originCellWalk_of_product_law D hγ hε m Q hQ hsupport
      S T hS hT hlaw
  refine ⟨H, Z, E, hZ, hE, hlawE, hZ₀, ?_⟩
  filter_upwards [hevent] with p hp
  obtain ⟨h, hlf, heq, hv, hl, hz, hg, he, hor, hrest⟩ := hp
  refine ⟨h, hlf, heq, hv, hl, hz, hg, he, hor, ?_, hrest⟩
  intro K hK
  have hfinite := finite_shiftedAreaCell_indices_meeting_compact h hε ((T p) / ε)
    (bmEdgeCount ε (fun t => (bm (S p) (t + T p)).1)
      (fun t => (bm (S p) (t + T p)).2)) (heq ▸ hv) hK
  convert hfinite using 1
  congr 1
  funext a
  have hceq :
      (LatticeProb.shiftedCompactCell
        ((⟨Complex.orthonormalBasisOneI.repr,
          Complex.orthonormalBasisOneI.repr.continuous⟩ : C(ℂ, ReflectedGMS.Plane)).comp (η (S p)))
        ε (T p / ε) a : Set ReflectedGMS.Plane) =
      (euclideanCell ε (fun t => η (S p) (t + ε * (T p / ε)))
        (h.1.comp (continuous_id.add continuous_const)) hε a : Set ReflectedGMS.Plane) := by
    rw [coe_euclideanCell, LatticeProb.coe_shiftedCompactCell]
    have ht := shiftedCompactCell_eq_cell_timeShift (η (S p)) hε.le (T p / ε) a
    rw [LatticeProb.coe_shiftedCompactCell] at ht
    change Set.image (fun t => Complex.orthonormalBasisOneI.repr (η (S p) t)) _ = _
    simpa only [Set.image_image, Function.comp_def] using
      congrArg (Set.image Complex.orthonormalBasisOneI.repr) ht
  rw [hceq]

end MatedCRT
end
