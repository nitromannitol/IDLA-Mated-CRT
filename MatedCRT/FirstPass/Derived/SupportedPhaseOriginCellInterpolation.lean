import MatedCRT.FirstPass.Derived.SupportedPhaseJointCellInterpolation
import MatedCRT.FirstPass.Derived.CouplingAreaParametrization
import MatedCRT.FirstPass.Derived.ShiftedOriginSelectedVertex

/-! # Origin walks for independently shifted coupling cells -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- An independent supported absolutely continuous phase selects the origin
cell with label zero on the joint environment and cell-walk event. -/
theorem exists_prod_jointEnvironment_originCellWalk_of_supported_phase
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
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
          vertexOf ε (fun t => η p.1 (t + p.2)) 0 = 0 ∧
          let M := bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
            (fun t => (bm p.1 (t + p.2)).2)
          let C := shiftedAreaCellConfig h hε (p.2 / ε) M
          (∀ a : ℤ, C.IsSRWLaw (shiftedEuclideanCellEquiv h hε (p.2 / ε) a)
            ((srwLaw M a).map (fun path n =>
              shiftedEuclideanCellEquiv h hε (p.2 / ε) (path n)))) ∧
          ∀ (R : Measure (ℕ → C.cells)),
            C.IsSRWLaw (shiftedEuclideanCellEquiv h hε (p.2 / ε)
              0) R →
            (Z p).2 = R.map (fun path =>
              interpPathCM (vertexPoint ε (fun t => η p.1 (t + p.2))) m.coe_nonneg
                (fun n => (shiftedEuclideanCellEquiv h hε (p.2 / ε)).symm (path n))) := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hf : ∀ᵐ ω ∂P, ∀ t, η ω t = η ω 0 → t = 0 := by
    apply LatticeProb.CorrelatedBM.ae_singleton_fiber_of_contour_relation
      D.measurable_curves.2.2.2.aemeasurable D.boundaryLawBM 0
    filter_upwards [D.onlyMerge] with ω hω t ht
    exact hω 0 t ht.symm
  have ha := ae_isAreaParametrized_of_coupling D hγ
  have hroot : ∀ᵐ ω ∂P, ∀ c, 0 < c → c < ε →
      vertexOf ε (fun t => η ω (t + c)) 0 = 0 := by
    filter_upwards [ha, hf] with ω harea hfiber c hc hcε
    exact vertexOf_shifted_origin_eq_zero harea.2.1 hfiber hε ⟨hc, hcε⟩
  have h0 : ∀ᵐ c ∂Q, c ≠ 0 := hQ.ae_le (Measure.ae_ne volume 0)
  have h1 : ∀ᵐ c ∂Q, c ≠ ε := hQ.ae_le (Measure.ae_ne volume ε)
  have hs : ∀ᵐ c ∂Q, 0 < c ∧ c < ε := by
    filter_upwards [hsupport, h0, h1] with c hc hc0 hc1
    exact ⟨lt_of_le_of_ne hc.1 (Ne.symm hc0), lt_of_le_of_ne hc.2 hc1⟩
  obtain ⟨H, Z, E, hZm, hEm, hmap, hevent⟩ :=
    exists_prod_jointEnvironment_interpolatedCellWalk_of_supported_phase
      D hγ hε m Q (fun _ => 0) measurable_const hQ hsupport
  refine ⟨H, Z, E, hZm, hEm, hmap, ?_⟩
  filter_upwards [hevent,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae hroot,
    (Measure.quasiMeasurePreserving_snd (μ := P) (ν := Q)).ae hs] with p hp hrootp hsp
  obtain ⟨h, hlf, hH, hC, hline, hZ, hgood, hE, hwalk, hinterp⟩ := hp
  have hv := hrootp p.2 hsp.1 hsp.2
  refine ⟨h, hlf, hH, hC, hline, hZ, hgood, hE, hv, hwalk, ?_⟩
  simpa only [hv] using hinterp

end MatedCRT
end
