import MatedCRT.FirstPass.Derived.CouplingJointEnvironmentCellWalk
import MatedCRT.FirstPass.Derived.ShiftedSelectedCellInterpolation

/-! # Joint environment and interpolated cell walks -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- The walk coordinate in the joint representation is the interpolation of
any cell random walk started at the selected cell. -/
theorem exists_prod_jointEnvironment_interpolatedCellWalk_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (x : Ω × ℝ → ℂ)
    (hx : Measurable x)
    (hembed : ∀ᵐ p ∂P.prod Q,
      let w : Path2 := ⟨fun t => bm p.1 (t + p.2),
        (bm p.1).continuous.comp (by fun_prop)⟩
      ∃ (hlf : IsLocallyFinite ε w)
        (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε w hlf) 0),
        H.cell = cell ε (fun t => η p.1 (t + p.2))) :
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
  obtain ⟨H, Z, E, hZ, hE, hmap, hmatch⟩ :=
    exists_prod_shiftedAreaCellConfig_jointEnvironment_cellWalk_of_coupling
      D hγ hε m Q x hx hembed
  refine ⟨H, Z, E, hZ, hE, hmap, ?_⟩
  filter_upwards [hmatch, hembed] with p hm he
  obtain ⟨h, hH, hconfig, hconnected, hwalk⟩ := hm.1
  obtain ⟨hlf, H', hH'⟩ := he
  refine ⟨h, hlf, hH, hconfig, hconnected, ?_, hm.2.2.1, hm.2.2.2, hwalk, ?_⟩
  · exact congrArg Prod.fst hm.2.1
  · intro R hR
    rw [congrArg Prod.snd hm.2.1]
    exact shiftedSelectedWalkLaw_eq_map_cellWalk h hε p.2 (bm p.1) (x p) m hlf R hR

end MatedCRT
end
