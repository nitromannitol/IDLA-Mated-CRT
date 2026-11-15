import MatedCRT.FirstPass.Derived.CouplingProductJointEnvironmentWalk
import MatedCRT.FirstPass.Derived.CouplingShiftedAreaCellWalk

/-! # Joint shifted environment and cell-walk laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- The joint environment and selected-walk representation can be matched with
Brownian-edge cell-walk laws at every integer start. -/
theorem exists_prod_shiftedAreaCellConfig_jointEnvironment_cellWalk_of_coupling
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
        (∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area p.1) (η p.1),
          H p = shiftedAreaCellConfig h hε (p.2 / ε)
            (bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
              (fun t => (bm p.1 (t + p.2)).2)) ∧
          (H p).IsCellConfiguration ∧ (H p).LineConnected ∧
          let M := bmEdgeCount ε (fun t => (bm p.1 (t + p.2)).1)
            (fun t => (bm p.1 (t + p.2)).2)
          let C := shiftedAreaCellConfig h hε (p.2 / ε) M
          ∀ a : ℤ, C.IsSRWLaw (shiftedEuclideanCellEquiv h hε (p.2 / ε) a)
            ((srwLaw M a).map (fun path n => shiftedEuclideanCellEquiv h hε (p.2 / ε) (path n)))) ∧
        Z p = ((H p).code, shiftedSelectedWalkLaw ε m p.2 (x p) (η p.1) (bm p.1)) ∧
        (Z p).1 ∈ goodCodes ∧ (E p).val = (Z p).1 := by
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨H, Z, E, hZ, hE, hmap, hmatch⟩ :=
    exists_prod_shiftedAreaCellConfig_jointEnvironment_selectedWalkLaw_of_coupling
      D hγ hε m Q x hx hembed
  have hwalk := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae
    (ae_shiftedAreaCellWalk_of_coupling D hγ hε)
  refine ⟨H, Z, E, hZ, hE, hmap, ?_⟩
  filter_upwards [hmatch, hembed, hwalk] with p hm he hw
  obtain ⟨h, hH, hconfig, hconnected⟩ := hm.1
  obtain ⟨hlf, H', hH'⟩ := he
  obtain ⟨h', hw⟩ := hw
  have hsrw := (hw p.2 hlf H' hH').2.2
  exact ⟨⟨h, hH, hconfig, hconnected, hsrw⟩, hm.2⟩

end MatedCRT
