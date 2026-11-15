import MatedCRT.FirstPass.Derived.CouplingAreaParametrization
import MatedCRT.FirstPass.Derived.ShiftedAreaCellPeanosphereConnectivity
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveGeometry
import LatticeProb.LQG.PeanosphereTimeTranslation

/-! # Shifted cell geometry in a mating-of-trees coupling -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTInput
open scoped NNReal

/-- A matching translated embedding gives a line-connected area-cell configuration
for the actual translated Brownian edge multiplicities. -/
theorem ae_shiftedAreaCellConfig_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized ((cellModelOfCoupling D hγ).area ω) (η ω),
      ∀ c : ℝ, ∀ (hlf : IsLocallyFinite ε
        ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩)
        (H : CellularEmbedding (MatedCRTHarmonic.MatedCRT.graph ε
          ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩ hlf) 0),
        H.cell = cell ε (fun t => η ω (t + c)) →
        let w : Path2 := ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩
        let C := shiftedAreaCellConfig h hε (c / ε)
          (bmEdgeCount ε (fun t => (w t).1) (fun t => (w t).2))
        C.IsCellConfiguration ∧ C.LineConnected := by
  filter_upwards [ae_isAreaParametrized_of_coupling D hγ, ae_peanosphere D] with ω h hP
  refine ⟨h, ?_⟩
  intro c hlf H hH
  have heq : ε * (c / ε) = c := mul_div_cancel₀ c (ne_of_gt hε)
  have hH' : H.cell = cell ε (fun t => η ω (t + ε * (c / ε))) := by
    simpa only [heq] using hH
  have hp := hP.time_translate c
  have hp' : RouteM.Peanosphere
      ⟨fun t => bm ω (t + c), (bm ω).continuous.comp (by fun_prop)⟩
      (fun t => η ω (t + ε * (c / ε))) := by
    simpa only [heq] using hp
  constructor
  · apply shiftedAreaCellConfig_isCellConfiguration h hε (c / ε) _ H hH'
      (bmEdgeCount_symm ε _ _) (bmEdgeCount_self ε _ _)
    intro a b hab
    have hne : a ≠ b := by
      intro he
      subst b
      rw [bmEdgeCount_self] at hab
      exact (lt_irrefl 0) hab
    rw [graph_adj_eq_srwGraph hlf hε.le]
    exact ⟨hne, Or.inl (Nat.ne_of_gt hab)⟩
  · exact shiftedAreaCellConfig_lineConnected_of_peanosphere h hε (c / ε) _ hlf H hH' hp'

end MatedCRT
