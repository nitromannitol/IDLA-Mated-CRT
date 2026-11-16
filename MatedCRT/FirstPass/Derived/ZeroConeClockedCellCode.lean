import MatedCRT.FirstPass.Derived.ZeroConeAreaParametrization
import MatedCRT.FirstPass.Derived.SelectedShiftedAreaCellCode
import MatedCRT.FirstPass.Derived.ShiftedAreaCellPeanosphereConnectivity
import LatticeProb.LQG.CoupledClockedCellEmbedding

/-! # Shifted cell codes for the zero-cone clock -/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal

/-- The zero-cone area cells admit a valid configuration with measurable code,
using the same clocked contour and independent phase as the embedding. -/
theorem exists_zeroCone_clocked_shiftedCellCode
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    {ε : ℝ} (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume)
    (hphase : ∀ᵐ θ ∂Q, θ ∈ Icc (0 : ℝ) 1) :
    ∃ G : Ω → Path2, Measurable G ∧
      (∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
        (∀ t, η₀ ω t = η ω (ψ t)) ∧
        (∀ t, G ω t = bm ω (ψ t)) ∧
        (∀ t, CellScaling.JointScalingO.clock γ
          (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
          (η₀ ω) t = ψ t) ∧ RouteM.Peanosphere (G ω) (η₀ ω)) ∧
      ∃ H : Ω × ℝ → CellConfig,
        (∀ᵐ p ∂P.prod Q, ∃ h : IsAreaParametrized
            ((l46tZeroConeCellModel D hγ).area p.1) (η₀ p.1),
          H p = shiftedAreaCellConfig h hε p.2
            (bmEdgeCount ε (fun t => (G p.1 (t + ε * p.2)).1)
              (fun t => (G p.1 (t + ε * p.2)).2)) ∧ (H p).IsCellConfiguration) ∧
        AEMeasurable (fun p => (H p).code) (P.prod Q) := by
  obtain ⟨G, hG, hclock, hembed⟩ :=
    LatticeProb.exists_coupled_clocked_cellularEmbedding D hγ hf ε hε Q hQ
  let : IsProbabilityMeasure P := D.isProbabilityMeasure
  have ha := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae
    (ae_zeroCone_isAreaParametrized_of_coupling D hγ)
  have hp := (Measure.quasiMeasurePreserving_snd (μ := P) (ν := Q)).ae hphase
  have hvalid : ∀ᵐ p ∂P.prod Q, ∃ h : IsAreaParametrized
      ((l46tZeroConeCellModel D hγ).area p.1) (η₀ p.1),
      (shiftedAreaCellConfig h hε p.2
        (bmEdgeCount ε (fun t => (G p.1 (t + ε * p.2)).1)
          (fun t => (G p.1 (t + ε * p.2)).2))).IsCellConfiguration := by
    filter_upwards [ha, hp, hembed] with p ha hp he
    obtain ⟨hlf, H, hH⟩ := he hp.1 hp.2
    refine ⟨ha, ?_⟩
    apply shiftedAreaCellConfig_isCellConfiguration ha hε p.2 _ H hH
      (bmEdgeCount_symm ε _ _) (bmEdgeCount_self ε _ _)
    intro a b hab
    have hne : a ≠ b := by
      intro heq
      subst b
      rw [bmEdgeCount_self] at hab
      exact (lt_irrefl 0) hab
    rw [graph_adj_eq_srwGraph hlf hε.le]
    exact ⟨hne, Or.inl (Nat.ne_of_gt hab)⟩
  obtain ⟨H, hH, hcode⟩ := exists_shiftedAreaCellConfig_aemeasurable_code
    (P.prod Q) hε (η₀ ∘ Prod.fst) (G ∘ Prod.fst) Prod.snd
    (fun p => (l46tZeroConeCellModel D hγ).area p.1)
    (D.measurable_curves.2.2.1.comp measurable_fst) (hG.comp measurable_fst)
    measurable_snd hvalid
  exact ⟨G, hG, hclock, H, hH, hcode⟩

end MatedCRT
