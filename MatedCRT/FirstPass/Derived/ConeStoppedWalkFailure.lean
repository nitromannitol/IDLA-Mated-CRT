import MatedCRT.FirstPass.Derived.ConeStoppedWalkVertexFamily

/-! # Transfer of measurable events for families of stopped walks -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set
open scoped NNReal ENNReal
open MatedCRT.ExitCouplingGlue

/-- Starting positions and quenched stopped laws, indexed by all vertices. -/
noncomputable def stoppedWalkVertexFamily (ε : ℝ) (η : ℝ → ℂ) (bm : ℝ → ℝ × ℝ)
    (D : Set ℂ) (m : ℝ≥0) : ℤ → ℂ × Measure C(ℝ≥0, ℂ) := fun a =>
  (vertexPoint ε η a,
    (srwLaw (bmEdgeCount ε (fun t => (bm t).1) (fun t => (bm t).2)) a).map
      (stoppedInterp (vertexPoint ε η) m (interiorCellVertices ε η D)))

/-- A measurable event of the whole stopped-walk family has the same probability
under a deterministic cone rescaling. -/
theorem MatedCRTEnv.IsValid.measure_stoppedWalkVertexFamily_rescaled
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (m : ℝ≥0)
    (E : Set (ℤ → ℂ × Measure C(ℝ≥0, ℂ))) (hE : MeasurableSet E) :
    S.P {ω | stoppedWalkVertexFamily ε
      (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
      (rescaledPair b (S.bm ω)) D m ∈ E} =
    S.P {ω | stoppedWalkVertexFamily ε (S.η ω) (S.bm ω) D m ∈ E} := by
  obtain ⟨V, V', hV, hC, hbm, htie, hV', hlaw, hae⟩ := hS.exists_coneDataLift hγ hγ2 hb
  have hid := hS.ae_coneDataLift_rescaled hγ hγ2 hb hV hC hbm htie hV' hlaw hae
  let F : C(ℝ, ℂ) × C(ℝ, ℝ × ℝ) → ℤ → ℂ × Measure C(ℝ≥0, ℂ) :=
    fun p => stoppedWalkVertexFamily ε p.1 p.2 D m
  have hF : Measurable F := by
    apply measurable_pi_iff.2
    intro a
    exact ((ContinuousMap.measurable_eval _).comp measurable_fst).prodMk
      (measurable_stoppedWalkLaw_curve_boundary ε D hD m a)
  let G : MatedCRTHarmonic.MatedCRT.CouplingData → ℤ → ℂ × Measure C(ℝ≥0, ℂ) :=
    fun v => F (v.η, v.bm)
  have hG : Measurable G := hF.comp
    (MatedCRTHarmonic.MatedCRT.CouplingData.measurable_η.prodMk
      MatedCRTHarmonic.MatedCRT.CouplingData.measurable_bm)
  have hscaled : AEMeasurable (fun ω => stoppedWalkVertexFamily ε
      (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
      (rescaledPair b (S.bm ω)) D m) S.P := by
    apply ((hG.comp hV').aemeasurable.congr ?_)
    filter_upwards [hid] with ω hω
    dsimp [G, F, stoppedWalkVertexFamily]
    rw [hω.1, hω.2.1]
  have horiginal : AEMeasurable (fun ω => stoppedWalkVertexFamily ε (S.η ω) (S.bm ω) D m) S.P := by
    apply ((hG.comp hV).aemeasurable.congr ?_)
    filter_upwards [htie] with ω hω
    dsimp [G, F, stoppedWalkVertexFamily]
    rw [hω.1, hbm ω]
  have heq := hS.map_stoppedWalkVertexFamily_rescaled hγ hγ2 hb ε D hD m
  change S.P.map (fun ω => stoppedWalkVertexFamily ε
      (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
      (rescaledPair b (S.bm ω)) D m) =
    S.P.map (fun ω => stoppedWalkVertexFamily ε (S.η ω) (S.bm ω) D m) at heq
  change S.P ((fun ω => stoppedWalkVertexFamily ε
      (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
      (rescaledPair b (S.bm ω)) D m) ⁻¹' E) =
    S.P ((fun ω => stoppedWalkVertexFamily ε (S.η ω) (S.bm ω) D m) ⁻¹' E)
  rw [← Measure.map_apply_of_aemeasurable hscaled hE,
    ← Measure.map_apply_of_aemeasurable horiginal hE, heq]

/-- A pathwise comparison outside the radius exception transfers a measurable
family-level event bound, retaining arbitrary dependence on the cone radius. -/
theorem MatedCRTEnv.IsValid.measure_le_of_stoppedWalkVertexFamily_rescaled
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ b : ℝ}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (m : ℝ≥0)
    (E : Set (ℤ → ℂ × Measure C(ℝ≥0, ℂ))) (hE : MeasurableSet E)
    (bad : Set Ω) (M : ℝ) (α θ : ℝ≥0∞)
    (hcomparison : ∀ᵐ ω ∂S.P, ω ∈ bad →
      stoppedWalkVertexFamily ε
        (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
        (rescaledPair b (S.bm ω)) D m ∈ E ∨ M < coneScaleRadius γ (S.hcirc ω) b)
    (hsource : S.P {ω | stoppedWalkVertexFamily ε (S.η ω) (S.bm ω) D m ∈ E} ≤ α)
    (hradius : S.P {ω | M < coneScaleRadius γ (S.hcirc ω) b} ≤ θ) :
    S.P bad ≤ α + θ := by
  calc
    S.P bad ≤ S.P ({ω | stoppedWalkVertexFamily ε
        (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
        (rescaledPair b (S.bm ω)) D m ∈ E} ∪
        {ω | M < coneScaleRadius γ (S.hcirc ω) b}) := by
      apply measure_mono_ae
      filter_upwards [hcomparison] with ω hω
      exact hω
    _ ≤ S.P {ω | stoppedWalkVertexFamily ε
        (fun s => (coneScaleRadius γ (S.hcirc ω) b : ℂ)⁻¹ * S.η ω (b * s))
        (rescaledPair b (S.bm ω)) D m ∈ E} +
        S.P {ω | M < coneScaleRadius γ (S.hcirc ω) b} := measure_union_le _ _
    _ ≤ α + θ := by
      rw [hS.measure_stoppedWalkVertexFamily_rescaled hγ hγ2 hb ε D hD m E hE]
      exact add_le_add hsource hradius

end MatedCRT
