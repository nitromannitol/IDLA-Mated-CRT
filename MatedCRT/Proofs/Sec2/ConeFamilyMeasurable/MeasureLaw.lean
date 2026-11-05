import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.Assembly
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.VolumeGrowthSupport

/-! # LQG measure laws from circle-average laws -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls ProbabilityTheory
open scoped ENNReal

/-- The law of an LQG limit is determined by the law of the continuous
positive-radius circle-average process. -/
theorem identDistrib_lqgMeasure_of_circleProcess
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {γ : ℝ}
    {c d : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hd : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => d ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (c ω) (μ ω))
    (hν : ∀ᵐ ω ∂P, IsLQGLimit γ (d ω) (ν ω))
    (hmμ : AEMeasurable μ P) (hmν : AEMeasurable ν P)
    (hlaw : IdentDistrib (fun ω => circleProcess (c ω)) (fun ω => circleProcess (d ω)) P P) :
    IdentDistrib μ ν P P := by
  classical
  apply identDistrib_of_open_masses hmμ hmν (hμ.mono fun _ h => h.isLocallyFiniteMeasure)
    (hν.mono fun _ h => h.isLocallyFiniteMeasure)
  intro ι _ U hU
  choose f hf hfc hmass using fun i : ι => exists_open_mass_test_functions (hU i)
  choose A hA hAeq using fun n : ℕ => exists_measurable_lqgApprox_decoder γ (dyadicScale n)
  let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
  let profile (n : ℕ) (v : Ioi (0 : ℝ) × ℂ → ℝ) (z : ℂ) :=
    v (⟨dyadicScale n, dyadicScale_pos n⟩, z)
  have hp (n : ℕ) : Measurable (profile n) := by
    apply Measurable.of_eval
    intro z
    exact measurable_pi_apply _
  let F : (Ioi (0 : ℝ) × ℂ → ℝ) → ι → ℝ≥0∞ := fun v i =>
    ⨆ j : ℕ, Filter.liminf (fun n => ENNReal.ofReal (∫ z, f i j z ∂(A n (profile n v)))) atTop
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro i
    apply Measurable.iSup
    intro j
    apply Measurable.liminf
    intro n
    exact (((hf i j).stronglyMeasurable.integral_kernel (κ := K)).measurable.comp
      ((hA n).comp (hp n))).ennreal_ofReal
  have hdecode (x : Ω → ℝ → ℂ → ℝ) (m : Ω → Measure ℂ)
      (hx : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => x ω p.1 p.2) (Ioi 0 ×ˢ univ))
      (hm : ∀ᵐ ω ∂P, IsLQGLimit γ (x ω) (m ω)) :
      ∀ᵐ ω ∂P, F (circleProcess (x ω)) = fun i => m ω (U i) := by
    filter_upwards [hx, hm] with ω hxω hmω
    funext i
    rw [hmass i (m ω) hmω.isLocallyFiniteMeasure]
    change (⨆ j : ℕ, Filter.liminf (fun n => ENNReal.ofReal
      (∫ z, f i j z ∂(A n (profile n (circleProcess (x ω)))))) atTop) = _
    apply iSup_congr
    intro j
    apply Filter.Tendsto.liminf_eq
    apply (ENNReal.continuous_ofReal.tendsto _).comp
    convert hmω.tendsto_integral (f i j) (hf i j) (hfc i j) using 1
    funext n
    have hcont : Continuous (fun z => x ω (dyadicScale n) z) :=
      hxω.comp_continuous (continuous_const.prodMk continuous_id)
        (fun z => ⟨dyadicScale_pos n, mem_univ z⟩)
    have heq : A n (profile n (circleProcess (x ω))) = lqgApprox γ (x ω) (dyadicScale n) := by
      simpa only [profile, circleProcess, lqgApprox] using hAeq n (fun z => x ω (dyadicScale n) z) hcont
    rw [heq]
  have hfd := hlaw.comp hF
  exact ((IdentDistrib.of_ae_eq hfd.aemeasurable_fst (hdecode c μ hc hμ)).symm.trans hfd).trans
    (IdentDistrib.of_ae_eq hfd.aemeasurable_snd (hdecode d ν hd hν))

/-- The rescaled quantum-cone LQG measure has the original measure law. -/
theorem IsConeField.identDistrib_rescaledMeasure
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (hscale : QuantumConeScalingInput)
    (hlqg : ConeLQGScalingStep) {b : ℝ} (hb : 0 < b) :
    IdentDistrib (fun ω => rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) μ P P := by
  let : IsProbabilityMeasure P := hcone.1
  have hs := hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb
  have hR : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b := hs.mono fun _ h => h.1
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ =>
      rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b p.1 p.2) (Ioi 0 ×ˢ univ) := by
    filter_upwards [hcone.2.1.ae_continuousOn_circle, hR] with ω hc hr
    exact continuousOn_rescaledCircle hc hr
  have hcirc : IdentDistrib (fun ω => circleProcess (rescaledCircle γ (hcirc ω)
      (coneScaleRadius γ (hcirc ω) b) b)) (fun ω => circleProcess (hcirc ω)) P P :=
    ⟨Sec1.aemeasurable_circleProcess_rescaledCircle hscale hγ hγ2 hcone.2.1 hb,
      hcone.2.1.measurable_circleProcess.aemeasurable,
      hscale γ hγ hγ2 Ω P hC hcirc hcone.1 hcone.2.1 b hb⟩
  exact identDistrib_lqgMeasure_of_circleProcess hcont hcone.2.1.ae_continuousOn_circle
    (hs.mono fun _ h => h.2) hcone.2.2 (hcone.aemeasurable_rescaledMeasure b hR)
    hcone.aemeasurable_lqgMeasure hcirc

/-- The rescaled cone measure has volume growth on each fixed disk strictly
inside the unit disk. -/
theorem IsConeField.ae_rescaledVolumeGrowth_inside_unit
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    (hscale : QuantumConeScalingInput) (hlqg : ConeLQGScalingStep)
    {b R : ℝ} (hb : 0 < b) (hR : 0 < R) (hR1 : R < 1) :
    ∀ᵐ ω ∂P, ∃ βm βp, VolumeGrowth
      (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) R βm βp := by
  obtain ⟨E, hE, hae, hgood⟩ := hcone.exists_measurable_volumeGrowth_support hγ hγ2 h27 hR hR1
  have hid := hcone.identDistrib_rescaledMeasure hγ hγ2 hscale hlqg hb
  have hmapped : ∀ᵐ ν ∂(P.map μ), ν ∈ E := (ae_map_iff hid.aemeasurable_snd hE).2 hae
  have hres : ∀ᵐ ω ∂P, rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b ∈ E :=
    (ae_map_iff hid.aemeasurable_fst hE).1 (by rw [hid.map_eq]; exact hmapped)
  filter_upwards [hres] with ω hω
  exact (hgood _ hω).2

/-- Cone-family measurability from cone volume growth, strict growth,
quantum-cone scaling and LQG coordinate scaling. -/
theorem coneFamilyAEMeasurableStep_of_scaling
    (h27 : VolumeGrowthStmt) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hscale : QuantumConeScalingInput) (hlqg : ConeLQGScalingStep) :
    ConeFamilyAEMeasurableStep := by
  apply coneFamilyAEMeasurableStep_of_rescaledVolumeGrowth h27 hgrow hscale hlqg
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone b hb
  exact hcone.ae_rescaledVolumeGrowth_inside_unit hγ hγ2 h27 hscale hlqg hb (by norm_num) (by norm_num)

end MatedCRT
