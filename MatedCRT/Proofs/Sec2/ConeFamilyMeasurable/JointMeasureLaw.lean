import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.MeasureFunctional

/-! # Joint laws of circle averages and LQG measures -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls ProbabilityTheory
open scoped ENNReal

/-- Circle-average laws determine the joint laws of the process and finitely
many open-set masses of its limiting LQG measure. -/
theorem identDistrib_circleProcess_openMasses
    {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω} {γ : ℝ}
    {c d : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hd : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => d ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (c ω) (μ ω))
    (hν : ∀ᵐ ω ∂P, IsLQGLimit γ (d ω) (ν ω))
    (hlaw : IdentDistrib (fun ω => circleProcess (c ω)) (fun ω => circleProcess (d ω)) P P)
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) :
    IdentDistrib (fun ω => (circleProcess (c ω), fun i => μ ω (U i)))
      (fun ω => (circleProcess (d ω), fun i => ν ω (U i))) P P := by
  classical
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
  have hD := hlaw.comp (measurable_id.prodMk hF)
  have hleft : ∀ᵐ ω ∂P, (circleProcess (c ω), F (circleProcess (c ω))) =
      (circleProcess (c ω), fun i => μ ω (U i)) := by
    filter_upwards [hdecode c μ hc hμ] with ω hω
    rw [hω]
  have hright : ∀ᵐ ω ∂P, (circleProcess (d ω), F (circleProcess (d ω))) =
      (circleProcess (d ω), fun i => ν ω (U i)) := by
    filter_upwards [hdecode d ν hd hν] with ω hω
    rw [hω]
  exact ((IdentDistrib.of_ae_eq hD.aemeasurable_fst hleft).symm.trans hD).trans
    (IdentDistrib.of_ae_eq hD.aemeasurable_snd hright)


/-- The circle-average process and its limiting LQG measure have a joint law
which is determined by the law of the circle averages. -/
theorem identDistrib_circleProcess_lqgMeasure
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {γ : ℝ}
    {c d : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hd : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => d ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (c ω) (μ ω))
    (hν : ∀ᵐ ω ∂P, IsLQGLimit γ (d ω) (ν ω))
    (hmμ : AEMeasurable μ P) (hmν : AEMeasurable ν P)
    (hlaw : IdentDistrib (fun ω => circleProcess (c ω)) (fun ω => circleProcess (d ω)) P P) :
    IdentDistrib (fun ω => (circleProcess (c ω), μ ω))
      (fun ω => (circleProcess (d ω), ν ω)) P P := by
  classical
  let O := {U : Set ℂ // IsOpen U}
  let I := Ioi (0 : ℝ) × ℂ
  let J := O ⊕ I
  let enc : ((I → ℝ) × Measure ℂ) → J → ℝ≥0∞ := fun p j =>
    match j with
    | .inl U => p.2 U.1
    | .inr i => ENNReal.ofReal (Real.exp (p.1 i))
  have henc : Measurable enc := by
    apply Measurable.of_eval
    intro j
    cases j with
    | inl U => exact (Measure.measurable_coe U.2.measurableSet).comp measurable_snd
    | inr i => exact (((measurable_pi_apply i).comp measurable_fst).exp).ennreal_ofReal
  let X : Ω → (I → ℝ) × Measure ℂ := fun ω => (circleProcess (c ω), μ ω)
  let Y : Ω → (I → ℝ) × Measure ℂ := fun ω => (circleProcess (d ω), ν ω)
  have hXm : AEMeasurable X P := hlaw.aemeasurable_fst.prodMk hmμ
  have hYm : AEMeasurable Y P := hlaw.aemeasurable_snd.prodMk hmν
  have hcode : IdentDistrib (enc ∘ X) (enc ∘ Y) P P := by
    apply (identDistrib_iff_forall_finset_identDistrib
      (henc.comp_aemeasurable hXm) (henc.comp_aemeasurable hYm)).2
    intro F
    let U : F → Set ℂ := fun i => match i.1 with | .inl u => u.1 | .inr _ => ∅
    have hU : ∀ i, IsOpen (U i) := by
      intro i
      rcases i with ⟨j, hj⟩
      cases j with
      | inl u => exact u.2
      | inr i => exact isOpen_empty
    let decode : ((I → ℝ) × (F → ℝ≥0∞)) → F → ℝ≥0∞ := fun p i =>
      match i.1 with | .inl _ => p.2 i | .inr j => ENNReal.ofReal (Real.exp (p.1 j))
    have hdecode : Measurable decode := by
      apply Measurable.of_eval
      intro i
      rcases i with ⟨j, hj⟩
      cases j with
      | inl u => exact (measurable_pi_apply (⟨Sum.inl u, hj⟩ : F)).comp measurable_snd
      | inr i => exact (((measurable_pi_apply i).comp measurable_fst).exp).ennreal_ofReal
    have h := (identDistrib_circleProcess_openMasses hc hd hμ hν hlaw U hU).comp hdecode
    convert h using 1 <;> funext ω i <;> cases i with | mk j hj => cases j <;> rfl
  let L := (I → ℝ) × {m : Measure ℂ // IsLocallyFiniteMeasure m}
  let e : L → J → ℝ≥0∞ := fun p => enc (p.1, p.2.1)
  let : MeasurableSpace L := MeasurableSpace.comap e inferInstance
  have hread : Measurable (fun p : L => (p.1, p.2.1)) := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro i
      have hv := ((measurable_pi_apply (Sum.inr i : J)).comp (comap_measurable e)).ennreal_toReal
      have hv := hv.log
      simpa [e, enc, ENNReal.toReal_ofReal, (Real.exp_pos _).le] using hv
    · apply measurable_measure_of_isOpen (fun p : L => p.2.2)
      intro U hU
      exact (measurable_pi_apply (Sum.inl (⟨U, hU⟩ : O))).comp (comap_measurable e)
  refine ⟨hXm, hYm, ?_⟩
  apply Measure.ext
  intro S hS
  obtain ⟨T, hT, heq⟩ := MeasurableSpace.measurableSet_comap.mp (hread hS)
  have hpreX : X ⁻¹' S =ᵐ[P] (enc ∘ X) ⁻¹' T := by
    filter_upwards [hμ] with ω hω
    change (X ω ∈ S) = (enc (X ω) ∈ T)
    have hh := Set.ext_iff.mp heq (⟨(X ω).1, ⟨μ ω, hω.isLocallyFiniteMeasure⟩⟩ : L)
    exact propext hh.symm
  have hpreY : Y ⁻¹' S =ᵐ[P] (enc ∘ Y) ⁻¹' T := by
    filter_upwards [hν] with ω hω
    change (Y ω ∈ S) = (enc (Y ω) ∈ T)
    have hh := Set.ext_iff.mp heq (⟨(Y ω).1, ⟨ν ω, hω.isLocallyFiniteMeasure⟩⟩ : L)
    exact propext hh.symm
  rw [Measure.map_apply_of_aemeasurable hXm hS,
    Measure.map_apply_of_aemeasurable hYm hS,
    measure_congr hpreX, measure_congr hpreY,
    ← Measure.map_apply_of_aemeasurable hcode.aemeasurable_fst hT,
    ← Measure.map_apply_of_aemeasurable hcode.aemeasurable_snd hT, hcode.map_eq]


/-- Quantum-cone scaling preserves the joint law of circle averages and the
corresponding LQG measure. -/
theorem IsConeField.identDistrib_rescaledCircleMeasure
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (hscale : QuantumConeScalingInput)
    (hlqg : ConeLQGScalingStep) {b : ℝ} (hb : 0 < b) :
    IdentDistrib (fun ω => (circleProcess (rescaledCircle γ (hcirc ω)
        (coneScaleRadius γ (hcirc ω) b) b),
      rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b))
      (fun ω => (circleProcess (hcirc ω), μ ω)) P P := by
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
  exact identDistrib_circleProcess_lqgMeasure hcont hcone.2.1.ae_continuousOn_circle
    (hs.mono fun _ h => h.2) hcone.2.2 (hcone.aemeasurable_rescaledMeasure b hR)
    hcone.aemeasurable_lqgMeasure hcirc

/-- The stopped cone family and its circle averages have the same joint law
after quantum-cone rescaling, provided both families satisfy their defining
conditions. -/
theorem IsConeField.identDistrib_rescaledCircleHalfBallFamily
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    (hgrow : ConeHarmonicBallStrictGrowthStep) (hscale : QuantumConeScalingInput)
    (hlqg : ConeLQGScalingStep) {b : ℝ} (hb : 0 < b)
    {T U : Ω → ℝ} {Λ Γ : Ω → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω))
    (hΓ : ∀ᵐ ω ∂P, 0 < U ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Γ ω) (b * U ω) ∧
      IsStoppedAtHalfBall (rescaledFamily (Γ ω) (coneScaleRadius γ (hcirc ω) b) b) (U ω)) :
    IdentDistrib (fun ω => (circleProcess (hcirc ω), familyProcess (Λ ω) (T ω)))
      (fun ω => (circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
        familyProcess (rescaledFamily (Γ ω) (coneScaleRadius γ (hcirc ω) b) b) (U ω))) P P := by
  have hs := hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb
  have hgood : ∀ᵐ ω ∂P,
      IsLocallyFiniteMeasure (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ∧
      ∃ βm βp, VolumeGrowth (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)
        (3 / 4) βm βp := by
    filter_upwards [hs, hcone.ae_rescaledVolumeGrowth_inside_unit hγ hγ2 h27 hscale hlqg
      hb (R := (3 / 4 : ℝ)) (by norm_num) (by norm_num)] with ω hω hv
    exact ⟨hω.2.isLocallyFiniteMeasure, hv⟩
  apply identDistrib_observable_halfBallFamily_of_measureLaw
    (hcone.identDistrib_rescaledCircleMeasure hγ hγ2 hscale hlqg hb).symm
    (hcone.ae_volumeGrowth_inside_unit hγ hγ2 h27 (by norm_num)) hgood
  · filter_upwards [hΛ, hgrow γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω hg
    exact ⟨hω.1, hω.2.1, hω.2.2, hg _ _ hω.2.1⟩
  · filter_upwards [hΓ, hs, hgrow γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω hR hg
    exact ⟨hω.1, coneHarmonicBallFamilyOnScalingStep (μ ω) (Γ ω) _ b (U ω)
      hR.1 hb hω.2.1, hω.2.2, (hg _ _ hω.2.1).rescaledFamily hb⟩

end MatedCRT
