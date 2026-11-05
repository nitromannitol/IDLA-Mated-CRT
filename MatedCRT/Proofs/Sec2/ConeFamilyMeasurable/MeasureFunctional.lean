import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.MeasureLaw

/-! # The stopped family as a measurable functional of the measure -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls TopologicalSpace ProbabilityTheory

/-- One measurable functional of a locally finite measure represents every
strictly growing harmonic-ball family stopped on reaching the half disk,
provided the measure satisfies volume growth on the three-quarter disk. -/
theorem exists_measurable_halfBallFamily_of_volumeGrowth :
    ∃ F : Measure ℂ → (ℝ × ℂ → Prop), Measurable F ∧
      ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν (3 / 4) βm βp) →
        ∀ (T : ℝ) (Λ : ℝ → Set ℂ), 0 < T →
          IsConeHarmonicBallFamilyOn ν Λ T → IsStoppedAtHalfBall Λ T →
          IsStrictlyGrowingOn Λ T → F ν = familyProcess Λ T := by
  classical
  obtain ⟨A, hA, hAeq⟩ := exists_measurable_clusterFamily_of_volumeGrowth
    (R := (3 / 4 : ℝ)) (by norm_num)
  let z : ball (0 : ℂ) (3 / 4) := ⟨0, mem_ball_self (by norm_num)⟩
  let C : Measure ℂ → Ioi (0 : ℝ) → Set ℂ := fun ν t =>
    denseSequenceRegularization (A ν (z, t))
  have hC : Measurable C := by
    apply Measurable.of_eval
    intro t
    exact measurable_denseSequenceRegularization.comp ((measurable_pi_apply (z, t)).comp hA)
  let H : Measure ℂ → ℝ := fun ν => (halfBallTestHorizon (C ν)).toReal
  have hH : Measurable H := (measurable_halfBallTestHorizon.comp hC).ennreal_toReal
  let F : Measure ℂ → (ℝ × ℂ → Prop) := fun ν p =>
    if hp : 0 < p.1 then p.1 < H ν ∧ p.2 ∈ C ν ⟨p.1, hp⟩ else False
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro p
    by_cases hp : 0 < p.1
    · simp only [F, hp, dite_true]
      apply measurableSet_setOfPred.mp
      exact (measurableSet_lt (measurable_const : Measurable fun _ : Measure ℂ => p.1) hH).inter
        (measurableSet_setOfPred.mpr ((measurable_pi_apply p.2).comp
          ((measurable_pi_apply (⟨p.1, hp⟩ : Ioi (0 : ℝ))).comp hC)))
    · simp [F, hp]
  refine ⟨F, hF, ?_⟩
  intro ν hloc hvol T Λ hT hf hs hg
  have hCeq (t : Ioi (0 : ℝ)) : C ν t =
      interior (closure (cluster ν (3 / 4) 0 t)) := by
    have hcluster := congrFun (hAeq ν hloc hvol) (z, t)
    have hopen : IsOpen (cluster ν (3 / 4) 0 t) := by
      obtain ⟨βm, βp, hV⟩ := hvol
      exact (cluster_open_laplacian_of_general greenFunctionBall
        obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
        obstacleCompatibilityShiftStep_holds hloc (by norm_num) hV
        (mem_ball_self (by norm_num)) t.property).1
    simp only [C, hcluster, z]
    exact denseSequenceRegularization_eq hopen
  have hmono : Monotone (C ν) := by
    intro s t hst
    rw [hCeq s, hCeq t]
    apply interior_mono (closure_mono ?_)
    obtain ⟨βm, βp, hV⟩ := hvol
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds
      obstacleCompatibilityShiftStep_holds hloc (by norm_num) hV
      (mem_ball_self (by norm_num)) s.property hst
  have heq : ∀ t (ht : t ∈ Ioo 0 T), C ν ⟨t, ht.1⟩ = Λ t := by
    intro t ht
    rw [hCeq]
    exact (hf.eq_threeQuarterDisk_cluster hs ht).symm
  have htest : ∀ q : PositiveRational, halfBallTest (C ν ⟨q, q.property⟩) ↔ (q : ℝ) < T :=
    fun q => halfBallTest_iff_lt (fun t => by rw [hCeq]; exact isOpen_interior) hmono heq hs hg q
  have hHν : H ν = T := by
    have hh := congrArg ENNReal.toReal (halfBallTestHorizon_eq htest)
    simpa only [H, ENNReal.toReal_ofReal hT.le] using hh
  funext p
  apply propext
  by_cases hp : 0 < p.1
  · simp only [F, hp, dite_true, hHν, familyProcess, mem_Ioo]
    constructor
    · rintro ⟨ht, hx⟩
      exact ⟨⟨trivial, ht⟩, by rw [← heq p.1 ⟨hp, ht⟩]; exact hx⟩
    · rintro ⟨⟨_, ht⟩, hx⟩
      exact ⟨ht, by rw [heq p.1 ⟨hp, ht⟩]; exact hx⟩
  · simp [F, hp, familyProcess]

/-- Stopped families of identically distributed measures have the same law
when both families are strictly growing and the measures have volume growth. -/
theorem identDistrib_halfBallFamily_of_measureLaw
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ ν : Ω → Measure ℂ}
    {T U : Ω → ℝ} {Λ Γ : Ω → ℝ → Set ℂ}
    (hμν : IdentDistrib μ ν P P)
    (hμ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βm βp, VolumeGrowth (μ ω) (3 / 4) βm βp)
    (hν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) ∧
      ∃ βm βp, VolumeGrowth (ν ω) (3 / 4) βm βp)
    (hΛ : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω) ∧ IsStrictlyGrowingOn (Λ ω) (T ω))
    (hΓ : ∀ᵐ ω ∂P, 0 < U ω ∧ IsConeHarmonicBallFamilyOn (ν ω) (Γ ω) (U ω) ∧
      IsStoppedAtHalfBall (Γ ω) (U ω) ∧ IsStrictlyGrowingOn (Γ ω) (U ω)) :
    IdentDistrib (fun ω => familyProcess (Λ ω) (T ω))
      (fun ω => familyProcess (Γ ω) (U ω)) P P := by
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_halfBallFamily_of_volumeGrowth
  have hD := hμν.comp hF
  have hleft : ∀ᵐ ω ∂P, F (μ ω) = familyProcess (Λ ω) (T ω) := by
    filter_upwards [hμ, hΛ] with ω hm hf
    exact hFeq _ hm.1 hm.2 _ _ hf.1 hf.2.1 hf.2.2.1 hf.2.2.2
  have hright : ∀ᵐ ω ∂P, F (ν ω) = familyProcess (Γ ω) (U ω) := by
    filter_upwards [hν, hΓ] with ω hm hf
    exact hFeq _ hm.1 hm.2 _ _ hf.1 hf.2.1 hf.2.2.1 hf.2.2.2
  exact ((IdentDistrib.of_ae_eq hD.aemeasurable_fst hleft).symm.trans hD).trans
    (IdentDistrib.of_ae_eq hD.aemeasurable_snd hright)

/-- Joint laws of a field observable and its stopped family agree when the
observable and underlying measure have the same joint law. -/
theorem identDistrib_observable_halfBallFamily_of_measureLaw
    {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {x y : Ω → X} {μ ν : Ω → Measure ℂ}
    {T U : Ω → ℝ} {Λ Γ : Ω → ℝ → Set ℂ}
    (hxy : IdentDistrib (fun ω => (x ω, μ ω)) (fun ω => (y ω, ν ω)) P P)
    (hμ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βm βp, VolumeGrowth (μ ω) (3 / 4) βm βp)
    (hν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) ∧
      ∃ βm βp, VolumeGrowth (ν ω) (3 / 4) βm βp)
    (hΛ : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω) ∧ IsStrictlyGrowingOn (Λ ω) (T ω))
    (hΓ : ∀ᵐ ω ∂P, 0 < U ω ∧ IsConeHarmonicBallFamilyOn (ν ω) (Γ ω) (U ω) ∧
      IsStoppedAtHalfBall (Γ ω) (U ω) ∧ IsStrictlyGrowingOn (Γ ω) (U ω)) :
    IdentDistrib (fun ω => (x ω, familyProcess (Λ ω) (T ω)))
      (fun ω => (y ω, familyProcess (Γ ω) (U ω))) P P := by
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_halfBallFamily_of_volumeGrowth
  have hD := hxy.comp (measurable_fst.prodMk (hF.comp measurable_snd))
  have hleft : ∀ᵐ ω ∂P, (x ω, F (μ ω)) = (x ω, familyProcess (Λ ω) (T ω)) := by
    filter_upwards [hμ, hΛ] with ω hm hf
    exact congrArg (Prod.mk (x ω)) (hFeq _ hm.1 hm.2 _ _ hf.1 hf.2.1 hf.2.2.1 hf.2.2.2)
  have hright : ∀ᵐ ω ∂P, (y ω, F (ν ω)) = (y ω, familyProcess (Γ ω) (U ω)) := by
    filter_upwards [hν, hΓ] with ω hm hf
    exact congrArg (Prod.mk (y ω)) (hFeq _ hm.1 hm.2 _ _ hf.1 hf.2.1 hf.2.2.1 hf.2.2.2)
  exact ((IdentDistrib.of_ae_eq hD.aemeasurable_fst hleft).symm.trans hD).trans
    (IdentDistrib.of_ae_eq hD.aemeasurable_snd hright)

/-- The stopped cone family has the same law after quantum-cone rescaling,
provided both families satisfy their defining conditions. -/
theorem IsConeField.identDistrib_rescaledHalfBallFamily
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
    IdentDistrib (fun ω => familyProcess (Λ ω) (T ω))
      (fun ω => familyProcess (rescaledFamily (Γ ω) (coneScaleRadius γ (hcirc ω) b) b) (U ω)) P P := by
  have hs := hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb
  have hgood : ∀ᵐ ω ∂P,
      IsLocallyFiniteMeasure (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ∧
      ∃ βm βp, VolumeGrowth (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)
        (3 / 4) βm βp := by
    filter_upwards [hs, hcone.ae_rescaledVolumeGrowth_inside_unit hγ hγ2 h27 hscale hlqg
      hb (R := (3 / 4 : ℝ)) (by norm_num) (by norm_num)] with ω hω hv
    exact ⟨hω.2.isLocallyFiniteMeasure, hv⟩
  apply identDistrib_halfBallFamily_of_measureLaw
    (hcone.identDistrib_rescaledMeasure hγ hγ2 hscale hlqg hb).symm
    (hcone.ae_volumeGrowth_inside_unit hγ hγ2 h27 (by norm_num)) hgood
  · filter_upwards [hΛ, hgrow γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω hg
    exact ⟨hω.1, hω.2.1, hω.2.2, hg _ _ hω.2.1⟩
  · filter_upwards [hΓ, hs, hgrow γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω hR hg
    exact ⟨hω.1, coneHarmonicBallFamilyOnScalingStep (μ ω) (Γ ω) _ b (U ω)
      hR.1 hb hω.2.1, hω.2.2, (hg _ _ hω.2.1).rescaledFamily hb⟩

end MatedCRT
