import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.StoppingTime
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Obstacle

/-! # Measurability for rescaled stopped harmonic-ball families -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls TopologicalSpace

/-- A strictly growing stopped family is measurable whenever its measure is
measurable and has fixed-disk volume growth almost surely. -/
theorem aemeasurable_halfBallFamily_of_volumeGrowth
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hμ : AEMeasurable μ P)
    (hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) (3 / 4) βminus βplus)
    (hf : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω) ∧ IsStrictlyGrowingOn (Λ ω) (T ω)) :
    AEMeasurable (fun ω => familyProcess (Λ ω) (T ω)) P := by
  let C : Ω → Ioi (0 : ℝ) → Set ℂ := fun ω t =>
    interior (closure (cluster (μ ω) (3 / 4) 0 t))
  let curry : ((Ioi (0 : ℝ) × ℂ) → Prop) → Ioi (0 : ℝ) → Set ℂ :=
    fun F t x => F (t, x)
  have hcurry : Measurable curry := by
    apply Measurable.of_eval
    intro t
    apply Measurable.of_eval
    intro x
    exact measurable_pi_apply (t, x)
  have hcluster := aemeasurable_regularizedClusterFamily_of_volumeGrowth (by norm_num) hμ hgood
  have hCm : AEMeasurable C P := hcurry.comp_aemeasurable hcluster
  have hT : AEMeasurable T P := by
    apply aemeasurable_stoppingTime_of_open_family hCm
    filter_upwards [hf, hgood] with ω hω hv
    refine ⟨hω.1, (fun _ => isOpen_interior), ?_, ?_, hω.2.2.1, hω.2.2.2⟩
    · intro s t hst
      apply interior_mono (closure_mono ?_)
      obtain ⟨hμω, βm, βp, hV⟩ := hv
      exact cluster_subset_of_general obstacleMonotoneGeneral_holds
        obstacleCompatibilityShiftStep_holds hμω (by norm_num) hV
        (mem_ball_self (by norm_num)) s.property hst
    · intro t ht
      exact (hω.2.1.eq_threeQuarterDisk_cluster hω.2.2.1 ht).symm
  exact aemeasurable_familyProcess_of_positiveTime_cluster hT hcluster
    (hf.mono fun _ h => ⟨h.2.1, h.2.2.1⟩)

/-- The rescaled family is measurable once its rescaled measure is
measurable and has volume growth. -/
theorem aemeasurable_rescaledHalfBallPair_of_volumeGrowth
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (hgrow : ConeHarmonicBallStrictGrowthStep)
    {b : ℝ} (hb : 0 < b) {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hR : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b)
    (hμ : AEMeasurable (fun ω => rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) P)
    (hgood : ∀ᵐ ω ∂P,
      IsLocallyFiniteMeasure (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ∧
      ∃ βminus βplus, VolumeGrowth
        (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) (3 / 4) βminus βplus)
    (hcirc' : AEMeasurable (fun ω => circleProcess
      (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) P)
    (hf : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (b * T ω) ∧
      IsStoppedAtHalfBall (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) (T ω)) :
    AEMeasurable (fun ω => (circleProcess
      (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b),
      familyProcess (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) (T ω))) P := by
  apply hcirc'.prodMk
  apply aemeasurable_halfBallFamily_of_volumeGrowth hμ hgood
  filter_upwards [hf, hR, hgrow γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω hRω hg
  exact ⟨hω.1, coneHarmonicBallFamilyOnScalingStep (μ ω) (Λ ω) _ b (T ω)
    hRω hb hω.2.1, hω.2.2, (hg _ _ hω.2.1).rescaledFamily hb⟩

end MatedCRT
