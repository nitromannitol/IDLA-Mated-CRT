import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.FixedDisk
import HarmonicBalls.Proofs.Sec5.PotentialMeasurableDecoder
import HarmonicBalls.Proofs.Sec3.OpenLaplacian

/-! # Simultaneous measurability of fixed-disk obstacle clusters -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- A measurable random measure with volume growth has a single measurable
version of all positive-time clusters in a fixed disk. -/
theorem aemeasurable_clusterFamily_of_volumeGrowth
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {R : ℝ} (hR : 0 < R) (hμ : AEMeasurable μ P)
    (hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) R βminus βplus) :
    AEMeasurable (fun ω (p : Ioi (0 : ℝ) × ℂ) => p.2 ∈ cluster (μ ω) R 0 p.1) P := by
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_clusterFamily_of_volumeGrowth hR
  let z : ball (0 : ℂ) R := ⟨0, mem_ball_self hR⟩
  have hm : Measurable (fun ν : Measure ℂ => fun p : Ioi (0 : ℝ) × ℂ => p.2 ∈ F ν (z, p.1)) := by
    apply Measurable.of_eval
    intro p
    exact (measurable_pi_apply p.2).comp ((measurable_pi_apply (z, p.1)).comp hF)
  refine (hm.comp_aemeasurable hμ).congr ?_
  filter_upwards [hgood] with ω hω
  funext p
  dsimp only [Function.comp_apply]
  rw [hFeq (μ ω) hω.1 hω.2]

/-- Volume growth also gives a simultaneous measurable version of the
regularized clusters. -/
theorem aemeasurable_regularizedClusterFamily_of_volumeGrowth
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {R : ℝ} (hR : 0 < R) (hμ : AEMeasurable μ P)
    (hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) R βminus βplus) :
    AEMeasurable (fun ω (p : Ioi (0 : ℝ) × ℂ) =>
      p.2 ∈ interior (closure (cluster (μ ω) R 0 p.1))) P := by
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_clusterFamily_of_volumeGrowth hR
  let z : ball (0 : ℂ) R := ⟨0, mem_ball_self hR⟩
  have hm : Measurable (fun ν : Measure ℂ => fun p : Ioi (0 : ℝ) × ℂ =>
      p.2 ∈ denseSequenceRegularization (F ν (z, p.1))) := by
    apply Measurable.of_eval
    intro p
    exact (measurable_pi_apply p.2).comp
      (measurable_denseSequenceRegularization.comp ((measurable_pi_apply (z, p.1)).comp hF))
  refine (hm.comp_aemeasurable hμ).congr ?_
  filter_upwards [hgood] with ω hω
  funext p
  dsimp only [Function.comp_apply]
  have ho : IsOpen (cluster (μ ω) R 0 p.1) := by
    obtain ⟨hμω, βm, βp, hV⟩ := hω
    exact (cluster_open_laplacian_of_general greenFunctionBall
      obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
      obstacleCompatibilityShiftStep_holds hμω hR hV (mem_ball_self hR) p.1.property).1
  rw [hFeq (μ ω) hω.1 hω.2, denseSequenceRegularization_eq ho]

/-- The positive-time decoder and a measurable stopping time determine the
stopped family in one fixed disk. -/
theorem aemeasurable_familyProcess_of_positiveTime_cluster {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : Ω → Measure ℂ} {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hT : AEMeasurable T P)
    (hcluster : AEMeasurable (fun ω (p : Ioi (0 : ℝ) × ℂ) =>
      p.2 ∈ interior (closure (cluster (μ ω) (3 / 4) 0 p.1))) P)
    (hf : ∀ᵐ ω ∂P, IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω)) :
    AEMeasurable (fun ω => familyProcess (Λ ω) (T ω)) P := by
  classical
  let T' := hT.mk T
  let C' := hcluster.mk _
  let F : Ω → (ℝ × ℂ → Prop) := fun ω p =>
    if hp : 0 < p.1 then p.1 < T' ω ∧ C' ω (⟨p.1, hp⟩, p.2) else False
  have hmeas : Measurable F := by
    apply measurable_pi_iff.mpr
    intro p
    by_cases hp : 0 < p.1
    · simp only [F, hp, dite_true]
      apply measurableSet_setOfPred.mp
      exact (measurableSet_lt (measurable_const : Measurable fun _ : Ω => p.1)
        hT.measurable_mk).inter
        (measurableSet_setOfPred.mpr ((measurable_pi_apply ((⟨p.1, hp⟩ : Ioi (0 : ℝ)), p.2)).comp hcluster.measurable_mk))
    · simp [F, hp]
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hf, hT.ae_eq_mk, hcluster.ae_eq_mk] with ω hω hTω hCω
  funext p
  apply propext
  by_cases hp : 0 < p.1
  · simp only [F, hp, dite_true, familyProcess, mem_Ioo]
    dsimp only [T', C']
    rw [← hTω, ← hCω]
    constructor
    · rintro ⟨ht, hx⟩
      exact ⟨⟨trivial, ht⟩, by rw [hω.1.eq_threeQuarterDisk_cluster hω.2 ⟨hp, ht⟩]; exact hx⟩
    · rintro ⟨⟨_, ht⟩, hx⟩
      exact ⟨ht, by rw [hω.1.eq_threeQuarterDisk_cluster hω.2 ⟨hp, ht⟩] at hx; exact hx⟩
  · simp [F, hp, familyProcess]

end MatedCRT
