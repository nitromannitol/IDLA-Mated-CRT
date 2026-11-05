import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.HorizonContactConverse

/-! # Measurability of fixed-disc premature contact -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls TopologicalSpace

/-- A measurable set detects premature contact of the regularized fixed-disc
clusters for every locally finite measure satisfying the volume-growth bound. -/
theorem exists_measurable_halfBallPrematureContact :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βm βp, VolumeGrowth ν (3 / 4) βm βp) →
      (ν ∈ E ↔ halfBallPrematureContact (fun t : Ioi (0 : ℝ) =>
        interior (closure (cluster ν (3 / 4) 0 t)))) := by
  classical
  obtain ⟨A, hA, hAeq⟩ := exists_measurable_clusterFamily_of_volumeGrowth
    (R := (3 / 4 : ℝ)) (by norm_num)
  let z : ball (0 : ℂ) (3 / 4) := ⟨0, mem_ball_self (by norm_num)⟩
  let C : Measure ℂ → Ioi (0 : ℝ) → Set ℂ := fun ν t =>
    denseSequenceRegularization (A ν (z, t))
  have hC : Measurable C := by
    apply Measurable.of_eval
    intro t
    exact measurable_denseSequenceRegularization.comp
      ((measurable_pi_apply (z, t)).comp hA)
  refine ⟨{ν | halfBallPrematureContact (C ν)},
    measurableSet_setOfPred.mpr (measurable_halfBallPrematureContact.comp hC), ?_⟩
  intro ν hloc hvol
  have heq : C ν = fun t : Ioi (0 : ℝ) =>
      interior (closure (cluster ν (3 / 4) 0 t)) := by
    funext t
    have hcluster := congrFun (hAeq ν hloc hvol) (z, t)
    have hopen : IsOpen (cluster ν (3 / 4) 0 t) := by
      obtain ⟨βm, βp, hV⟩ := hvol
      exact (cluster_open_laplacian_of_general greenFunctionBall
        obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
        obstacleCompatibilityShiftStep_holds hloc (by norm_num) hV
        (mem_ball_self (by norm_num)) t.property).1
    simp only [C, hcluster, z]
    exact denseSequenceRegularization_eq hopen
  simp only [mem_ofPred_eq, heq]

/-- Under local validity of the fixed-disc clusters, the measurable contact
set detects exactly the failure of stopped-horizon uniqueness. -/
theorem exists_measurable_halfBallHorizonNonunique_of_local_validity :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βm βp, VolumeGrowth ν (3 / 4) βm βp) →
      (∀ r : PositiveRational,
        (∀ n : ℕ, denseSeq ℂ n ∈ interior (closure (cluster ν (3 / 4) 0 r)) →
          denseSeq ℂ n ∈ closedBall (0 : ℂ) (1 / 2)) →
        ∃ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn ν Λ r ∧
          ∀ t (_ht : t ∈ Ioo 0 (r : ℝ)),
            interior (closure (cluster ν (3 / 4) 0 t)) = Λ t) →
      (ν ∈ E ↔ ν ∉ halfBallHorizonUniqueMeasures) := by
  obtain ⟨E, hE, htest⟩ := exists_measurable_halfBallPrematureContact
  refine ⟨E, hE, ?_⟩
  intro ν hloc hvol hvalid
  rw [htest ν hloc hvol]
  let C : Ioi (0 : ℝ) → Set ℂ := fun t => interior (closure (cluster ν (3 / 4) 0 t))
  have ho : ∀ t, IsOpen (C t) := fun _ => isOpen_interior
  have hm : Monotone C := by
    intro s t hst
    apply interior_mono (closure_mono ?_)
    obtain ⟨βm, βp, hV⟩ := hvol
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds
      obstacleCompatibilityShiftStep_holds hloc (by norm_num) hV
      (mem_ball_self (by norm_num)) s.property hst
  have hrep : ∀ (T : ℝ) (Λ : ℝ → Set ℂ), 0 < T →
      IsConeHarmonicBallFamilyOn ν Λ T → IsStoppedAtHalfBall Λ T →
      ∀ t (ht : t ∈ Ioo 0 T), C ⟨t, ht.1⟩ = Λ t := by
    intro T Λ _ hf hs t ht
    exact (hf.eq_threeQuarterDisk_cluster hs ht).symm
  exact halfBallPrematureContact_iff_not_unique_of_local_validity ho hm hvalid hrep

end MatedCRT
