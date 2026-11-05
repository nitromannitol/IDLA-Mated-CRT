import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.HorizonLaw

/-! # Countable detection of premature half-ball contact -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace

/-- A countable test for an earlier cluster reaching every smaller half disk
while a later cluster is still contained in the closed half disk. -/
def halfBallPrematureContact (C : Ioi (0 : ℝ) → Set ℂ) : Prop :=
  ∃ q r : PositiveRational, (q : ℝ) < (r : ℝ) ∧
    ¬ halfBallTest (C ⟨q, q.property⟩) ∧
    ∀ n : ℕ, denseSeq ℂ n ∈ C ⟨r, r.property⟩ →
      denseSeq ℂ n ∈ closedBall (0 : ℂ) (1 / 2)

/-- Premature contact is measurable on the pointwise cluster path space. -/
theorem measurable_halfBallPrematureContact : Measurable halfBallPrematureContact := by
  unfold halfBallPrematureContact
  apply Measurable.exists
  intro q
  apply Measurable.exists
  intro r
  apply measurable_const.and
  apply (measurable_halfBallTest.comp (measurable_pi_apply (⟨q, q.property⟩ : Ioi (0 : ℝ)))).not.and
  apply Measurable.forall
  intro n
  exact ((measurable_pi_apply (denseSeq ℂ n)).comp (measurable_pi_apply (⟨r, r.property⟩ : Ioi (0 : ℝ)))).imp measurable_const

/-- Two distinct stopped horizons produce the countable premature-contact
witness in any open path that represents both stopped families. -/
theorem halfBallPrematureContact_of_distinct_horizons
    {μ : Measure ℂ} {C : Ioi (0 : ℝ) → Set ℂ}
    {T S : ℝ} {Λ Γ : ℝ → Set ℂ}
    (_hT : 0 < T) (hΛ : IsConeHarmonicBallFamilyOn μ Λ T) (hsΛ : IsStoppedAtHalfBall Λ T)
    (hS : 0 < S) (hΓ : IsConeHarmonicBallFamilyOn μ Γ S) (hsΓ : IsStoppedAtHalfBall Γ S)
    (hST : S < T) (ho : ∀ t, IsOpen (C t))
    (heq : ∀ t (ht : t ∈ Ioo 0 T), C ⟨t, ht.1⟩ = Λ t) :
    halfBallPrematureContact C := by
  obtain ⟨q, hSq, hqT⟩ := exists_rat_btwn hST
  obtain ⟨r, hqr, hrT⟩ := exists_rat_btwn hqT
  have hq0 : 0 < (q : ℝ) := hS.trans hSq
  have hr0 : 0 < (r : ℝ) := hq0.trans hqr
  let q' : PositiveRational := ⟨q, hq0⟩
  let r' : PositiveRational := ⟨r, hr0⟩
  refine ⟨q', r', hqr, ?_, ?_⟩
  · rintro ⟨ρ, hρ, htest⟩
    obtain ⟨ρ', hρρ', hρ'⟩ := exists_rat_btwn hρ
    obtain ⟨t, ht, hnot⟩ := hsΓ.2 ρ' hρ'
    have htT : t ∈ Ioo 0 T := ⟨ht.1, ht.2.trans hST⟩
    have htmin : t ∈ Ioo 0 (min T S) := ⟨ht.1, lt_min htT.2 ht.2⟩
    have he : Γ t = Λ t := hΛ.eqOn hΓ htmin
    have hsub := closure_subset_closedBall_of_halfBallTest
      (ho ⟨q, hq0⟩) htest
    apply hnot
    intro x hx
    have hxΛ : x ∈ Λ t := he ▸ hx
    have hxq : x ∈ Λ q := hΛ.2.1.monotoneOn htT ⟨hq0, hqT⟩
      (le_of_lt (ht.2.trans hSq)) hxΛ
    have hxC : x ∈ C ⟨q, hq0⟩ := by rwa [heq q ⟨hq0, hqT⟩]
    exact (hsub (subset_closure hxC)).trans_lt hρρ'
  · intro n hn
    have hnΛ : denseSeq ℂ n ∈ Λ r := by rwa [← heq r ⟨hr0, hrT⟩]
    exact ball_subset_closedBall (hsΛ.1 r ⟨hr0, hrT⟩ hnΛ)

/-- Failure of horizon uniqueness is contained in a measurable event built
from the fixed-disc obstacle decoder, on measures with volume growth. -/
theorem exists_measurable_prematureContact_cover :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βm βp, VolumeGrowth ν (3 / 4) βm βp) →
      ν ∉ E → ν ∈ halfBallHorizonUniqueMeasures := by
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
  let E : Set (Measure ℂ) := {ν | halfBallPrematureContact (C ν)}
  refine ⟨E, measurableSet_setOfPred.mpr (measurable_halfBallPrematureContact.comp hC), ?_⟩
  intro ν hloc hvol hnot T S Λ Γ hT hΛ hsΛ hS hΓ hsΓ
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
  have ho : ∀ t, IsOpen (C ν t) := fun t => by rw [hCeq]; exact isOpen_interior
  have heqΛ : ∀ t (ht : t ∈ Ioo 0 T), C ν ⟨t, ht.1⟩ = Λ t := by
    intro t ht
    rw [hCeq]
    exact (hΛ.eq_threeQuarterDisk_cluster hsΛ ht).symm
  have heqΓ : ∀ t (ht : t ∈ Ioo 0 S), C ν ⟨t, ht.1⟩ = Γ t := by
    intro t ht
    rw [hCeq]
    exact (hΓ.eq_threeQuarterDisk_cluster hsΓ ht).symm
  rcases lt_trichotomy S T with hST | hST | hST
  · exact False.elim (hnot (halfBallPrematureContact_of_distinct_horizons
      hT hΛ hsΛ hS hΓ hsΓ hST ho heqΛ))
  · exact hST
  · exact False.elim (hnot (halfBallPrematureContact_of_distinct_horizons
      hS hΓ hsΓ hT hΛ hsΛ hST ho heqΓ))

end MatedCRT
