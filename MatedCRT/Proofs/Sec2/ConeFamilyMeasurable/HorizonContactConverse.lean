import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.HorizonContact

/-! # A converse to premature contact for valid local families -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls TopologicalSpace

/-- If an open decoded path has premature contact and is a valid cone
harmonic-ball family up to the later rational time, it admits two different
stopping horizons. -/
theorem exists_distinct_stopped_horizons_of_prematureContact
    {μ : Measure ℂ} {C : Ioi (0 : ℝ) → Set ℂ}
    (ho : ∀ t, IsOpen (C t)) (hm : Monotone C)
    (hvalid : ∀ r : PositiveRational,
      (∀ n : ℕ, denseSeq ℂ n ∈ C ⟨r, r.property⟩ →
        denseSeq ℂ n ∈ closedBall (0 : ℂ) (1 / 2)) →
      ∃ Λ : ℝ → Set ℂ, IsConeHarmonicBallFamilyOn μ Λ r ∧
        ∀ t (ht : t ∈ Ioo 0 (r : ℝ)), C ⟨t, ht.1⟩ = Λ t)
    (hcontact : halfBallPrematureContact C) : μ ∉ halfBallHorizonUniqueMeasures := by
  obtain ⟨q, r, hqr, hq, hr⟩ := hcontact
  obtain ⟨Λ, hf, heq⟩ := hvalid r hr
  have hrsub : C ⟨r, r.property⟩ ⊆ ball (0 : ℂ) (1 / 2) := by
    have hc := closure_subset_closedBall_of_halfBallTest (ho ⟨r, r.property⟩) hr
    have hi : C ⟨r, r.property⟩ ⊆ interior (closedBall (0 : ℂ) (1 / 2)) :=
      interior_maximal (subset_closure.trans hc) (ho ⟨r, r.property⟩)
    simpa only [interior_closedBall (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)] using hi
  have hqcontact : ∀ ρ : ℝ, ρ < 1 / 2 → ¬ Λ q ⊆ ball 0 ρ := by
    intro ρ hρ hsub
    obtain ⟨ρ', hρρ', hρ'⟩ := exists_rat_btwn hρ
    apply hq
    refine ⟨ρ', hρ', fun n hn => ?_⟩
    have hnΛ : denseSeq ℂ n ∈ Λ q := by rwa [← heq q ⟨q.property, hqr⟩]
    exact le_of_lt ((hsub hnΛ).trans hρρ')
  obtain ⟨V, hqV, hVr⟩ := exists_between hqr
  obtain ⟨S, hqS, hSV⟩ := exists_between hqV
  have hS : 0 < S := q.property.trans hqS
  have hV : 0 < V := hS.trans hSV
  have hstop : ∀ H : ℝ, (q : ℝ) < H → H ≤ r → IsStoppedAtHalfBall Λ H := by
    intro H hqH hHr
    refine ⟨?_, ?_⟩
    · intro t ht
      have htr : t < (r : ℝ) := ht.2.trans_le hHr
      intro x hx
      have hxC : x ∈ C ⟨t, ht.1⟩ := by rwa [heq t ⟨ht.1, htr⟩]
      exact hrsub (hm (show (⟨t, ht.1⟩ : Ioi (0 : ℝ)) ≤ ⟨r, r.property⟩ from htr.le) hxC)
    · intro ρ hρ
      exact ⟨q, ⟨q.property, hqH⟩, hqcontact ρ hρ⟩
  intro hu
  have heqSV := hu V S Λ Λ hV (hf.restrict_time hV hVr.le) (hstop V hqV hVr.le)
    hS (hf.restrict_time hS (le_of_lt (hSV.trans hVr))) (hstop S hqS (le_of_lt (hSV.trans hVr)))
  exact (ne_of_lt hSV) heqSV

end MatedCRT
