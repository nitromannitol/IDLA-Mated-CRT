import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ContactEvent
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.StoppedClosure

/-! # Closure containment before the stopping time (written argument, draft lines 275-304)

Written argument: `notes/prop42-proof/prop42-proof.tex`, theorem `t:closure` (lines 275-304). Its probabilistic input is
the plateau lemma `l:plateau` (lines 230-274). The rational form of the excluded event is `halfBallPrematureContact`
(`HorizonContact.lean`): an earlier rational cluster reaches the half circle while a later rational cluster lies in
the closed half disk.

This file proves the deterministic part (draft lines 291-304). If the raw `3/4`-clusters of `ν` have no premature
contact, then every family `Λ` stopped at `T` for `ν` satisfies `closure (Λ t) ⊆ B_{1/2}` for `0 < t < T`. The
probabilistic input is the Prop `ConePrematureContactNullStep` (draft lines 275-289). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace

/-- Closure containment before the stopping time from the absence of premature contact (draft lines 291-304). If
`closure (Λ t)` met the circle `∂B_{1/2}` at some `t < T`, monotonicity would give the rational times
`t < q₁ < q₂ < T`, with `Λ_{q₁}` meeting the circle and `Λ_{q₂} ⊆ B_{1/2}`: this is premature contact of the raw
`3/4`-clusters. -/
theorem closure_subset_ball_of_not_halfBallPrematureContact {ν : Measure ℂ} {Λ : ℝ → Set ℂ} {T : ℝ}
    (hf : IsConeHarmonicBallFamilyOn ν Λ T) (hs : IsStoppedAtHalfBall Λ T)
    (hnot : ¬ halfBallPrematureContact
      (fun t : Ioi (0 : ℝ) => interior (closure (cluster ν (3 / 4) 0 t)))) :
    ∀ t ∈ Ioo 0 T, closure (Λ t) ⊆ ball (0 : ℂ) (1 / 2) := by
  intro t ht
  by_contra hcl
  obtain ⟨x, hxcl, hxout⟩ := Set.not_subset.mp hcl
  have hxge : (1 / 2 : ℝ) ≤ dist x 0 := not_lt.mp fun h => hxout (mem_ball.mpr h)
  obtain ⟨q1, hq1t, hq1T⟩ := exists_rat_btwn ht.2
  obtain ⟨q2, hq12, hq2T⟩ := exists_rat_btwn hq1T
  have hq1pos : (0 : ℝ) < q1 := ht.1.trans hq1t
  have hq2pos : (0 : ℝ) < q2 := hq1pos.trans hq12
  have hC1 : interior (closure (cluster ν (3 / 4) 0 (q1 : ℝ))) = Λ q1 :=
    (hf.eq_threeQuarterDisk_cluster hs (show (q1 : ℝ) ∈ Ioo 0 T from ⟨hq1pos, hq1T⟩)).symm
  have hC2 : interior (closure (cluster ν (3 / 4) 0 (q2 : ℝ))) = Λ q2 :=
    (hf.eq_threeQuarterDisk_cluster hs (show (q2 : ℝ) ∈ Ioo 0 T from ⟨hq2pos, hq2T⟩)).symm
  refine hnot ⟨⟨q1, hq1pos⟩, ⟨q2, hq2pos⟩, hq12, ?_, ?_⟩
  · rintro ⟨r', hr', hdense⟩
    have hdense' : ∀ n : ℕ, denseSeq ℂ n ∈ interior (closure (cluster ν (3 / 4) 0 (q1 : ℝ))) →
        denseSeq ℂ n ∈ closedBall (0 : ℂ) (r' : ℝ) := hdense
    have hcl1 := closure_subset_closedBall_of_halfBallTest isOpen_interior hdense'
    have hsub : Λ t ⊆ interior (closure (cluster ν (3 / 4) 0 (q1 : ℝ))) := by
      rw [hC1]
      exact hf.2.1.monotoneOn ht (show (q1 : ℝ) ∈ Ioo 0 T from ⟨hq1pos, hq1T⟩) hq1t.le
    have hxr : x ∈ closedBall (0 : ℂ) (r' : ℝ) := hcl1 (closure_mono hsub hxcl)
    have hxr' := mem_closedBall.mp hxr
    linarith
  · intro n hn
    have hn' : denseSeq ℂ n ∈ Λ q2 := by
      rw [← hC2]
      exact hn
    exact ball_subset_closedBall (hs.1 (q2 : ℝ) ⟨hq2pos, hq2T⟩ hn')

/-- **No premature contact of the cone clusters** (draft lines 275-289, with the plateau lemma of lines 230-274 as its
probabilistic input): almost surely, the raw `3/4`-clusters of the cone measure have no premature half-ball contact. -/
def ConePrematureContactNullStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∀ᵐ ω ∂P, ¬ halfBallPrematureContact
      (fun t : Ioi (0 : ℝ) => interior (closure (cluster (μ ω) (3 / 4) 0 t)))

/-- **Closure step** (`ConeHalfBallClosureInsideStep`, `StoppedClosure.lean:18`), derived from the absence of premature
contact by the deterministic argument above. -/
theorem coneHalfBallClosureInsideStep_of_prematureContactNull (h : ConePrematureContactNullStep) :
    ConeHalfBallClosureInsideStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  filter_upwards [h γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω
  intro T Λ hf hs t ht
  exact closure_subset_ball_of_not_halfBallPrematureContact hf hs hω t ht

end MatedCRT
