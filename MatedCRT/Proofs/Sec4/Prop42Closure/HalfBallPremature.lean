import MatedCRT.Proofs.Sec4.Prop42Closure.HalfBallPlateau
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.HorizonContact

/-! # Premature contact forces a half-ball plateau (closure of Proposition 4.2, z5)

Pointwise (deterministic) part of the whole-plane side of `t:closure` (draft lines 275-289): if the raw `3/4`-clusters
`C_t = interior (closure (cluster ν (3/4) 0 t))` of a measure `ν` have premature half-ball contact
(`halfBallPrematureContact`), then the global harmonic-ball family `Λ` of `ν` has the plateau value `1/2`
(`plateauValues`, draft lines 237-242).

Inputs, all pointwise: monotonicity of `Λ` (draft line 277 "monotonicity"), the compatibility of the global family with
the `3/4`-clusters ([HB] Lemma 5.8, `ClusterStrongCompatibilityStmt`, applied at `z = 0`, `U = B_{3/4}`), and the openness
of the raw clusters ([HB] `ClusterOpenLaplacianStmt`). -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace

/-- The cluster of a ball is the cluster on the ball (`Λ_{B_r;z}(t)`, the two definitions of `clusterOn` and `cluster`
agree for `r ≠ 0`: the supersolutions on `B_r` are the same, since `closure (ball 0 r) = closedBall 0 r`). -/
theorem clusterOn_ball_eq_cluster_of_ne (μ : Measure ℂ) {r : ℝ} (hr : r ≠ 0) (z : ℂ) (t : ℝ) :
    clusterOn μ (ball (0 : ℂ) r) z t = cluster μ r z t := by
  have hsup : supersolutionsOn μ (ball (0 : ℂ) r) z t = supersolutions μ r z t := by
    unfold supersolutionsOn supersolutions
    rw [closure_ball (0 : ℂ) hr]
  unfold clusterOn cluster leastSupersolutionOn leastSupersolution
  rw [hsup]

/-- The closure of the interior of the closure of an open set is the closure of the set. -/
theorem closure_interior_closure_of_isOpen {S : Set ℂ} (hS : IsOpen S) :
    closure (interior (closure S)) = closure S :=
  le_antisymm (closure_minimal interior_subset isClosed_closure)
    (closure_mono (interior_maximal subset_closure hS))

/-- A family radius equals `c` when its points have norm at most `c` and approach `c` (`R_h = sup |x|`). -/
theorem familyRadius_eq_of_bounds {Λ : Set ℂ} {c : ℝ} (hne : Λ.Nonempty) (hle : ∀ x ∈ Λ, ‖x‖ ≤ c)
    (hlt : ∀ w < c, ∃ x ∈ Λ, w < ‖x‖) : familyRadius Λ = c := by
  unfold familyRadius
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (hne.image _)
  · rintro _ ⟨x, hx, rfl⟩
    exact hle x hx
  · intro w hw
    obtain ⟨x, hx, hwx⟩ := hlt w hw
    exact ⟨‖x‖, ⟨x, hx, rfl⟩, hwx⟩

/-- A point of the closure of a set with norm above `s` is approximated by points of the set with norm above `s`. -/
theorem exists_mem_norm_gt_of_mem_closure {Λ : Set ℂ} {x : ℂ} {s : ℝ} (hx : x ∈ closure Λ) (hs : s < ‖x‖) :
    ∃ y ∈ Λ, s < ‖y‖ := by
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hx (‖x‖ - s) (sub_pos.mpr hs)
  refine ⟨y, hy, ?_⟩
  have h2 : ‖x - y‖ < ‖x‖ - s := by rwa [← dist_eq_norm]
  have h1 := norm_sub_norm_le x y
  linarith

/-- The closed half ball is contained in the open ball of radius `3/4`. -/
theorem closedBall_half_subset_ball_three_quarter :
    closedBall (0 : ℂ) (1 / 2) ⊆ ball (0 : ℂ) (3 / 4) := by
  intro x hx
  rw [mem_closedBall, dist_zero_right] at hx
  rw [mem_ball, dist_zero_right]
  linarith

/-- **Premature contact forces the half-ball plateau** (pointwise form of draft lines 275-289 on the whole-plane side).
If the raw `3/4`-clusters of `ν` have premature half-ball contact, then `1/2` is a plateau value of the global family
`Λ` of `ν`: the two rational times `q < r` give `R(q) = R(r) = 1/2`. -/
theorem plateau_of_prematureContact {ν : Measure ℂ} {Λ : ℝ → Set ℂ}
    (hmono : ∀ s t : ℝ, 0 < s → s ≤ t → Λ s ⊆ Λ t)
    (hcomp : ∀ t : ℝ, 0 < t →
      (closure (Λ t) ⊆ ball (0 : ℂ) (3 / 4) ∨
        closure (clusterOn ν (ball (0 : ℂ) (3 / 4)) 0 t) ⊆ ball (0 : ℂ) (3 / 4)) →
      closure (Λ t) = closure (clusterOn ν (ball (0 : ℂ) (3 / 4)) 0 t))
    (hopen : ∀ t : ℝ, 0 < t → IsOpen (cluster ν (3 / 4) 0 t))
    (hpre : halfBallPrematureContact (fun t : Ioi (0 : ℝ) => interior (closure (cluster ν (3 / 4) 0 t)))) :
    (1 / 2 : ℝ) ∈ plateauValues Λ := by
  unfold halfBallPrematureContact at hpre
  obtain ⟨q, r, hqr, hnot, hbound⟩ := hpre
  set qR : ℝ := (q.1 : ℝ) with hqR
  set rR : ℝ := (r.1 : ℝ) with hrR
  have hq : (0 : ℝ) < qR := q.2
  have hr : (0 : ℝ) < rR := r.2
  have hnot' : ¬ halfBallTest (interior (closure (cluster ν (3 / 4) 0 qR))) := hnot
  have hbound' : ∀ n : ℕ, denseSeq ℂ n ∈ interior (closure (cluster ν (3 / 4) 0 rR)) →
      denseSeq ℂ n ∈ closedBall (0 : ℂ) (1 / 2) := hbound
  -- the later raw cluster lies in the closed half ball, hence so does its closure
  have hCr : closure (interior (closure (cluster ν (3 / 4) 0 rR))) ⊆ closedBall (0 : ℂ) (1 / 2) :=
    closure_subset_closedBall_of_halfBallTest isOpen_interior hbound'
  have hball_r : closure (clusterOn ν (ball (0 : ℂ) (3 / 4)) 0 rR) ⊆ ball (0 : ℂ) (3 / 4) := by
    rw [clusterOn_ball_eq_cluster_of_ne ν (r := 3 / 4) (by norm_num), ← closure_interior_closure_of_isOpen (hopen rR hr)]
    exact hCr.trans closedBall_half_subset_ball_three_quarter
  have hΛr : closure (Λ rR) = closure (interior (closure (cluster ν (3 / 4) 0 rR))) := by
    rw [hcomp rR hr (Or.inr hball_r), clusterOn_ball_eq_cluster_of_ne ν (r := 3 / 4) (by norm_num),
      closure_interior_closure_of_isOpen (hopen rR hr)]
  have hΛr_sub : closure (Λ rR) ⊆ closedBall (0 : ℂ) (1 / 2) := by
    rw [hΛr]
    exact hCr
  have hΛq_sub : closure (Λ qR) ⊆ ball (0 : ℂ) (3 / 4) :=
    (closure_mono (hmono qR rR hq hqr.le)).trans (hΛr_sub.trans closedBall_half_subset_ball_three_quarter)
  have hΛq : closure (Λ qR) = closure (interior (closure (cluster ν (3 / 4) 0 qR))) := by
    rw [hcomp qR hq (Or.inl hΛq_sub), clusterOn_ball_eq_cluster_of_ne ν (r := 3 / 4) (by norm_num),
      closure_interior_closure_of_isOpen (hopen qR hq)]
  -- upper bounds: every point of the family up to time `r` has norm at most `1/2`
  have hup_r : ∀ x ∈ Λ rR, ‖x‖ ≤ 1 / 2 := by
    intro x hx
    have hx' : x ∈ closedBall (0 : ℂ) (1 / 2) := hΛr_sub (subset_closure hx)
    rwa [mem_closedBall, dist_zero_right] at hx'
  have hup_q : ∀ x ∈ Λ qR, ‖x‖ ≤ 1 / 2 := fun x hx => hup_r x (hmono qR rR hq hqr.le hx)
  -- lower bounds: the rational test at `q` fails, so the raw cluster at `q` reaches every radius below `1/2`
  have hlow : ∀ w < (1 / 2 : ℝ), ∃ x ∈ Λ qR, w < ‖x‖ := by
    intro w hw
    obtain ⟨s, hws, hs⟩ := exists_rat_btwn hw
    have hex : ∃ n : ℕ, denseSeq ℂ n ∈ interior (closure (cluster ν (3 / 4) 0 qR)) ∧
        denseSeq ℂ n ∉ closedBall (0 : ℂ) (s : ℝ) := by
      by_contra hcon
      apply hnot'
      unfold halfBallTest
      refine ⟨s, hs, fun n hn => ?_⟩
      by_contra hc
      exact hcon ⟨n, hn, hc⟩
    obtain ⟨n, hnC, hnB⟩ := hex
    have hnorm : (s : ℝ) < ‖denseSeq ℂ n‖ := by
      rw [mem_closedBall, dist_zero_right, not_le] at hnB
      exact hnB
    have hmem : denseSeq ℂ n ∈ closure (Λ qR) := by
      rw [hΛq]
      exact subset_closure hnC
    obtain ⟨y, hy, hys⟩ := exists_mem_norm_gt_of_mem_closure hmem hnorm
    exact ⟨y, hy, lt_trans hws hys⟩
  have hfamq : familyRadius (Λ qR) = 1 / 2 := by
    apply familyRadius_eq_of_bounds
    · obtain ⟨y, hy, -⟩ := hlow 0 (by norm_num)
      exact ⟨y, hy⟩
    · exact hup_q
    · exact hlow
  have hfamr : familyRadius (Λ rR) = 1 / 2 := by
    apply familyRadius_eq_of_bounds
    · obtain ⟨y, hy, -⟩ := hlow 0 (by norm_num)
      exact ⟨y, hmono qR rR hq hqr.le hy⟩
    · exact hup_r
    · intro w hw
      obtain ⟨y, hy, hwy⟩ := hlow w hw
      exact ⟨y, hmono qR rR hq hqr.le hy, hwy⟩
  exact ⟨by norm_num, q.1, r.1, hq, hqr, hfamq, hfamr⟩

end MatedCRT
