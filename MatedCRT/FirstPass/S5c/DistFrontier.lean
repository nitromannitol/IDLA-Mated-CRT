import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# FIRST PASS, Lemma 5.3 (three-inputs §7, geometry): the distance to the frontier of a closed set by rational test points

For a closed set `U ⊆ ℂ` with a point `z ∈ U` and a nonempty frontier, `δ < infDist z (frontier U)` holds iff some
rational `r > δ` makes every Gaussian-rational translate `z + q` with `‖q‖ < r` lie in `U` (the closed ball `B̄(z, r)`
is then contained in `U`, the open ball `B(z, r)` in its interior, and conversely). This is the geometric step of the
measurability of the success event `E ε` (Proofs/Sec5 `MeanValueSurplusLowerStep`, `DistFrontier` in the three-inputs
§7 route); it is pure topology and involves no measure.
-/

namespace MatedCRT.S5c

open Metric Set Topology

/-- The Gaussian rational `q₁ + q₂ i` for `q = (q₁, q₂) ∈ ℚ × ℚ`, a countable dense subset of `ℂ`. -/
def gaussRat (q : ℚ × ℚ) : ℂ := ((q.1 : ℝ) : ℂ) + ((q.2 : ℝ) : ℂ) * Complex.I

/-- Gaussian rationals approximate every complex number. -/
lemma exists_gaussRat_near (w : ℂ) {ε : ℝ} (hε : 0 < ε) : ∃ q : ℚ × ℚ, ‖gaussRat q - w‖ < ε := by
  obtain ⟨a, ha⟩ := exists_rat_btwn (show w.re - ε / 2 < w.re + ε / 2 by linarith)
  obtain ⟨b, hb⟩ := exists_rat_btwn (show w.im - ε / 2 < w.im + ε / 2 by linarith)
  refine ⟨(a, b), ?_⟩
  have h1 := Complex.norm_le_abs_re_add_abs_im (gaussRat (a, b) - w)
  have hre : (gaussRat (a, b) - w).re = (a : ℝ) - w.re := by simp [gaussRat]
  have him : (gaussRat (a, b) - w).im = (b : ℝ) - w.im := by simp [gaussRat]
  rw [hre, him] at h1
  have ha' : |(a : ℝ) - w.re| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have hb' : |(b : ℝ) - w.im| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  linarith

/-- **Distance to the frontier of a closed set, by rational test points.** For a closed `U ⊆ ℂ` with nonempty frontier
and `z ∈ U`: `δ < infDist z (frontier U)` iff some rational `r > δ` has `z + q ∈ U` for every Gaussian rational `q`
with `‖q‖ < r`. -/
theorem lt_infDist_frontier_iff {U : Set ℂ} (hU : IsClosed U) (hne : (frontier U).Nonempty) {z : ℂ} (hz : z ∈ U)
    {δ : ℝ} :
    δ < infDist z (frontier U) ↔
      ∃ r : ℚ, δ < (r : ℝ) ∧ ∀ q : ℚ × ℚ, ‖gaussRat q‖ < (r : ℝ) → z + gaussRat q ∈ U := by
  have hnn : 0 ≤ infDist z (frontier U) := infDist_nonneg
  -- a point within `r` of `z`, where all Gaussian-rational test points lie in `U`, lies in `U`
  have hball : ∀ r : ℝ, (∀ q : ℚ × ℚ, ‖gaussRat q‖ < r → z + gaussRat q ∈ U) →
      ∀ w : ℂ, dist w z < r → w ∈ U := by
    intro r H w hw
    have hcl : w ∈ closure U := by
      rw [Metric.mem_closure_iff]
      intro ε' hε'
      have ht : 0 < r - dist w z := by linarith
      obtain ⟨q, hq⟩ := exists_gaussRat_near (w - z) (lt_min hε' ht)
      have hq1 : ‖gaussRat q - (w - z)‖ < min ε' (r - dist w z) := hq
      have hq2 : ‖gaussRat q‖ < r := by
        have e : gaussRat q = (w - z) + (gaussRat q - (w - z)) := by ring
        have htri := norm_add_le (w - z) (gaussRat q - (w - z))
        rw [← e, ← dist_eq_norm] at htri
        have := min_le_right ε' (r - dist w z)
        linarith [dist_eq_norm w z]
      refine ⟨z + gaussRat q, H q hq2, ?_⟩
      have e2 : w - (z + gaussRat q) = -(gaussRat q - (w - z)) := by ring
      rw [dist_eq_norm, e2, norm_neg]
      exact lt_of_lt_of_le hq1 (min_le_left _ _)
    rwa [hU.closure_eq] at hcl
  constructor
  · intro hlt
    rcases lt_or_eq_of_le hnn with hpos | hzero
    · -- `infDist > 0`: the open ball of radius `infDist` lies in `U`
      have hzF : z ∉ frontier U := fun h => by
        have := infDist_zero_of_mem h
        linarith
      have hzint : z ∈ interior U := by
        by_contra h
        exact hzF ⟨subset_closure hz, h⟩
      have hsub : ball z (infDist z (frontier U)) ⊆ U := by
        have hcover : ball z (infDist z (frontier U)) ⊆
            interior U ∪ interior Uᶜ := by
          intro x hx
          have hxF : x ∉ frontier U := fun h => by
            have := infDist_le_dist_of_mem (x := z) h
            rw [mem_ball, dist_comm] at hx
            linarith
          by_cases hxc : x ∈ closure U
          · left
            by_contra h
            exact hxF ⟨hxc, h⟩
          · right
            rw [interior_compl]
            exact hxc
        have hdisj : Disjoint (interior U) (interior Uᶜ) :=
          Set.disjoint_left.2 fun x hu hv => (interior_subset hv) (interior_subset hu)
        have hconn : IsPreconnected (ball z (infDist z (frontier U))) :=
          (convex_ball z (infDist z (frontier U))).isPreconnected
        have hsubI := hconn.subset_left_of_subset_union isOpen_interior isOpen_interior hdisj hcover
          ⟨z, mem_ball_self hpos, hzint⟩
        exact hsubI.trans interior_subset
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show max δ 0 < infDist z (frontier U) from max_lt hlt hpos)
      refine ⟨r, lt_of_le_of_lt (le_max_left _ _) hr1, fun q hq => ?_⟩
      apply hsub
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact lt_trans hq hr2
    · -- `infDist = 0`: then `δ < 0`, and the radius-`r` test is vacuous for `r < 0`
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show δ < 0 by linarith)
      refine ⟨r, hr1, fun q hq => ?_⟩
      exfalso
      have := norm_nonneg (gaussRat q)
      linarith
  · rintro ⟨r, hδr, H⟩
    have hball' := hball r H
    have hle : (r : ℝ) ≤ infDist z (frontier U) := by
      rw [Metric.le_infDist hne]
      intro p hp
      by_contra hlt'
      have hlt : dist z p < r := not_le.1 hlt'
      have hpint : p ∈ interior U :=
        mem_interior.2 ⟨ball z r, fun w hw => hball' w (mem_ball.1 hw), isOpen_ball,
          mem_ball.2 (by rw [dist_comm]; exact hlt)⟩
      exact hp.2 hpint
    exact lt_of_lt_of_le hδr hle

end MatedCRT.S5c
