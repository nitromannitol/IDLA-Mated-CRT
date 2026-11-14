import MatedCRT.FirstPass.Derived.UniformStartStopTransfer

/-!
# Stopping at a subdomain after stopping at an arbitrary larger domain

Let `f` be a continuous path started in an open set `U` which satisfies the quantitative good event
`GoodStop U T η d ε f` at its exit from `U`. Then the comparison of `cmpEDist_stopAtExit_le_of_goodStop` also holds
for the path stopped at its exit time from ANY set `V` containing the closed `ε`-thickening of `U`: every path `g`
within `cmpEDist`-distance `min ε d` of `stopAtExit V f`, once stopped at its exit time from `U`, is within `2ε`
of `stopAtExit U f`. The constants do not depend on `V`.

The reason is that up to the rational time `q` of the good event, shortly after the exit from `U`, the path stays
in the closed `ε`-thickening of `U` (by the modulus of continuity of the good event), so that stopping at the exit
from `V` does not change it before `q`.

This is the form needed for the local metric on curves modulo time parametrization (Gwynne-Miller-Sheffield,
arXiv:1705.11161, (2.2)): closeness of two curves in that metric gives closeness of the curves stopped at their exit
times from `B_r(0)` only for some radius `r` of a given interval, which depends on the curves.

## Main statements
* `MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_le_of_goodStop_of_cthickening_subset`: the general comparison.
* `MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_le_of_goodStopN_of_cthickening_subset`: the same for `GoodStopN`.
* `MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_ball_le_of_goodStopN`: discs `B_R(0) ⊆ B_r(0)` with `R + ε < r`.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- Before its exit time from `U`, a path lies in `U`. -/
theorem mem_of_coe_lt_pathExitTime {U : Set ℂ} {f : ℝ≥0 → ℂ} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < pathExitTime U f) : f t ∈ U := by
  by_contra h
  exact (not_le.2 ht) (by unfold pathExitTime; exact sInf_le ⟨t, rfl, h⟩)

/-- A path which stays in `V` up to time `s` leaves `V` no earlier than `s`. -/
theorem coe_le_pathExitTime_of_forall_mem {V : Set ℂ} {f : ℝ≥0 → ℂ} {s : ℝ≥0}
    (h : ∀ t ≤ s, f t ∈ V) : (s : ℝ≥0∞) ≤ pathExitTime V f := by
  unfold pathExitTime
  refine le_sInf ?_
  rintro _ ⟨t, rfl, ht⟩
  by_contra hlt
  exact ht (h t (ENNReal.coe_le_coe.1 (not_le.1 hlt).le))

/-- At a finite exit time from an open set `U`, a continuous path started in `U` lies in the closure of `U`. -/
theorem mem_closure_at_pathExitTime {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (h0 : f 0 ∈ U) (hfin : pathExitTime U f ≠ ⊤) : f (pathExitTime U f).toNNReal ∈ closure U := by
  rw [← pathExitPosition_eq_of_ne_top hfin]
  exact frontier_subset_closure
    (pathExitPosition_mem_frontier_of_continuous hU hf h0 (lt_top_iff_ne_top.2 hfin))

/-- **Stopping at `U` after stopping at any larger set.** If the continuous path `f`, started in the open set `U`,
satisfies `GoodStop U T η d ε f`, and `V` contains the closed `ε`-thickening of `U`, then every path `g` within
`cmpEDist`-distance `min ε d` of `f` stopped at its exit time from `V` satisfies
`cmpEDist (stopAtExit U g) (stopAtExit U f) ≤ 2ε`. -/
theorem cmpEDist_stopAtExit_le_of_goodStop_of_cthickening_subset {U V : Set ℂ} (hU : IsOpen U)
    {T η : ℝ≥0} {d ε : ℝ} {f : ℝ≥0 → ℂ} (hf : Continuous f) (h0 : f 0 ∈ U) (hη : 0 < η)
    (hUV : cthickening ε U ⊆ V) (hgood : GoodStop U T η d ε f) {g : ℝ≥0 → ℂ}
    (hg : cmpEDist g (stopAtExit V f) < ENNReal.ofReal (min ε d)) :
    cmpEDist (stopAtExit U g) (stopAtExit U f) ≤ ENNReal.ofReal (2 * ε) := by
  obtain ⟨⟨q, hq1, hq2, hqT, hout⟩, hmod, htube⟩ := hgood
  have hUV' : U ⊆ V := (self_subset_cthickening U).trans hUV
  have hfin : pathExitTime U f ≠ ⊤ := ne_top_of_lt hq1
  have hcl := mem_closure_at_pathExitTime hU hf h0 hfin
  set τ : ℝ≥0 := (pathExitTime U f).toNNReal with hτdef
  have hτ : pathExitTime U f = (τ : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
  have hs : ratTime q ∈ Ioo τ (τ + η) := by
    rw [hτ] at hq1 hq2
    refine ⟨ENNReal.coe_lt_coe.1 hq1, ?_⟩
    rw [← ENNReal.coe_add] at hq2
    exact ENNReal.coe_lt_coe.1 hq2
  have hmodR := modulus_of_ratTime hf hη hmod
  have hstay : ∀ t ≤ ratTime q, f t ∈ V := by
    intro t ht
    by_cases htτ : (t : ℝ≥0∞) < pathExitTime U f
    · exact hUV' (mem_of_coe_lt_pathExitTime htτ)
    · have hτt : τ ≤ t := by
        rw [hτ, not_lt] at htτ
        exact ENNReal.coe_le_coe.1 htτ
      apply hUV
      rw [← cthickening_closure]
      refine mem_cthickening_of_dist_le (f t) (f τ) ε (closure U) hcl ?_
      refine hmodR t (ht.trans hqT) τ (hs.1.le.trans hqT) ?_
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hτt))]
      have h1 : (t : ℝ) ≤ ratTime q := NNReal.coe_le_coe.2 ht
      have h2 : ((ratTime q : ℝ≥0) : ℝ) < τ + η := by
        have := NNReal.coe_lt_coe.2 hs.2
        rwa [NNReal.coe_add] at this
      linarith
  have hqV : ((ratTime q : ℝ≥0) : ℝ≥0∞) ≤ pathExitTime V f := coe_le_pathExitTime_of_forall_mem hstay
  have hτV : (τ : ℝ≥0∞) ≤ pathExitTime V f := (ENNReal.coe_le_coe.2 hs.1.le).trans hqV
  have hE := pathExitTime_stopAtExit_of_subset hU hUV' hf
  rw [← stopAtExit_stopAtExit_of_subset hU hUV' hf]
  refine cmpEDist_stopAtExit_le_of_modulus (hE.trans hτ) hη ?_ hs hqT ?_ ?_ hg
  · intro t ht t' ht' htt'
    by_cases hV : pathExitTime V f = ⊤
    · have e : ∀ s, stopAtExit V f s = f s := fun s => by simp [stopAtExit, hV]
      rw [e, e]
      exact hmodR t ht t' ht' htt'
    · have e : ∀ s, stopAtExit V f s = f (min s (pathExitTime V f).toNNReal) := fun s => by
        simp [stopAtExit, hV]
      rw [e, e]
      refine hmodR _ ((min_le_left _ _).trans ht) _ ((min_le_left _ _).trans ht') (lt_of_le_of_lt ?_ htt')
      rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_min, NNReal.coe_min]
      have hab := abs_min_sub_min_le_max (t : ℝ) ((pathExitTime V f).toNNReal : ℝ) (t' : ℝ)
        ((pathExitTime V f).toNNReal : ℝ)
      rwa [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at hab
  · intro w hw
    rw [stopAtExit_apply_of_le hqV] at hw
    exact hout w hw
  · intro t ht w hw
    have htV : (t : ℝ≥0∞) ≤ pathExitTime V f :=
      (ENNReal.coe_le_coe.2 (le_self_add.trans ht)).trans hτV
    rw [stopAtExit_apply_of_le htV] at hw
    exact tube_of_ratTime hf hη hτ htube t ht w hw

/-- `GoodStopN` form of `cmpEDist_stopAtExit_le_of_goodStop_of_cthickening_subset`. -/
theorem cmpEDist_stopAtExit_le_of_goodStopN_of_cthickening_subset {U V : Set ℂ} (hU : IsOpen U) {N : ℕ}
    {ε : ℝ} {f : ℝ≥0 → ℂ} (hf : Continuous f) (h0 : f 0 ∈ U) (hUV : cthickening ε U ⊆ V)
    (hgood : GoodStopN U N ε f) {g : ℝ≥0 → ℂ}
    (hg : cmpEDist g (stopAtExit V f) < ENNReal.ofReal (min ε (N : ℝ)⁻¹)) :
    cmpEDist (stopAtExit U g) (stopAtExit U f) ≤ ENNReal.ofReal (2 * ε) := by
  obtain ⟨T, m, k, -, -, hk, hm0, hk0, hg'⟩ := hgood
  have hη : (0 : ℝ≥0) < (m : ℝ≥0)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hm0)
  refine cmpEDist_stopAtExit_le_of_goodStop_of_cthickening_subset hU hf h0 hη hUV hg'
    (lt_of_lt_of_le hg (ENNReal.ofReal_le_ofReal ?_))
  exact min_le_min le_rfl (inv_anti₀ (Nat.cast_pos.2 hk0) (Nat.cast_le.2 hk))

/-- **Discs.** If the continuous path `f` starts in `B_R(0)` and satisfies `GoodStopN (B_R(0)) N ε f`, then for
EVERY radius `r > R + ε` and every path `g` within `cmpEDist`-distance `min ε (1/N)` of `f` stopped at its exit time
from `B_r(0)`, the paths stopped at their exit times from `B_R(0)` are within `2ε`. -/
theorem cmpEDist_stopAtExit_ball_le_of_goodStopN {R r ε : ℝ} {N : ℕ} {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (h0 : f 0 ∈ ball (0 : ℂ) R) (hε : 0 ≤ ε) (hRr : R + ε < r) (hgood : GoodStopN (ball (0 : ℂ) R) N ε f)
    {g : ℝ≥0 → ℂ} (hg : cmpEDist g (stopAtExit (ball (0 : ℂ) r) f) < ENNReal.ofReal (min ε (N : ℝ)⁻¹)) :
    cmpEDist (stopAtExit (ball (0 : ℂ) R) g) (stopAtExit (ball (0 : ℂ) R) f) ≤ ENNReal.ofReal (2 * ε) := by
  have hR : 0 < R := pos_of_mem_ball h0
  have hUV : cthickening ε (ball (0 : ℂ) R) ⊆ ball (0 : ℂ) r := by
    rw [cthickening_ball hε hR]
    exact closedBall_subset_ball (by linarith)
  exact cmpEDist_stopAtExit_le_of_goodStopN_of_cthickening_subset isOpen_ball hf h0 hUV hgood hg

end MatedCRT.StopAtExitCmp
