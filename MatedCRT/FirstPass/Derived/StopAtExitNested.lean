import MatedCRT.FirstPass.Derived.BrownianRegularExitBall
import MatedCRT.Proofs.LBM.ExitPosition

/-!
# Stopping at the exit of a subdomain

Let `U ⊆ V ⊆ ℂ` with `U` open and let `f : [0, ∞) → ℂ` be continuous. Stopping `f` on exiting `V` and then on
exiting `U` is the same as stopping `f` on exiting `U` (`stopAtExit_stopAtExit_of_subset`): the exit time from `U`
does not change when the path is first stopped at its exit from `V`. If moreover `closure U ⊆ interior V` and `f`
starts in `U` and exits `U` regularly, the path stopped at its exit from `V` still exits `U` regularly.

This is the last step of the proof of the uniform-start invariance principle (Gwynne–Miller–Sheffield, arXiv
1807.07515, proof of Theorem 3.10, p. 45: "noting that `B_r(0) ⊂ S_k^P`"): closeness, for the distance `cmpEDist`
of curves modulo time parametrization, of walk and Brownian paths stopped at the exit of a square transfers to the
paths stopped at the exit of a disc inside it. For planar Brownian motion started in `ball z r` with
`closedBall z r ⊆ interior V` this is `ae_cmpEDist_stopAtExit_ball_of_stopAtExit_planarBrownian`.

## Main statements

* `MatedCRT.StopAtExitCmp.pathExitTime_stopAtExit_of_subset`, `stopAtExit_stopAtExit_of_subset`.
* `MatedCRT.StopAtExitCmp.regularExit_stopAtExit`: regular exit from `U` survives stopping at the exit of `V`.
* `MatedCRT.StopAtExitCmp.ae_cmpEDist_stopAtExit_ball_of_stopAtExit_planarBrownian`.
-/

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- Exit times are monotone in the domain. -/
theorem pathExitTime_mono {U V : Set ℂ} (hUV : U ⊆ V) (f : ℝ≥0 → ℂ) :
    pathExitTime U f ≤ pathExitTime V f := by
  unfold pathExitTime
  refine sInf_le_sInf fun s hs => ?_
  obtain ⟨t, rfl, ht⟩ := hs
  exact ⟨t, rfl, fun h => ht (hUV h)⟩

/-- At a finite exit time, the exit position is the value of the path at the exit time. -/
theorem pathExitPosition_eq_of_ne_top {U : Set ℂ} {f : ℝ≥0 → ℂ} (h : pathExitTime U f ≠ ⊤) :
    pathExitPosition U f = f (pathExitTime U f).toNNReal := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ≥0, (u : ℝ≥0∞) = pathExitTime U f := ⟨_, ENNReal.coe_toNNReal h⟩
  rw [pathExitPosition, ← hu]
  rfl

/-- At its finite exit time from an open set `U`, a continuous path is outside `U`. -/
theorem not_mem_at_exitTime {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (hfin : pathExitTime U f ≠ ⊤) : f (pathExitTime U f).toNNReal ∉ U := by
  by_cases h0 : f 0 ∈ U
  · have hfr := pathExitPosition_mem_frontier_of_continuous hU hf h0 (lt_top_iff_ne_top.2 hfin)
    rw [hU.frontier_eq, pathExitPosition_eq_of_ne_top hfin] at hfr
    exact hfr.2
  · have h : pathExitTime U f = 0 := by
      have h' := exitTime_le_of_not_mem (U := U) (g := f) (t := 0) h0
      simpa using h'
    rw [h]
    simpa using h0

/-- Up to the exit time from `V`, the path stopped at that exit time agrees with the path. -/
theorem stopAtExit_apply_of_le {V : Set ℂ} {f : ℝ≥0 → ℂ} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ pathExitTime V f) : stopAtExit V f t = f t := by
  unfold stopAtExit
  split_ifs with h
  · rfl
  · obtain ⟨u, hu⟩ : ∃ u : ℝ≥0, (u : ℝ≥0∞) = pathExitTime V f := ⟨_, ENNReal.coe_toNNReal h⟩
    rw [← hu] at ht ⊢
    rw [ENNReal.toNNReal_coe, min_eq_left (ENNReal.coe_le_coe.1 ht)]

/-- A continuous path stopped at its exit time is continuous. -/
theorem continuous_stopAtExit {V : Set ℂ} {f : ℝ≥0 → ℂ} (hf : Continuous f) :
    Continuous (stopAtExit V f) := by
  show Continuous fun t => f (if pathExitTime V f = ⊤ then t else min t (pathExitTime V f).toNNReal)
  by_cases h : pathExitTime V f = ⊤
  · simp only [h, ↓reduceIte]
    exact hf
  · simp only [h, ↓reduceIte]
    exact hf.comp (continuous_id.min continuous_const)

/-- For `U ⊆ V` with `U` open and `f` continuous, the path stopped at its exit from `V` has the same exit time
from `U` as `f`. -/
theorem pathExitTime_stopAtExit_of_subset {U V : Set ℂ} (hU : IsOpen U) (hUV : U ⊆ V) {f : ℝ≥0 → ℂ}
    (hf : Continuous f) : pathExitTime U (stopAtExit V f) = pathExitTime U f := by
  apply le_antisymm
  · by_cases hfin : pathExitTime U f = ⊤
    · rw [hfin]
      exact le_top
    · have hnot := not_mem_at_exitTime hU hf hfin
      have hle : ((pathExitTime U f).toNNReal : ℝ≥0∞) ≤ pathExitTime V f := by
        rw [ENNReal.coe_toNNReal hfin]
        exact pathExitTime_mono hUV f
      calc pathExitTime U (stopAtExit V f) ≤ ((pathExitTime U f).toNNReal : ℝ≥0∞) := by
            refine exitTime_le_of_not_mem ?_
            rw [stopAtExit_apply_of_le hle]
            exact hnot
        _ = pathExitTime U f := ENNReal.coe_toNNReal hfin
  · show pathExitTime U f ≤
      sInf {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧ stopAtExit V f t ∉ U}
    refine le_sInf fun s hs => ?_
    obtain ⟨t, rfl, ht⟩ := hs
    unfold stopAtExit at ht
    split_ifs at ht with h
    · exact exitTime_le_of_not_mem ht
    · exact (exitTime_le_of_not_mem ht).trans (ENNReal.coe_le_coe.2 (min_le_left _ _))

/-- Stopping a continuous path at its exit from `V` and then at its exit from an open `U ⊆ V` is stopping it at its
exit from `U`. -/
theorem stopAtExit_stopAtExit_of_subset {U V : Set ℂ} (hU : IsOpen U) (hUV : U ⊆ V) {f : ℝ≥0 → ℂ}
    (hf : Continuous f) : stopAtExit U (stopAtExit V f) = stopAtExit U f := by
  funext t
  have hE := pathExitTime_stopAtExit_of_subset hU hUV hf
  have hmono := pathExitTime_mono hUV f
  show stopAtExit V f (if pathExitTime U (stopAtExit V f) = ⊤ then t
      else min t (pathExitTime U (stopAtExit V f)).toNNReal) =
    f (if pathExitTime U f = ⊤ then t else min t (pathExitTime U f).toNNReal)
  rw [hE]
  apply stopAtExit_apply_of_le
  split_ifs with h
  · have hV : pathExitTime V f = ⊤ := top_le_iff.1 (h ▸ hmono)
    rw [hV]
    exact le_top
  · calc ((min t (pathExitTime U f).toNNReal : ℝ≥0) : ℝ≥0∞)
          ≤ ((pathExitTime U f).toNNReal : ℝ≥0∞) := ENNReal.coe_le_coe.2 (min_le_right _ _)
      _ = pathExitTime U f := ENNReal.coe_toNNReal h
      _ ≤ pathExitTime V f := hmono

/-- If `closure U ⊆ interior V`, a continuous path that starts in the open set `U`, leaves it at a finite time and
exits it regularly, still exits `U` regularly after being stopped at its exit from `V`. -/
theorem regularExit_stopAtExit {U V : Set ℂ} (hU : IsOpen U) (hUV : closure U ⊆ interior V)
    {f : ℝ≥0 → ℂ} (hf : Continuous f) (h0 : f 0 ∈ U) (hfin : pathExitTime U f ≠ ⊤)
    (hreg : MatedCRT.TruncatedLaws.RegularExit U f) :
    pathExitTime U (stopAtExit V f) ≠ ⊤ ∧ MatedCRT.TruncatedLaws.RegularExit U (stopAtExit V f) := by
  have hsub : U ⊆ V := subset_closure.trans (hUV.trans interior_subset)
  have hE := pathExitTime_stopAtExit_of_subset hU hsub hf
  refine ⟨hE ▸ hfin, Or.inr ?_⟩
  rw [hE]
  have hfr : f (pathExitTime U f).toNNReal ∈ frontier U := by
    rw [← pathExitPosition_eq_of_ne_top hfin]
    exact pathExitPosition_mem_frontier_of_continuous hU hf h0 (lt_top_iff_ne_top.2 hfin)
  have hint : f (pathExitTime U f).toNNReal ∈ interior V := hUV (frontier_subset_closure hfr)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
    (hf.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint))
  set τ : ℝ≥0 := (pathExitTime U f).toNNReal with hτ
  have hτeq : (τ : ℝ≥0∞) = pathExitTime U f := ENNReal.coe_toNNReal hfin
  set u : ℝ≥0 := τ + (ε / 2).toNNReal with hu
  have hτu : τ < u := by
    rw [hu]
    exact lt_add_of_pos_right _ (Real.toNNReal_pos.2 (half_pos hε))
  have hstay : ∀ t ≤ u, f t ∈ V := by
    intro t ht
    by_cases hlt : (t : ℝ≥0∞) < pathExitTime U f
    · exact hsub (mem_of_lt_exitTime hlt)
    · have hτt : τ ≤ t := by
        rw [← ENNReal.coe_le_coe, hτeq]
        exact not_lt.1 hlt
      refine interior_subset (hball ?_)
      rw [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hτt))]
      have htu : (t : ℝ) ≤ (u : ℝ) := NNReal.coe_le_coe.2 ht
      have hu' : (u : ℝ) = (τ : ℝ) + ε / 2 := by
        rw [hu, NNReal.coe_add, Real.coe_toNNReal _ (half_pos hε).le]
      linarith
  have hVu : (u : ℝ≥0∞) ≤ pathExitTime V f := le_exitTime_of_forall_le_mem hstay
  have hev : ∀ᶠ t in 𝓝[>] τ, t < u :=
    (eventually_lt_nhds hτu).filter_mono nhdsWithin_le_nhds
  refine (hreg.resolve_left hfin).mp (hev.mono fun t htu hft => ?_)
  rw [stopAtExit_apply_of_le ((ENNReal.coe_le_coe.2 htu.le).trans hVu)]
  exact hft

/-- For almost every planar Brownian path `b` started in `ball z r`, and `V ⊇ closedBall z r` a neighbourhood of
the closed disc, closeness modulo time parametrization of a continuous path `Y` stopped at its exit from `V` to `b`
stopped at its exit from `V` implies closeness of the two paths stopped at their exits from `ball z r`. -/
theorem ae_cmpEDist_stopAtExit_ball_of_stopAtExit_planarBrownian {V : Set ℂ} {x z : ℂ} {r : ℝ}
    (hx : x ∈ ball z r) (hV : closedBall z r ⊆ interior V) :
    ∀ᵐ (b : ContinuousPath ℂ) ∂planarBrownianMotion x, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ Y : ℝ≥0 → ℂ, Continuous Y → cmpEDist (stopAtExit V Y) (stopAtExit V ⇑b) < ENNReal.ofReal δ →
        cmpEDist (stopAtExit (ball z r) Y) (stopAtExit (ball z r) ⇑b) < ENNReal.ofReal ε := by
  have hUV : closure (ball z r) ⊆ interior V := closure_ball_subset_closedBall.trans hV
  have hsub : ball z r ⊆ V := subset_closure.trans (hUV.trans interior_subset)
  filter_upwards [ae_regularExit_ball_planarBrownian hx, ae_planarBrownianMotion_eval_zero x]
    with b hb h0 ε hε
  obtain ⟨hfin', hreg'⟩ :=
    regularExit_stopAtExit isOpen_ball hUV b.continuous (h0 ▸ hx) hb.1 hb.2
  obtain ⟨δ, hδ, hδε⟩ := cmpEDist_stopAtExit_lt_of_regularExit isOpen_ball
    (continuous_stopAtExit b.continuous) hfin' hreg' hε
  refine ⟨δ, hδ, fun Y hY hYδ => ?_⟩
  have h := hδε (stopAtExit V Y) hYδ
  rwa [stopAtExit_stopAtExit_of_subset isOpen_ball hsub hY,
    stopAtExit_stopAtExit_of_subset isOpen_ball hsub b.continuous] at h

end MatedCRT.StopAtExitCmp
