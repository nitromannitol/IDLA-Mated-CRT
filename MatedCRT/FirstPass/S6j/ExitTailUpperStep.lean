import MatedCRT.FirstPass.S6j.ExitTailUpperWalk
import MatedCRT.FirstPass.S6j.CmpEDistPointwise
import MatedCRT.FirstPass.Derived.StopAtExitNested
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkContinuity
import LatticeProb.Prob.ContinuousPathStepTimeChain
import LatticeProb.Prob.ContinuousPathStepTimeStay

/-!
# The per-environment step of the upper tail of the exit time (BG20 Lemma 6.10)

Fix an environment `(ε, η, m)` on the cell-size event in `B_{7/8}(0)` (cell diameters at most `c ≤ 1/8`) and on the event
of the uniform-start invariance principle with tolerance `κ ≤ 1/8` (radii `5/8 < 7/8`). For a vertex `x` whose cell
meets `B_{1/2}(0)`, the probability that the walk from `x` makes `K` successive exits from the interior cells of the
balls of radius `δ` before leaving the interior cells of `B_{1/2}(0)` is at most `κ` plus the probability that planar
Brownian motion from `η(εx)` stays in `B_2(η(εx))` up to its `K'`-th displacement time of size `r`, whenever
`2 r + 2 κ ≤ (δ - c)/2` and `K' ≤ K`.

The walk event is contained in the event that the walk stopped at its exit from `B_{7/8}(0)` stays in `B_{5/8}(0)`
before its `K`-th displacement time of size `(δ - c)/2` (the successive exits form a chain of separation `δ - c`,
`ExitTailUpperWalk.chain_of_not_exit_le`, and the greedy displacement time is dominated by any such chain); the
uniform-start principle transfers this to Brownian motion, and the stay form of the comparison of displacement times
of two paths close modulo a time change gives the Brownian event
(Berestycki-Gwynne, arXiv:2003.10320, proof of Lemma 6.10).
-/

namespace MatedCRT.ExitTailUpperStep

open Set Metric MeasureTheory _root_.HarmonicBalls SuccessiveExitGaps WalkDisplacementBlocks ExitTailUpperWalk
open scoped ENNReal NNReal

variable {ε : ℝ} {η : ℝ → ℂ}

/-- The regions `V^ε(B_δ(η(ε z))) \ V^ε(∂B_δ(η(ε z)))` used after the exit from the one centred at `η(ε w_{σ_{k-1}})`. -/
abbrev exitRegion (ε : ℝ) (η : ℝ → ℂ) (δ : ℝ) : ℤ → Set ℤ := fun z =>
  interiorCellVertices ε η (ball (vertexPoint ε η z) δ)

/-- **The walk event is contained in a stay event for the stopped interpolated walk.** On the event that the walk
makes `K` successive exits from the regions `exitRegion ε η δ` before leaving the interior cells of `B_{1/2}(0)`,
the interpolated walk stopped at its exit from `B_{7/8}(0)` stays in `B_{5/8}(0)` before its `K`-th displacement
time of size `(δ - c)/2`. -/
theorem stopAtExit_mem_stay_of_not_exit_le (hε : 0 ≤ ε) (hη : Continuous η) {c δ : ℝ} {K : ℕ} (hδ : 0 < δ)
    (hc8 : c ≤ 1 / 8) (hr0 : 0 < (δ - c) / 2)
    (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) (7 / 8)).Nonempty → diam (cell ε η k) ≤ c) {w : ℕ → ℤ}
    (hw : ¬ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) (1 / 2))) w ≤
      succExit (exitRegion ε η δ) K w) :
    stopAtExit (ball (0 : ℂ) (7 / 8)) (interpolatedWalk ε η 1 w) ∈
      {f : ℝ≥0 → ℂ | ∀ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime f ((δ - c) / 2) K → ‖f t‖ < 5 / 8} := by
  obtain ⟨hstay, hloc, hmono, hsep⟩ :=
    chain_of_not_exit_le (R := 7 / 8) (r₁ := 1 / 2) hε hη hδ (by norm_num) (by linarith) hcell hw
  have hne : succExit (exitRegion ε η δ) K w ≠ ⊤ := ne_top_of_lt (not_le.1 hw)
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
  have hcT : chainTime (exitRegion ε η δ) K w K = (N : ℝ≥0∞) := by
    simp only [chainTime, le_refl, ↓reduceIte]
    rw [← hN, ENat.toENNReal_coe]
  have hle : ∀ t : ℝ≥0, t ≤ (N : ℝ≥0) → (t : ℝ≥0∞) ≤ chainTime (exitRegion ε η δ) K w K := fun t ht => by
    rw [hcT, ← ENNReal.coe_natCast]
    exact ENNReal.coe_le_coe.2 ht
  have hle' : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ chainTime (exitRegion ε η δ) K w K → t ≤ (N : ℝ≥0) := fun t ht => by
    rw [hcT, ← ENNReal.coe_natCast] at ht
    exact ENNReal.coe_le_coe.1 ht
  have hτ := LatticeProb.stepTime_le_of_chain (f := interpolatedWalk ε η 1 w) (r := (δ - c) / 2)
    (D := δ - c) (by linarith) hmono hsep K
  have hTN : LatticeProb.stepTime (interpolatedWalk ε η 1 w) ((δ - c) / 2) K ≤ ((N : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_natCast]
    exact hτ.trans hcT.le
  have heq := LatticeProb.stepTime_eq_of_eqOn_of_le (g := stopAtExit (ball (0 : ℂ) (7 / 8))
    (interpolatedWalk ε η 1 w)) (fun t ht => (hloc t (hle t ht)).symm)
    (continuous_interpolatedWalk ε 1 η w) hr0 hTN
  intro t ht
  rw [heq] at ht
  have htN : t ≤ (N : ℝ≥0) := by
    have : (t : ℝ≥0∞) ≤ ((N : ℝ≥0) : ℝ≥0∞) := ht.le.trans hTN
    exact ENNReal.coe_le_coe.1 this
  rw [hloc t (hle t htN)]
  linarith [hstay t (hle t htN)]

/-- **The Brownian event.** If a path `f` that stays in `B_{5/8}(0)` before its `K`-th displacement time of size
`(δ - c)/2` is within curve distance `κ` of the planar path `b` stopped at its exit from `B_{7/8}(0)`, and
`2 r + 2 κ ≤ (δ - c)/2`, `κ ≤ 1/8`, `0 < r`, then `b` stays in `B_{5/8 + κ}(0)` before its `K`-th displacement
time of size `r`. -/
theorem norm_lt_of_cmpEDist_lt_of_stay {b f : ℝ≥0 → ℂ} (hb : Continuous b) {κ r s : ℝ} (hr0 : 0 < r)
    (hκ : κ ≤ 1 / 8) (hr : 2 * r + 2 * κ ≤ s) {K : ℕ}
    (hf : ∀ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime f s K → ‖f t‖ < 5 / 8)
    (h : cmpEDist (stopAtExit (ball (0 : ℂ) (7 / 8)) b) f < ENNReal.ofReal κ) :
    ∀ u : ℝ≥0, (u : ℝ≥0∞) < LatticeProb.stepTime b r K → ‖b u‖ < 5 / 8 + κ := by
  by_cases hexit : pathExitTime (ball (0 : ℂ) (7 / 8)) b = ⊤
  · rw [CmpEDistPointwise.stopAtExit_eq_self_of_exit_eq_top hexit] at h
    obtain ⟨ψ, hψ⟩ := CmpEDistPointwise.exists_orderIso_norm_sub_lt_of_cmpEDist_lt h
    exact LatticeProb.norm_lt_of_lt_stepTime_of_norm_sub_comp_le ψ (fun t => (hψ t).le) hr hf
  · obtain ⟨ψ, hψ⟩ := CmpEDistPointwise.exists_orderIso_norm_sub_stopped_le_of_cmpEDist_lt hexit h
    have hT := StopAtExitCmp.not_mem_at_exitTime (isOpen_ball (x := (0 : ℂ)) (ε := 7 / 8)) hb hexit
    have hT' : 7 / 8 ≤ ‖b (pathExitTime (ball (0 : ℂ) (7 / 8)) b).toNNReal‖ :=
      not_lt.1 fun hlt => hT (mem_ball_zero_iff.2 hlt)
    exact LatticeProb.norm_lt_of_lt_stepTime_of_norm_sub_comp_stopped_le hb ψ hr0 hψ hr hf
      (by linarith)

/-- **The per-environment step of [BG20, Lemma 6.10].** See the module docstring. -/
theorem srwLaw_notExit_le_planarBrownianMotion_add (hε : 0 ≤ ε) (hη : Continuous η) {m : ℤ → ℤ → ℕ}
    {c δ κ r : ℝ} {K K' : ℕ} (hδ : 0 < δ) (hc8 : c ≤ 1 / 8) (hκ0 : 0 < κ) (hκ : κ ≤ 1 / 8) (hr0 : 0 < r)
    (hr : 2 * r + 2 * κ ≤ (δ - c) / 2) (hK : K' ≤ K)
    (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) (7 / 8)).Nonempty → diam (cell ε η k) ≤ c)
    (hN4 : ∀ x : ℤ, vertexPoint ε η x ∈ closedBall (0 : ℂ) (5 / 8) → ∀ A : Set (ℝ≥0 → ℂ),
      srwLaw m x {w | stopAtExit (ball (0 : ℂ) (7 / 8)) (interpolatedWalk ε η 1 w) ∈ A} ≤
        planarBrownianMotion (vertexPoint ε η x)
          {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) (7 / 8)) ⇑b) f < ENNReal.ofReal κ} +
          ENNReal.ofReal κ)
    {x : ℤ} (hx : x ∈ cellVertices ε η (ball (0 : ℂ) (1 / 2))) :
    srwLaw m x {w | ¬ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) (1 / 2))) w ≤
        succExit (exitRegion ε η δ) K w} ≤
      planarBrownianMotion (vertexPoint ε η x)
          {b | ∀ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime (⇑b) r K' →
            ‖b t - vertexPoint ε η x‖ < 2} + ENNReal.ofReal κ := by
  have hxv : ‖vertexPoint ε η x‖ ≤ 5 / 8 := by
    obtain ⟨y, hyc, hyb⟩ := hx
    have hd : diam (cell ε η x) ≤ c := hcell x ⟨y, hyc, ball_subset_ball (by norm_num) hyb⟩
    have := dist_vertexPoint_lt_of_mem_cellVertices hε hη (z := (0 : ℂ)) ⟨y, hyc, hyb⟩ hd
    rw [dist_zero_right] at this
    linarith
  have hr0' : 0 < (δ - c) / 2 := by linarith
  set A : Set (ℝ≥0 → ℂ) := {f | ∀ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime f ((δ - c) / 2) K →
    ‖f t‖ < 5 / 8} with hA
  calc _ ≤ srwLaw m x {w | stopAtExit (ball (0 : ℂ) (7 / 8)) (interpolatedWalk ε η 1 w) ∈ A} :=
        measure_mono fun w hw => stopAtExit_mem_stay_of_not_exit_le hε hη hδ hc8 hr0' hcell hw
    _ ≤ _ := hN4 x (mem_closedBall_zero_iff.2 hxv) A
    _ ≤ _ := by
        refine add_le_add (measure_mono (μ := planarBrownianMotion (vertexPoint ε η x)) fun b hb => ?_) le_rfl
        obtain ⟨f, hfA, hf⟩ := hb
        intro t ht
        have h1 := norm_lt_of_cmpEDist_lt_of_stay b.continuous hr0 hκ hr hfA hf t
          (lt_of_lt_of_le ht (LatticeProb.monotone_stepTime hK))
        calc ‖b t - vertexPoint ε η x‖ ≤ ‖b t‖ + ‖vertexPoint ε η x‖ := norm_sub_le _ _
          _ < 2 := by linarith

end MatedCRT.ExitTailUpperStep
