import MatedCRT.FirstPass.S6j.ExitTailUpperStep
import MatedCRT.FirstPass.S6j.ExitTailUpperWalkV

/-!
# Upper tail of the exit time, full cell sets: from the walk to planar Brownian motion

The variant of `ExitTailUpperStep` for the exit time from `V^ε(B_{1/2}(0))` (cells meeting the ball) and the
successive exits from `V^ε(B_δ(η(ε ·)))`: on the event that the walk makes `K` successive exits before leaving
`V^ε(B_{1/2}(0))`, the interpolated walk stopped at its exit from `B_{7/8}(0)` stays in `B_{5/8}(0)` before its `K`-th
displacement time of size `δ / 2`; the uniform-start invariance principle transfers this, up to `κ`, to planar
Brownian motion (Berestycki-Gwynne, arXiv:2003.10320, proof of Lemma 6.10 giving the estimate (6.50)).
-/

set_option autoImplicit false

namespace MatedCRT.ExitTailUpperStepV

open Set Metric MeasureTheory _root_.HarmonicBalls SuccessiveExitGaps WalkDisplacementBlocks ExitTailUpperWalk
  ExitTailUpperWalkV
open scoped ENNReal NNReal

variable {ε : ℝ} {η : ℝ → ℂ}

/-- **The walk event is contained in a stay event for the stopped interpolated walk.** -/
theorem stopAtExit_mem_stay_of_not_exit_le_V (hε : 0 ≤ ε) (hη : Continuous η) {c δ : ℝ} {K : ℕ} (hδ : 0 < δ)
    (hc8 : c ≤ 1 / 8)
    (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) (7 / 8)).Nonempty → diam (cell ε η k) ≤ c) {w : ℕ → ℤ}
    (hw : ¬ vExitTime (cellVertices ε η (ball (0 : ℂ) (1 / 2))) w ≤
      succExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) δ)) K w) :
    stopAtExit (ball (0 : ℂ) (7 / 8)) (interpolatedWalk ε η 1 w) ∈
      {f : ℝ≥0 → ℂ | ∀ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime f (δ / 2) K → ‖f t‖ < 5 / 8} := by
  set A : ℤ → Set ℤ := fun z => cellVertices ε η (ball (vertexPoint ε η z) δ) with hAdef
  obtain ⟨hstay, hloc, hmono, hsep⟩ :=
    chain_of_not_exit_le_V (R := 7 / 8) (r₁ := 1 / 2) hε hη (by norm_num) (by linarith) hcell hw
  have hne : succExit A K w ≠ ⊤ := ne_top_of_lt (not_le.1 hw)
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
  have hcT : chainTime A K w K = (N : ℝ≥0∞) := by
    simp only [chainTime, le_refl, ↓reduceIte]
    rw [← hN, ENat.toENNReal_coe]
  have hle : ∀ t : ℝ≥0, t ≤ (N : ℝ≥0) → (t : ℝ≥0∞) ≤ chainTime A K w K := fun t ht => by
    rw [hcT, ← ENNReal.coe_natCast]
    exact ENNReal.coe_le_coe.2 ht
  have hτ := LatticeProb.stepTime_le_of_chain (f := interpolatedWalk ε η 1 w) (r := δ / 2)
    (D := δ) (by linarith) hmono hsep K
  have hTN : LatticeProb.stepTime (interpolatedWalk ε η 1 w) (δ / 2) K ≤ ((N : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_natCast]
    exact hτ.trans hcT.le
  have heq := LatticeProb.stepTime_eq_of_eqOn_of_le (g := stopAtExit (ball (0 : ℂ) (7 / 8))
    (interpolatedWalk ε η 1 w)) (fun t ht => (hloc t (hle t ht)).symm)
    (continuous_interpolatedWalk ε 1 η w) (half_pos hδ) hTN
  intro t ht
  rw [heq] at ht
  have htN : t ≤ (N : ℝ≥0) := by
    have : (t : ℝ≥0∞) ≤ ((N : ℝ≥0) : ℝ≥0∞) := ht.le.trans hTN
    exact ENNReal.coe_le_coe.1 this
  rw [hloc t (hle t htN)]
  linarith [hstay t (hle t htN)]

/-- **The per-environment step of [BG20, Lemma 6.10], full cell sets.** For a vertex `x` whose cell meets `B_{1/2}(0)`:
the probability that the walk from `x` makes `K` successive exits from `V^ε(B_δ(η(ε ·)))` before leaving
`V^ε(B_{1/2}(0))` is at most `κ` plus the probability that planar Brownian motion from `η(εx)` stays in `B_2(η(εx))`
before its `K'`-th displacement time of size `r`, whenever `2 r + 2 κ ≤ δ / 2` and `K' ≤ K`. -/
theorem srwLaw_notExit_le_planarBrownianMotion_add_V (hε : 0 ≤ ε) (hη : Continuous η) {m : ℤ → ℤ → ℕ}
    {c δ κ r : ℝ} {K K' : ℕ} (hδ : 0 < δ) (hc8 : c ≤ 1 / 8) (hκ : κ ≤ 1 / 8) (hr0 : 0 < r)
    (hr : 2 * r + 2 * κ ≤ δ / 2) (hK : K' ≤ K)
    (hcell : ∀ k, (cell ε η k ∩ ball (0 : ℂ) (7 / 8)).Nonempty → diam (cell ε η k) ≤ c)
    (hN4 : ∀ x : ℤ, vertexPoint ε η x ∈ closedBall (0 : ℂ) (5 / 8) → ∀ A : Set (ℝ≥0 → ℂ),
      srwLaw m x {w | stopAtExit (ball (0 : ℂ) (7 / 8)) (interpolatedWalk ε η 1 w) ∈ A} ≤
        planarBrownianMotion (vertexPoint ε η x)
          {b | ∃ f ∈ A, cmpEDist (stopAtExit (ball (0 : ℂ) (7 / 8)) ⇑b) f < ENNReal.ofReal κ} +
          ENNReal.ofReal κ)
    {x : ℤ} (hx : x ∈ cellVertices ε η (ball (0 : ℂ) (1 / 2))) :
    srwLaw m x {w | ¬ vExitTime (cellVertices ε η (ball (0 : ℂ) (1 / 2))) w ≤
        succExit (fun z => cellVertices ε η (ball (vertexPoint ε η z) δ)) K w} ≤
      planarBrownianMotion (vertexPoint ε η x)
          {b | ∀ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime (⇑b) r K' →
            ‖b t - vertexPoint ε η x‖ < 2} + ENNReal.ofReal κ := by
  have hxv : ‖vertexPoint ε η x‖ ≤ 5 / 8 := by
    obtain ⟨y, hyc, hyb⟩ := hx
    have hd : diam (cell ε η x) ≤ c := hcell x ⟨y, hyc, ball_subset_ball (by norm_num) hyb⟩
    have := dist_vertexPoint_lt_of_mem_cellVertices hε hη (z := (0 : ℂ)) ⟨y, hyc, hyb⟩ hd
    rw [dist_zero_right] at this
    linarith
  set A : Set (ℝ≥0 → ℂ) := {f | ∀ t : ℝ≥0, (t : ℝ≥0∞) < LatticeProb.stepTime f (δ / 2) K →
    ‖f t‖ < 5 / 8} with hA
  calc _ ≤ srwLaw m x {w | stopAtExit (ball (0 : ℂ) (7 / 8)) (interpolatedWalk ε η 1 w) ∈ A} :=
        measure_mono fun w hw => stopAtExit_mem_stay_of_not_exit_le_V hε hη hδ hc8 hcell hw
    _ ≤ _ := hN4 x (mem_closedBall_zero_iff.2 hxv) A
    _ ≤ _ := by
        refine add_le_add (measure_mono (μ := planarBrownianMotion (vertexPoint ε η x)) fun b hb => ?_) le_rfl
        obtain ⟨f, hfA, hf⟩ := hb
        intro t ht
        have h1 := ExitTailUpperStep.norm_lt_of_cmpEDist_lt_of_stay b.continuous hr0 hκ hr hfA hf t
          (lt_of_lt_of_le ht (LatticeProb.monotone_stepTime hK))
        calc ‖b t - vertexPoint ε η x‖ ≤ ‖b t‖ + ‖vertexPoint ε η x‖ := norm_sub_le _ _
          _ < 2 := by linarith

end MatedCRT.ExitTailUpperStepV
