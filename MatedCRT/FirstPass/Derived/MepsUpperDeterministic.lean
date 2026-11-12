import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.ExitTime
import MatedCRT.FirstPass.S4S6c.GreenTest68

/-!
# Deterministic steps of the upper bound on the median exit time `m_ε`

The upper bound `m_ε ≤ C ε⁻¹` of the median exit time (eq:meps, line 731) compares the exit time of
the embedded walk from `B_{1/2}` with the exit time of the walk from the interior vertex set
`V^ε(B_ρ) \ V^ε(∂B_ρ)` of a larger ball, whose expectation is controlled by the exit-time upper bound
of Berestycki-Gwynne (Lemma 2.18). This file proves the deterministic steps of that comparison.

## Main results

* `MatedCRT.vertexPoint_mem_ball_subset_interiorCellVertices`: when every cell meeting `B_ρ` has
  diameter `< ρ - r`, every vertex whose embedded position lies in `B_r` belongs to
  `V^ε(B_ρ) \ V^ε(∂B_ρ)`.
* `MatedCRT.zero_mem_cell_vertexOf`: for a path with `η 0 = 0`, the starting vertex `a^ε_0` has `0`
  in its cell (also when the defining infimum takes its junk value).
* `MatedCRT.embeddedExitTime_le_vExitTime`: the exit time of the embedded walk from `B_r` is at most
  its exit time from `V^ε(B_ρ) \ V^ε(∂B_ρ)` under the same diameter bound.
* `MatedCRT.srwLaw_lt_vExitTime_le`: Markov's inequality for the exit time, with a larger set on
  the right: `P_a(s < τ_A) ≤ E_a[τ_B] / s` for `A ⊆ B`.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT

/-- **Small cells of points of a ball are interior cells of a larger ball.** If `r ≤ ρ` and every
cell meeting `B_ρ` has diameter `< ρ - r`, then every vertex `k` whose embedded position `η(εk)` lies
in `B_r` belongs to `V^ε(B_ρ) \ V^ε(∂B_ρ)`: its cell contains `η(εk)` and lies inside `B_ρ`. -/
theorem vertexPoint_mem_ball_subset_interiorCellVertices {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε)
    (hcont : Continuous η) {r ρ : ℝ} (hrρ : r ≤ ρ)
    (hd : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) < ρ - r) :
    {k : ℤ | vertexPoint ε η k ∈ ball 0 r} ⊆ interiorCellVertices ε η (ball 0 ρ) := by
  intro k hk
  have hk' : vertexPoint ε η k ∈ ball (0 : ℂ) r := hk
  have hmem : vertexPoint ε η k ∈ cell ε η k :=
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩
  have hbdd : Bornology.IsBounded (cell ε η k) := (isCompact_Icc.image hcont).isBounded
  have hne : (cell ε η k ∩ ball 0 ρ).Nonempty := ⟨_, hmem, ball_subset_ball hrρ hk'⟩
  have hsub : cell ε η k ⊆ ball (0 : ℂ) ρ := by
    intro y hy
    have h1 := dist_le_diam_of_mem hbdd hy hmem
    have h2 := hd k hne
    rw [mem_ball] at hk' ⊢
    linarith [dist_triangle y (vertexPoint ε η k) 0]
  refine ⟨hne, ?_⟩
  rintro ⟨y, hy, hyf⟩
  have hint : y ∉ interior (ball (0 : ℂ) ρ) := hyf.2
  rw [isOpen_ball.interior_eq] at hint
  exact hint (hsub hy)

/-- **The starting vertex `a^ε_0`.** For a path with `η 0 = 0` and `ε ≥ 0`, the point `0` lies in the
cell of `a^ε_0 = vertexOf ε η 0`; this holds also when the infimum defining `a^ε_0` takes its junk
value `0`, since `0 = η 0` lies in the cell `η([-ε, 0])` of the vertex `0`. -/
theorem zero_mem_cell_vertexOf {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) (h0 : η 0 = 0) :
    (0 : ℂ) ∈ cell ε η (vertexOf ε η 0) := by
  have h0s : (0 : ℤ) ∈ {k : ℤ | (0 : ℂ) ∈ cell ε η k} :=
    ⟨0, ⟨by push_cast; nlinarith, by simp⟩, h0⟩
  by_cases hb : BddBelow {k : ℤ | (0 : ℂ) ∈ cell ε η k}
  · exact Int.csInf_mem ⟨0, h0s⟩ hb
  · have : vertexOf ε η 0 = 0 := Int.csInf_of_not_bddBelow hb
    rw [this]
    exact h0s

/-- **Comparison of exit times.** Under the diameter bound of
`vertexPoint_mem_ball_subset_interiorCellVertices`, the exit time of the embedded walk from `B_r` is
at most the exit time of the walk from `V^ε(B_ρ) \ V^ε(∂B_ρ)`. -/
theorem embeddedExitTime_le_vExitTime {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) (hcont : Continuous η)
    {r ρ : ℝ} (hrρ : r ≤ ρ)
    (hd : ∀ k : ℤ, (cell ε η k ∩ ball 0 ρ).Nonempty → diam (cell ε η k) < ρ - r) (x : ℕ → ℤ) :
    embeddedExitTime ε η (ball 0 r) x ≤ vExitTime (interiorCellVertices ε η (ball 0 ρ)) x :=
  GreenTest68.vExitTime_le_of_subset (vertexPoint_mem_ball_subset_interiorCellVertices hε hcont hrρ hd) x

/-- **Markov's inequality for exit times.** For `A ⊆ B` and `0 < s < ∞`, the probability that the
walk started at `a` stays in `A` beyond time `s` is at most `E_a[τ_B] / s`. -/
theorem srwLaw_lt_vExitTime_le (m : ℤ → ℤ → ℕ) {A B : Set ℤ} (hAB : A ⊆ B) (a : ℤ) {s : ℝ≥0∞}
    (hs0 : s ≠ 0) (hs : s ≠ ∞) :
    srwLaw m a {x | s < (vExitTime A x : ℝ≥0∞)} ≤ exitTimeMoment m B a 1 / s := by
  have hsub : {x : ℕ → ℤ | s < (vExitTime A x : ℝ≥0∞)} ⊆ {x | s ≤ (vExitTime B x : ℝ≥0∞)} :=
    fun x (hx : s < (vExitTime A x : ℝ≥0∞)) =>
      show s ≤ (vExitTime B x : ℝ≥0∞) from
        hx.le.trans (ENat.toENNReal_le.mpr (GreenTest68.vExitTime_le_of_subset hAB x))
  refine (measure_mono hsub).trans ?_
  simpa [exitTimeMoment] using
    meas_ge_le_lintegral_div (Tightness.measurable_vExitTime_coe B).aemeasurable hs0 hs

end MatedCRT
