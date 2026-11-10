import MatedCRT.FirstPass.S6r.Shells.Crossing

/-!
# Lemma 6.8, window S7': choice of the shell centre at the hitting time

Step 5 of the redesigned S7' (`notes/fp-gaps/CHATGPT-idla-6-8-shells.md`, displayed (7.23)-(7.26)).
At the first hitting time `C_j` of the shell `Σ_j`, the centre is the grid rounding `z = Q_d(η(a))` of the
vertex point of the current cell, and `R = R_z` is its good radius. The shell is within distance `g + h_ε` of
`z`, and the current cell lies in the ball `B_{R/50}(z)`.

Named hypothesis (see the report): `hzElig`, the eligibility of the selected centre `z`. The printed note
(line 389) derives it from the eligibility argument of step 2, which controls grid points within distance `g`
of the shell; the selected centre is only within `g + h_ε ≤ 2g` of it, and the printed (7.13) does not cover
that margin.
-/

namespace MatedCRT.Lemma68Window

open Metric Set

/-- Step 5, displayed (7.23)-(7.26): at the hitting time, with centre `z = Q_d(η(X_C))` (the grid rounding of
the vertex point of the current cell) and good radius `R = R_z`, the shell `Σ` lies within `g + h_ε` of `z`,
the cell `H_{X_C}` lies in `B_{R/50}(z)`, and `z` is eligible with `d ≤ R ≤ s`. -/
theorem shell_hit_choose_center {K : Set ℂ} {ε r h d s g lam : ℝ} {η : ℝ → ℂ} (hε : 0 < ε)
    (X : ℕ → ℤ) (C : ℕ) (R : ℂ → ℝ) (Elig : ℂ → Prop) (z : ℂ)
    (hdiam : ∀ p ∈ cell ε η (X C), ∀ q ∈ cell ε η (X C), dist p q ≤ h)
    (hC : (cell ε η (X C) ∩ twoSidedShell K r lam).Nonempty)
    (hg : g = d / 100) (hd : 0 < d) (hh : h ≤ d / 100)
    (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s)
    (hz : z = gridRound g (vertexPoint ε η (X C)))
    (hzElig : Elig z) :
    (∃ y ∈ twoSidedShell K r lam, dist z y ≤ g + h) ∧
    g + h ≤ R z / 50 ∧
    (∀ p ∈ cell ε η (X C), dist p z ≤ R z / 50) ∧
    (∀ p ∈ cell ε η (X C), dist p z < 4 * R z / 3) ∧
    (d ≤ R z ∧ R z ≤ s ∧ Elig z) := by
  obtain ⟨y, hy1, hy2⟩ := hC
  have hgpos : 0 < g := by rw [hg]; positivity
  have hvcell := vertexPoint_mem_cell (η := η) hε (X C)
  have hxz : dist (vertexPoint ε η (X C)) z ≤ g := by
    rw [hz, dist_comm]
    exact dist_gridRound_le hgpos _
  have hxy : dist (vertexPoint ε η (X C)) y ≤ h := hdiam _ hvcell _ hy1
  have hR' := hR z hzElig
  have hgh : g + h ≤ R z / 50 := by
    linarith [hR'.1]
  refine ⟨⟨y, hy2, ?_⟩, hgh, ?_, ?_, ⟨hR'.1, hR'.2, hzElig⟩⟩
  · have htri := dist_triangle z (vertexPoint ε η (X C)) y
    rw [dist_comm z (vertexPoint ε η (X C))] at htri
    linarith
  · intro p hp
    have htri := dist_triangle p (vertexPoint ε η (X C)) z
    have hpx : dist p (vertexPoint ε η (X C)) ≤ h := hdiam p hp _ hvcell
    linarith
  · intro p hp
    have hRpos : 0 < R z := lt_of_lt_of_le hd hR'.1
    have htri := dist_triangle p (vertexPoint ε η (X C)) z
    have hpx : dist p (vertexPoint ε η (X C)) ≤ h := hdiam p hp _ hvcell
    linarith

end MatedCRT.Lemma68Window
