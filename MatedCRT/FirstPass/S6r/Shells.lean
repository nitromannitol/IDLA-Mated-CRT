import MatedCRT.FirstPass.S6r.Shells.Crossing

/-!
# Lemma 6.8, window S7': choice of the shell centre at the hitting time

Step 5 of the redesigned S7' (displayed (7.23)-(7.26)).
At the first hitting time `C_j` of the shell `Σ_j`, the centre is the grid rounding `z = Q_d(η(a))` of the
vertex point of the current cell, and `R = R_z` is its good radius. The shell is within distance `g + h_ε` of
`z`, and the current cell lies in the ball `B_{R/50}(z)`.

Step 5 of the referee repair: the printed (7.13) covers grid
centres within distance `g` of the shell, while the selected centre is within `g + h_ε ≤ 2g`. So
`shell_hit_choose_center` keeps the named hypothesis `hzElig` (consumed by `S6r/ShellWiring.lean`), and
`shell_hit_choose_center_direct` derives the eligibility of `z` from the geometry (cutoffs `hcut1`, `hcut2`).
-/

namespace MatedCRT.Lemma68Window

open Metric Set

/-- Step 5, displayed (7.23)-(7.26): at the hitting time, with centre `z = Q_d(η(X_C))` (the grid rounding of
the vertex point of the current cell) and good radius `R = R_z`, the shell `Σ` lies within `g + h_ε` of `z`,
the cell `H_{X_C}` lies in `B_{R/50}(z)`, and `z` is eligible with `d ≤ R ≤ s`.
Superseded as a stand-alone claim by `shell_hit_choose_center_direct` (referee repair, eligibility derived, not
assumed). Kept unchanged with the named hypothesis `hzElig` because `S6r/ShellWiring.lean` consumes it. -/
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

/-- Step 5, referee repair (referee table, step 5; PRO `shell_center_is_eligible`): at the hitting time `C` of
`Σ = twoSidedShell K r lam`, the centre `z = Q_d(η(X_C))` is eligible **directly**, with no named hypothesis.
Take `y ∈ H_{X_C} ∩ Σ`. Then `dist z y ≤ g + h ≤ 2g`. Since `B_{s0} ⊆ K ⊆ B_{ρ/2}` and the band
`9r/20 ≤ f ≤ 11r/20` (`shell_band`) hold on `Σ`, `s0 ≤ |y| ≤ ρ/2 + 11r/20`, hence
`s0 - 2g ≤ |z| ≤ ρ/2 + 11r/20 + 2g`. The cutoffs `2g + 3s < s0/10` and `ρ/2 + 11r/20 + 2g + 3s < 3ρ/4` put the
closed `3s`-ball about `z` in the good region `Reg`, so `Elig z` by `hEligReg`, and `d ≤ R z ≤ s` by `hR`.
The distance bounds of `shell_hit_choose_center` then follow as before. -/
theorem shell_hit_choose_center_direct {K : Set ℂ} {ε r h d s g lam ρ s0 : ℝ} {η : ℝ → ℂ}
    (R : ℂ → ℝ) (Elig : ℂ → Prop) (Reg : Set ℂ)
    (hKne : K.Nonempty) (hs0 : ball (0 : ℂ) s0 ⊆ K) (hKb : K ⊆ ball (0 : ℂ) (ρ / 2))
    (hr : 0 < r) (hε : 0 < ε) (X : ℕ → ℤ) (C : ℕ)
    (hdiam : ∀ p ∈ cell ε η (X C), ∀ q ∈ cell ε η (X C), dist p q ≤ h)
    (hC : (cell ε η (X C) ∩ twoSidedShell K r lam).Nonempty)
    (hlam : lam ≤ r / 20) (hg : g = d / 100) (hd : 0 < d) (hh : h ≤ d / 100)
    (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s)
    (hEligReg : ∀ w : ℂ, closedBall w (3 * s) ⊆ Reg → Elig w)
    (hReg : ∀ x : ℂ, 9 * s0 / 10 ≤ ‖x‖ → ‖x‖ ≤ 3 * ρ / 4 → x ∈ Reg)
    (hcut1 : 2 * g + 3 * s < s0 / 10)
    (hcut2 : ρ / 2 + 11 / 20 * r + 2 * g + 3 * s < 3 * ρ / 4)
    (z : ℂ) (hz : z = gridRound g (vertexPoint ε η (X C))) :
    (∃ y ∈ twoSidedShell K r lam, dist z y ≤ g + h) ∧ g + h ≤ R z / 50 ∧
      (∀ p ∈ cell ε η (X C), dist p z ≤ R z / 50) ∧ (∀ p ∈ cell ε η (X C), dist p z < 4 * R z / 3) ∧
      (d ≤ R z ∧ R z ≤ s ∧ Elig z) := by
  obtain ⟨y, hy1, hy2⟩ := hC
  have hgpos : 0 < g := by rw [hg]; positivity
  have hhg : h ≤ g := by rw [hg]; exact hh
  have hvcell := vertexPoint_mem_cell (η := η) hε (X C)
  have hxz : dist (vertexPoint ε η (X C)) z ≤ g := by
    rw [hz, dist_comm]
    exact dist_gridRound_le hgpos _
  have hxy : dist (vertexPoint ε η (X C)) y ≤ h := hdiam _ hvcell _ hy1
  have hzy : dist z y ≤ g + h := by
    have htri := dist_triangle z (vertexPoint ε η (X C)) y
    rw [dist_comm z (vertexPoint ε η (X C))] at htri
    linarith
  have hyz : dist y z ≤ g + h := by rw [dist_comm]; exact hzy
  have hyS := shell_band hlam hy2
  have hylo : s0 ≤ ‖y‖ := by
    by_contra hcon
    have hmem : y ∈ ball (0 : ℂ) s0 := mem_ball_zero_iff.mpr (not_le.mp hcon)
    have h0 : infDist y K = 0 := infDist_zero_of_mem (hs0 hmem)
    linarith [hyS.1]
  have hyup : ‖y‖ ≤ ρ / 2 + 11 / 20 * r := norm_le_of_infDist_le hKne hKb hyS.2
  have hzlo : s0 - 2 * g ≤ ‖z‖ := by
    have h1 : ‖y‖ - ‖z‖ ≤ dist y z := by rw [dist_eq_norm]; exact norm_sub_norm_le y z
    linarith
  have hzhi : ‖z‖ ≤ ρ / 2 + 11 / 20 * r + 2 * g := by
    have h2 : ‖z‖ - ‖y‖ ≤ dist z y := by rw [dist_eq_norm]; exact norm_sub_norm_le z y
    linarith
  have hsub : closedBall z (3 * s) ⊆ Reg := by
    intro x hx
    rw [mem_closedBall] at hx
    have h1 : ‖z‖ - ‖x‖ ≤ dist z x := by rw [dist_eq_norm]; exact norm_sub_norm_le z x
    have h2 : ‖x‖ - ‖z‖ ≤ dist x z := by rw [dist_eq_norm]; exact norm_sub_norm_le x z
    rw [dist_comm] at h1
    exact hReg x (by linarith) (by linarith)
  have hEl : Elig z := hEligReg z hsub
  have hRz := hR z hEl
  have hRpos : 0 < R z := lt_of_lt_of_le hd hRz.1
  have hgh : g + h ≤ R z / 50 := by linarith [hRz.1]
  refine ⟨⟨y, hy2, hzy⟩, hgh, ?_, ?_, ⟨hRz.1, hRz.2, hEl⟩⟩
  · intro p hp
    have hvp : dist p (vertexPoint ε η (X C)) ≤ h := hdiam p hp _ hvcell
    have htri := dist_triangle p (vertexPoint ε η (X C)) z
    linarith
  · intro p hp
    have hvp : dist p (vertexPoint ε η (X C)) ≤ h := hdiam p hp _ hvcell
    have htri := dist_triangle p (vertexPoint ε η (X C)) z
    linarith

end MatedCRT.Lemma68Window
