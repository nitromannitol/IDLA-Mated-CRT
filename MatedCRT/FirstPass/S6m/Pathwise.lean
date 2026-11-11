import Mathlib
import MatedCRT.FirstPass.S6m.Path

/-!
# The pathwise containment `T_N < τ_U` (Lemma 6.8, write-up C6-C12)

Induction on `j ≤ N` for a fixed legal path `x` started at `a` (write-up C3, C6-C11). With `s = √δ`, `g = δ/100`,
`K = fillCells Θ`, `U = killed ε η Θ F0 r`, the invariants are
* `P(j)`: `T_j = t` for some `t ∈ ℕ` and `dist(η(x_t), η(a)) ≤ 3 j s` (write-up (C6)); here `x_t` is the vertex `x t`;
* `Q(j)`: `x n ∈ U` for every `n ≤ t` (write-up (C11)).
The step uses the window `I(B_{2R}(z))`, `z = Q_δ(η(x_t))`, `δ ≤ R ≤ s`, the connectedness of cells (Armitage-Gardiner),
the cell-size bound `diam H_v ≤ d` for cells meeting `B_ρ` (write-up C1), and the start estimate (write-up C5).
-/

namespace MatedCRT

namespace Lemma68C12

open MeasureTheory Set Metric Filter
open scoped ENNReal
open Lemma68Geometry Lemma68GeometryId Lemma68Admissible Lemma68Relation Lemma68Successive

/-- **Pathwise containment (write-up C6-C12).** For a legal path `x` from `a` with finite successive exits up to `N`,
`T_N < τ_U` where `U = killed ε η Θ F0 r`. -/
theorem pathwise_containment {ε r ρ δ s d : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hε : 0 < ε)
    {m : ℤ → ℤ → ℕ} {Θ F0 : Finset ℤ} {a : ℤ} {N : ℕ}
    (z : ℤ → ℂ) (R : ℤ → ℝ) (W : ℤ → Set ℤ)
    (hW : ∀ y, W y = interiorCellVertices ε η (ball (z y) (2 * R y)))
    (hz : ∀ y, dist (z y) (vertexPoint ε η y) ≤ δ / 100)
    (hR : ∀ y, δ ≤ R y ∧ R y ≤ s)
    (hδ : 0 < δ) (hδs : δ ≤ s) (hs : s ≤ r / 1000) (hsN : (N : ℝ) * (100 * s) ≤ r)
    (hdδ : d ≤ δ / 100) (hr : 0 < r) (hrρ : r ≤ ρ / 100)
    (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty)
    (hKb : fillCells ε η (↑Θ : Set ℤ) ⊆ ball (0 : ℂ) (ρ / 2))
    (hsize : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty → Metric.diam (cell ε η k) ≤ d)
    (hF : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ (↑F0 : Set ℤ))
    (hdd : dd ε η Θ a ≤ r / 2 ∧ r / 2 ≤ ddMax ε η Θ a)
    (x : ℕ → ℤ) (hx0 : x 0 = a)
    (hleg : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hadj : ∀ u v, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty)
    (hfin : ∀ j ≤ N, exitSchedule W j x ≠ ⊤) :
    exitSchedule W N x < vExitTime (killed ε η Θ F0 r) x := by
  classical
  have hs0 : 0 < s := lt_of_lt_of_le hδ hδs
  have hsd : d ≤ s / 100 := by linarith
  have hstart := abs_le.1 (start_infDist_close hη hε hK hKb hr hrρ hdd.1 hdd.2 hsize)
  have hsN' : (N : ℝ) * s ≤ r / 100 := by linarith
  have key : ∀ j : ℕ, j ≤ N → ∃ t : ℕ, exitSchedule W j x = (t : ℕ∞) ∧
      dist (vertexPoint ε η (x t)) (vertexPoint ε η a) ≤ 3 * j * s ∧
      ∀ n ≤ t, x n ∈ killed ε η Θ F0 r := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨0, ?_, ?_, ?_⟩
      · simp [exitSchedule]
      · simp [hx0]
      · intro n hn
        have hn0 : n = 0 := by omega
        subst hn0
        rw [hx0]
        apply mem_killed_of_infDist hη hε hF
        · linarith [hstart.1, hstart.2]
        · linarith [hstart.1, hstart.2]
    | succ j ih =>
      intro hj
      obtain ⟨t, ht, hP, hQ⟩ := ih (by omega)
      have hjN : (j : ℝ) ≤ N := by exact_mod_cast (by omega : j ≤ N)
      have h2 := abs_infDist_sub_le (K := fillCells ε η (↑Θ : Set ℤ))
        (vertexPoint ε η (x t)) (vertexPoint ε η a)
      have hjr : 3 * (j : ℝ) * s ≤ 3 * r / 100 := by
        have := mul_le_mul_of_nonneg_right hjN hs0.le
        linarith
      obtain ⟨hl, hu⟩ := abs_le.1 (h2.trans hP)
      -- (C7): the distance of x_j to K
      have hinf_lo : r / 2 - d - 3 * r / 100 ≤ Metric.infDist (vertexPoint ε η (x t)) (fillCells ε η (↑Θ : Set ℤ)) := by
        linarith [hstart.1, hstart.2]
      have hinf_hi : Metric.infDist (vertexPoint ε η (x t)) (fillCells ε η (↑Θ : Set ℤ)) ≤ r / 2 + d + 3 * r / 100 := by
        linarith [hstart.1, hstart.2]
      have hinf_lt : Metric.infDist (vertexPoint ε η (x t)) (fillCells ε η (↑Θ : Set ℤ)) < r := by
        linarith
      have hinf_pos : 0 < Metric.infDist (vertexPoint ε η (x t)) (fillCells ε η (↑Θ : Set ℤ)) := by
        linarith
      have hnorm : ‖vertexPoint ε η (x t)‖ < ρ / 2 + r := norm_lt_of_infDist_lt hK hKb hinf_lt
      have hxjρ : vertexPoint ε η (x t) ∈ ball (0 : ℂ) ρ := by
        rw [mem_ball_zero_iff]
        linarith
      have hxjcell : vertexPoint ε η (x t) ∈ cell ε η (x t) := vertexPoint_mem_cell hε η (x t)
      have hzc : dist (vertexPoint ε η (x t)) (z (x t)) ≤ δ / 100 := by
        rw [dist_comm]
        exact hz (x t)
      obtain ⟨hRδ, hRs⟩ := hR (x t)
      have hWt := hW (x t)
      -- the window ball lies in B_ρ
      have hball : ball (z (x t)) (2 * R (x t)) ⊆ ball (0 : ℂ) ρ := by
        intro w hw
        rw [mem_ball] at hw ⊢
        have h1 := dist_triangle w (z (x t)) (0 : ℂ)
        have h2' := dist_triangle (z (x t)) (vertexPoint ε η (x t)) (0 : ℂ)
        have h3 : dist (vertexPoint ε η (x t)) 0 = ‖vertexPoint ε η (x t)‖ := dist_zero_right _
        have hzc' : dist (z (x t)) (vertexPoint ε η (x t)) ≤ δ / 100 := hz (x t)
        linarith
      -- the start cell is in the window
      have hxjB : vertexPoint ε η (x t) ∈ ball (z (x t)) (2 * R (x t)) := by
        rw [mem_ball]
        linarith
      have hfr : cell ε η (x t) ∩ frontier (ball (z (x t)) (2 * R (x t))) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro w ⟨hw, hwf⟩
        rw [frontier_ball _ (by linarith : (0 : ℝ) < 2 * R (x t)).ne', mem_sphere] at hwf
        have hd1 : dist w (vertexPoint ε η (x t)) ≤ d :=
          (Metric.dist_le_diam_of_mem (S6k.cell_isCompact ε hη (x t)).isBounded hw hxjcell).trans
            (hsize (x t) ⟨vertexPoint ε η (x t), hxjcell, hxjρ⟩)
        have h4 := dist_triangle w (vertexPoint ε η (x t)) (z (x t))
        linarith
      have hxtW : x t ∈ W (x t) := by
        rw [hWt]
        exact ⟨⟨vertexPoint ε η (x t), hxjcell, hxjB⟩, fun h => by
          obtain ⟨w, hw⟩ := h
          exact (Set.eq_empty_iff_forall_notMem.1 hfr) w hw⟩
      -- the exit time from the window `W (x t)`
      have hexit : exitSchedule W (j + 1) x = (t : ℕ∞) + vExitTime (W (x t)) (WalkPotential.pathShift t x) :=
        exitSchedule_succ_of_eq ht
      have hne : vExitTime (W (x t)) (WalkPotential.pathShift t x) ≠ ⊤ := by
        intro htop
        apply hfin (j + 1) hj
        rw [hexit, htop]
        simp
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
      have hspec := vExitTime_eq_coe_spec hk.symm
      have hk_out : x (t + k) ∉ W (x t) := hspec.1
      have hk_in : ∀ i < k, x (t + i) ∈ W (x t) := hspec.2
      have hk1 : 1 ≤ k := by
        by_contra hc
        have h0 : k = 0 := by omega
        subst h0
        exact hk_out (by simpa using hxtW)
      obtain ⟨k₀, hk₀⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
      have hin : ∀ n, t ≤ n → n < t + k → x n ∈ W (x t) := by
        intro n h1 h2
        have := hk_in (n - t) (by omega)
        rwa [show t + (n - t) = n by omega] at this
      -- (C10) inside the window
      have hdist_in : ∀ n, t ≤ n → n < t + k → dist (vertexPoint ε η (x n)) (vertexPoint ε η (x t)) < 3 * s := by
        intro n h1 h2
        have hmemI : x n ∈ interiorCellVertices ε η (ball (z (x t)) (2 * R (x t))) := by
          rw [← hWt]
          exact hin n h1 h2
        have hcell := cell_subset_of_mem_interior hη _ _ hmemI
        have hpt : vertexPoint ε η (x n) ∈ ball (z (x t)) (2 * R (x t)) :=
          hcell (vertexPoint_mem_cell hε η (x n))
        rw [mem_ball] at hpt
        have h4 := dist_triangle (vertexPoint ε η (x n)) (z (x t)) (vertexPoint ε η (x t))
        have hzc'' : dist (z (x t)) (vertexPoint ε η (x t)) ≤ δ / 100 := hz (x t)
        linarith
      -- (C10) at the exit vertex
      have hv_bound : dist (vertexPoint ε η (x (t + k))) (vertexPoint ε η (x t)) < 3 * s := by
        obtain ⟨k₁, hk₁⟩ : ∃ k₁, k = k₁ + 1 := ⟨k - 1, by omega⟩
        have hu : x (t + k₁) ∈ W (x t) := hk_in k₁ (by omega)
        have hlegal := hleg (t + k₁)
        have hsucc : t + k₁ + 1 = t + k := by omega
        rw [hsucc] at hlegal
        have hadjuv : (cell ε η (x (t + k₁)) ∩ cell ε η (x (t + k))).Nonempty := by
          rcases hlegal with h | h
          · exact absurd (h ▸ hu) hk_out
          · exact hadj _ _ h
        obtain ⟨p, hp1, hp2⟩ := hadjuv
        have hcellu : cell ε η (x (t + k₁)) ⊆ ball (z (x t)) (2 * R (x t)) := by
          have hmemI : x (t + k₁) ∈ interiorCellVertices ε η (ball (z (x t)) (2 * R (x t))) := by
            rw [← hWt]
            exact hu
          exact cell_subset_of_mem_interior hη _ _ hmemI
        have hpB : p ∈ ball (z (x t)) (2 * R (x t)) := hcellu hp1
        have hvB : x (t + k) ∈ cellVertices ε η (ball (z (x t)) (2 * R (x t))) := ⟨p, hp2, hpB⟩
        have hvF : (cell ε η (x (t + k)) ∩ frontier (ball (z (x t)) (2 * R (x t)))).Nonempty := by
          by_contra hne'
          exact hk_out (by rw [hWt]; exact ⟨hvB, hne'⟩)
        obtain ⟨w, hwv, hwf⟩ := hvF
        rw [frontier_ball _ (by linarith : (0 : ℝ) < 2 * R (x t)).ne', mem_sphere] at hwf
        have hpρ : p ∈ ball (0 : ℂ) ρ := by
          have := hball hpB
          exact this
        have hdiam := hsize (x (t + k)) ⟨p, hp2, hpρ⟩
        have hd1 : dist (vertexPoint ε η (x (t + k))) w ≤ d :=
          (Metric.dist_le_diam_of_mem (S6k.cell_isCompact ε hη (x (t + k))).isBounded
            (vertexPoint_mem_cell hε η (x (t + k))) hwv).trans hdiam
        have h4 := dist_triangle (vertexPoint ε η (x (t + k))) w (z (x t))
        have h5 := dist_triangle (vertexPoint ε η (x (t + k))) (z (x t)) (vertexPoint ε η (x t))
        have hzc' : dist (z (x t)) (vertexPoint ε η (x t)) ≤ δ / 100 := hz (x t)
        linarith
      refine ⟨t + k, ?_, ?_, ?_⟩
      · rw [hexit, ← hk, Nat.cast_add]
      · have h6 := dist_triangle (vertexPoint ε η (x (t + k))) (vertexPoint ε η (x t)) (vertexPoint ε η a)
        push_cast
        linarith
      · intro n hn
        by_cases hnt : n ≤ t
        · exact hQ n hnt
        · have hd3 : dist (vertexPoint ε η (x n)) (vertexPoint ε η (x t)) < 3 * s := by
            rcases Nat.lt_or_ge n (t + k) with h | h
            · exact hdist_in n (by omega) h
            · have hn' : n = t + k := by omega
              rw [hn']
              exact hv_bound
          have habs := abs_infDist_sub_le (K := fillCells ε η (↑Θ : Set ℤ))
            (vertexPoint ε η (x n)) (vertexPoint ε η (x t))
          obtain ⟨h7, h8⟩ := abs_lt.1 (lt_of_le_of_lt habs hd3)
          apply mem_killed_of_infDist hη hε hF
          · linarith
          · linarith
  obtain ⟨t, ht, -, hQ⟩ := key N le_rfl
  rw [ht]
  exact lt_vExitTime_iff'.2 hQ

end Lemma68C12

end MatedCRT
