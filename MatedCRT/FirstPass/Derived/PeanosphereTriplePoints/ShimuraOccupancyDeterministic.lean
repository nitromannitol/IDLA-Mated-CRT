import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyDrop

/-!
# A deterministic criterion for the occupation of a later cell

Fix a mesh `1/n`, a first cell `k` and a later cell `l = k + j`, and write `b = k/n`, `A = (k + j - 1)/n`,
`Bl = (k + j)/n = A + 1/n`, `sd = √((j - 1)/n)`.  This file shows that a path lies in
`firstCellEvent n k ∩ cellEvent n (k + j)` as soon as it has the following pieces, which are independent
events for a correlated Brownian pair:

* the past event `pastEvent n k` and the tameness event `tameEvent n k j` (both drops across the cell `k`
  are at most `sd`);
* a level `θ ≤ cellDropR n k p` and a gap piece on `[b, A]`: the second coordinate stays above its value at
  `b` minus `θ` and ends above it plus `sd`, while the first coordinate stays above its value at `A` minus
  `e` and ends below its value at `b` minus `sd`;
* a piece on the cell `l = [A, Bl]`: the first coordinate drops by `2 e` below its value at `A`,
  the second drops by `2 e` below its value at `Bl`, stays above its value at `A` minus `4 e`, and
  `R Bl ≥ R A - e`;
* a final piece: the second coordinate stays above `R Bl - 2 e` on `[Bl, Bl + 2 - 1/n]`.

The proof combines the description of the first occupied cell (answer §2, `mem_firstCellEvent_iff`) for the
right test at `k` and the left and right tests at `k + j` directly.  It uses no measure.
-/

set_option autoImplicit false

open Set
open MatedCRTHarmonic.MatedCRT (Path2)

namespace MatedCRT.PeanosphereTriplePoints

/-- **Occupation of the cell `k + j` from deterministic pieces.** A path in the past event and the tameness
event of the cell `k`, which has the gap, cell and final pieces described in the module documentation
at the level `θ ≤ cellDropR n k p`, lies in `firstCellEvent n k ∩ cellEvent n (k + j)`. -/
theorem mem_firstCell_inter_cell_of_pieces {n k j : ℕ} (hn : 1 ≤ n) (_hk : 1 ≤ k) (hkn : k ≤ n)
    (_hkj : k + j ≤ 2 * n) (_hj : 2 ≤ j) {p : Path2} {θ e : ℝ} (he : 0 < e)
    (_hen : e ^ 2 = 1 / (n : ℝ)) (hsd : 4 * e ≤ Real.sqrt (((j : ℝ) - 1) / n))
    (hpast : p ∈ pastEvent n k) (htame : p ∈ tameEvent n k j) (_hθ0 : 0 ≤ θ)
    (hlev : θ ≤ cellDropR n k p)
    (hgap : (∀ s ∈ Icc ((k : ℝ) / n) (((k : ℝ) + j - 1) / n),
        (p ((k : ℝ) / n)).2 - θ ≤ (p s).2) ∧
      (p ((k : ℝ) / n)).2 + Real.sqrt (((j : ℝ) - 1) / n) ≤ (p (((k : ℝ) + j - 1) / n)).2 ∧
      (∀ s ∈ Icc ((k : ℝ) / n) (((k : ℝ) + j - 1) / n),
        (p (((k : ℝ) + j - 1) / n)).1 - e ≤ (p s).1) ∧
      (p (((k : ℝ) + j - 1) / n)).1 ≤ (p ((k : ℝ) / n)).1 - Real.sqrt (((j : ℝ) - 1) / n))
    (hpoly : (∃ s ∈ Icc (((k : ℝ) + j - 1) / n) (((k : ℝ) + j) / n),
        (p s).1 ≤ (p (((k : ℝ) + j - 1) / n)).1 - 2 * e) ∧
      (∃ s ∈ Icc (((k : ℝ) + j - 1) / n) (((k : ℝ) + j) / n),
        (p s).2 ≤ (p (((k : ℝ) + j) / n)).2 - 2 * e) ∧
      (∀ s ∈ Icc (((k : ℝ) + j - 1) / n) (((k : ℝ) + j) / n),
        (p (((k : ℝ) + j - 1) / n)).2 - 4 * e ≤ (p s).2) ∧
      (p (((k : ℝ) + j - 1) / n)).2 - e ≤ (p (((k : ℝ) + j) / n)).2)
    (hafter : ∀ u ∈ Icc (((k : ℝ) + j) / n) (((k : ℝ) + j) / n + (2 - 1 / (n : ℝ))),
      (p (((k : ℝ) + j) / n)).2 - 2 * e ≤ (p u).2) :
    p ∈ firstCellEvent n k ∩ cellEvent n (k + j) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hpast' : priorCellsFail n k (fun t => (p t).1) (fun t => (p t).2) := hpast
  have htame' : cellDropR n k p ≤ Real.sqrt (((j : ℝ) - 1) / n) ∧
      cellDropL n k p ≤ Real.sqrt (((j : ℝ) - 1) / n) := htame
  have hV := (cellDropL_le_iff n k p _).1 htame'.2
  have hU0 := cellDropR_nonneg n k p
  obtain ⟨g1, g2, g3, g4⟩ := hgap
  obtain ⟨⟨sL, hsL, hsL'⟩, ⟨sR, hsR, hsR'⟩, hp3, hp4⟩ := hpoly
  have hak_le_A : ((k : ℝ) - 1) / n ≤ ((k : ℝ) + j - 1) / n :=
    div_le_div_of_nonneg_right (by linarith) hnR.le
  have hb_le_Bl : (k : ℝ) / n ≤ ((k : ℝ) + j) / n :=
    div_le_div_of_nonneg_right (by linarith) hnR.le
  have hAeq : ((k : ℝ) + j - 1) / n = ((k : ℝ) + j) / n - 1 / n := sub_div _ _ _
  have hBT : ((k : ℝ) + j) / n + (2 - 1 / (n : ℝ)) = ((k : ℝ) + j - 1) / n + 2 := by
    linarith
  refine ⟨(mem_firstCellEvent_iff hn (by omega) p).2 ⟨hpast', ?_⟩, ?_⟩
  · -- the right test at `k`
    obtain ⟨s0, hs0, hU⟩ := exists_eq_cellDropR n k p
    refine ⟨s0, hs0, fun u hu => ?_⟩
    show (p s0).2 ≤ (p u).2
    by_cases h1 : u ≤ ((k : ℝ) + j - 1) / n
    · have := g1 u ⟨hu.1, h1⟩
      linarith
    · by_cases h2 : u ≤ ((k : ℝ) + j) / n
      · have := hp3 u ⟨(not_le.1 h1).le, h2⟩
        linarith [htame'.1]
      · have hu3 := hafter u ⟨(not_le.1 h2).le, by linarith [hu.2]⟩
        linarith [htame'.1]
  · -- the tests at `k + j`
    show ShimuraCell n (k + j) (fun t => (p t).1) (fun t => (p t).2)
    unfold ShimuraCell
    push_cast
    refine ⟨⟨sL, hsL, fun u hu => ?_⟩, ⟨sR, hsR, fun u hu => ?_⟩⟩
    · by_cases c1 : (k : ℝ) / n ≤ u
      · have := g3 u ⟨c1, hu.2⟩
        linarith
      · by_cases c2 : ((k : ℝ) - 1) / n ≤ u
        · have := hV u ⟨c2, (not_le.1 c1).le⟩
          linarith
        · obtain ⟨s', hs', hLs'⟩ := hpast'.1
          have h1 := hLs' u ⟨by linarith [hu.1], (not_le.1 c2).le⟩
          have h2 := hV s' hs'
          have h1' : (p s').1 ≤ (p u).1 := h1
          linarith
    · have := hafter u ⟨hu.1, by linarith [hu.2]⟩
      linarith

end MatedCRT.PeanosphereTriplePoints
