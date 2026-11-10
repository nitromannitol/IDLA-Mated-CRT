import MatedCRT.FirstPass.S4S6c.HcPrinted68
import MatedCRT.FirstPass.S4S6c.BandInduction68

/-!
# Test starts lie in the sphere band (q2, task fp-S4S6c-envscaling-6-7-6-8; LEMMA68 C3, C11)

The trace argument of the printed Lemma 6.8 needs its test-start vertices `x_j = X_{T_j}` to satisfy two memberships:
`x_j ∈ I(B_{4R_j/3}(z_j))` (the one-test bound `HcPrinted68.hc_band_var` applies there) and `x_j ∈ band` (the window
containment `BandInduction68.window_sub` and the induction `band_induction` are stated on the band). This file proves
the deterministic memberships. The cell `H v` of a start is within `d` of its vertex point `P v` (cell-size input
`hsm`), and `P v` is within `g` of the test centre `z_v = ctr v`; the cell then lies in the open ball
`B_{4R/3}(z_v)` (`g + d < 4R/3`), so `v` is an inner vertex of that ball (`innerVertices`, Armitage-Gardiner
potential theory: the cell is interior, so it does not meet the frontier `∂B`).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT

namespace StartBand68

/-- A vertex whose (nonempty) cell lies in an open set `D` is an inner vertex of `D`: the cell meets `D` and does not
meet the frontier `∂D = closure D \ D`. -/
theorem mem_innerVertices_of_sub {H : ℤ → Set ℂ} {D : Set ℂ} {v : ℤ} (hD : IsOpen D)
    (hne : (H v).Nonempty) (hsub : H v ⊆ D) : v ∈ innerVertices H D := by
  obtain ⟨x, hx⟩ := hne
  refine Set.mem_sdiff_of_mem (show (H v ∩ D).Nonempty from ⟨x, hx, hsub hx⟩) ?_
  rintro ⟨y, hy, hyF⟩
  rw [hD.frontier_eq] at hyF
  exact hyF.2 (hsub hy)

/-- A start `v` whose cell lies within `d` of `P v`, with the centre `ctr v` within `g` of `P v` and
`g + d < 4 R_v / 3`, is in the sphere band `I(B_{4R_v/3}(ctr v))`. -/
theorem mem_bandSet_of_cell {H : ℤ → Set ℂ} {P ctr : ℤ → ℂ} {rad : ℤ → ℝ} {d g : ℝ} {v : ℤ}
    (hne : (H v).Nonempty) (hsub : H v ⊆ closedBall (P v) d) (hctr : dist (ctr v) (P v) ≤ g)
    (hlt : g + d < 4 * rad v / 3) : v ∈ HcPrinted68.bandSet H ctr rad := by
  show v ∈ innerVertices H (ball (ctr v) (4 * rad v / 3))
  refine mem_innerVertices_of_sub isOpen_ball hne ?_
  intro u hu
  rw [mem_ball]
  have h1 : dist u (P v) ≤ d := mem_closedBall.1 (hsub hu)
  linarith [dist_triangle u (P v) (ctr v), dist_comm (P v) (ctr v)]

/-- **Test starts are in the band and in the sphere band.** For a vertex `v` with vertex point `P v` in its cell
`H v`, a test centre `ctr v` within `g` of `P v`, radius `rad v ≥ 0` with `g + d < 4 rad v / 3`, and cell-size input
`hsm` at the test (cells meeting `B_{2 rad v}(ctr v)` have diameter at most `d`), together with the start distance
`dist (P v) (P b) ≤ 3r/100` from the frontier start `b` (`band_induction`), the vertex `v` lies in
`band P F r d ∩ bandSet H ctr rad`. -/
theorem start_mem_band_inter {H : ℤ → Set ℂ} {P ctr : ℤ → ℂ} {rad : ℤ → ℝ} {F : Set ℂ} {r d g : ℝ} {v b : ℤ}
    (hd : 0 ≤ d) (hstart : |Metric.infDist (P b) F - r / 2| ≤ d) (hv : dist (P v) (P b) ≤ 3 * r / 100)
    (hPv : P v ∈ H v)
    (hsm : ∀ v', (closure (H v') ∩ closedBall (ctr v) (2 * rad v)).Nonempty →
      ∀ x ∈ closure (H v'), ∀ y' ∈ closure (H v'), dist x y' ≤ d)
    (hctr : dist (ctr v) (P v) ≤ g) (hR0 : 0 ≤ rad v) (hlt : g + d < 4 * rad v / 3) :
    v ∈ BandInduction68.band P F r d ∩ HcPrinted68.bandSet H ctr rad := by
  have hg2 : g ≤ 2 * rad v := by linarith
  have hsub : H v ⊆ closedBall (P v) d := by
    intro u hu
    have hmeet : (closure (H v) ∩ closedBall (ctr v) (2 * rad v)).Nonempty :=
      ⟨P v, subset_closure hPv, mem_closedBall.2 (by rw [dist_comm]; linarith)⟩
    exact mem_closedBall.2 (hsm v hmeet u (subset_closure hu) (P v) (subset_closure hPv))
  have hne : (H v).Nonempty := ⟨P v, hPv⟩
  exact ⟨BandInduction68.mem_band_of_dist hd hstart hv, mem_bandSet_of_cell hne hsub hctr hlt⟩

end StartBand68

end MatedCRT

#print axioms MatedCRT.StartBand68.start_mem_band_inter
