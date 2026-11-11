import MatedCRT.FirstPass.S4S6c.BandInduction68
import MatedCRT.FirstPass.S4S6c.FrontierSeparation

/-!
# Frontier starts, the rounding map and cell diameters of the printed Lemma 6.8

Deterministic inputs of `BandInduction68` (C5):

* `start_dist_of_frontier`: a frontier vertex `b` of `U₁ = thickening (r/2) F` (a cell meeting `∂U₁`) has
  `|dist(P b, F) - r/2| ≤ d`, where `d` bounds the cell diameter (hypothesis `hstart` of `BandInduction68`).
* `roundC`, `dist_roundC_le`: the Borel rounding map `Q_δ`, `Q_δ(x₁,x₂) = g(⌊x₁/g + 1/2⌋, ⌊x₂/g + 1/2⌋)`,
  with `|Q_δ(x) - x| ≤ g`; the test centre is `ctr v = Q_δ(P v)`, hypothesis `hctr`.
* `dist_le_of_diam_le`: a cell of diameter at most `d` (the cell-size estimate, `CellSizeEstimateStmt`) has all pairs of
  closure points at distance at most `d` (hypothesis `hsm` of `BandInduction68`), for bounded cells.

No probability input. Terminology: infimal distance to a set (Armitage-Gardiner), frontier of a thickening.
-/

open Set Metric

namespace MatedCRT

namespace FrontierStart68

/-- Points of the frontier of `thickening t F` have infimal distance `t` to `F` (for `t ≥ 0`). -/
theorem infDist_eq_of_mem_frontier {F : Set ℂ} {t : ℝ} (ht : 0 ≤ t) {u : ℂ}
    (hu : u ∈ frontier (thickening t F)) : infDist u F = t := by
  have h : infEDist u F = ENNReal.ofReal t := Metric.frontier_thickening_subset F hu
  rw [infDist, h, ENNReal.toReal_ofReal ht]

/-- **Frontier start.** For a vertex `b` whose cell meets the frontier of `U₁ = thickening (r/2) F`, the
vertex point `P b` satisfies `|dist(P b, F) - r/2| ≤ d`. The frontier point `u` lies in `B_ρ` (its distance to `F` is
`r/2`, and `r ≤ ρ/100`), so the cell-size bound `hsm` applies to the cell of `b`. -/
theorem start_dist_of_frontier {H : ℤ → Set ℂ} {P : ℤ → ℂ} {F : Set ℂ} {r ρ d : ℝ} {b : ℤ}
    (hr : 0 < r) (hrρ : r ≤ ρ / 100) (hFne : F.Nonempty) (hFball : F ⊆ ball (0 : ℂ) (ρ / 2))
    (hPmem : ∀ v, P v ∈ H v)
    (hsm : ∀ v, (H v ∩ ball (0 : ℂ) ρ).Nonempty → ∀ u ∈ closure (H v), ∀ u' ∈ closure (H v), dist u u' ≤ d)
    (hb : b ∈ FrontierSeparation.frontierVerts H (thickening (r / 2) F)) :
    |infDist (P b) F - r / 2| ≤ d := by
  obtain ⟨u, hucl, hufr⟩ := hb
  have hinf : infDist u F = r / 2 := infDist_eq_of_mem_frontier (by linarith) hufr
  have hnorm : ‖u‖ < ρ := by
    have h := BandInduction68.norm_lt_of_infDist (p := u) (t := r / 2 + ρ / 4) hFball hFne
      (by rw [hinf]; linarith)
    have hρpos : 0 < ρ := by linarith
    linarith
  have hHb : (H b ∩ ball (0 : ℂ) ρ).Nonempty := by
    have h := (_root_.mem_closure_iff.1 hucl) (ball (0 : ℂ) ρ) isOpen_ball (mem_ball_zero_iff.2 hnorm)
    rwa [inter_comm] at h
  have hd := hsm b hHb (P b) (subset_closure (hPmem b)) u hucl
  have hlip := BandInduction68.abs_infDist_sub_le F (P b) u
  rw [hinf] at hlip
  exact hlip.trans hd

/-- The rounding map `Q_δ`on `ℂ` with mesh `g = δ/100`:
`Q_δ(x₁, x₂) = g (⌊x₁/g + 1/2⌋, ⌊x₂/g + 1/2⌋)` (Borel, coordinatewise). -/
noncomputable def roundC (g : ℝ) (z : ℂ) : ℂ :=
  ⟨g * (⌊z.re / g + 1 / 2⌋ : ℝ), g * (⌊z.im / g + 1 / 2⌋ : ℝ)⟩

/-- One coordinate of the rounding map moves by at most `g/2`. -/
theorem abs_round_coord_le {g : ℝ} (hg : 0 < g) (x : ℝ) :
    |g * (⌊x / g + 1 / 2⌋ : ℝ) - x| ≤ g / 2 := by
  have hx : x = g * (x / g) := by field_simp
  have h1 := Int.floor_le (x / g + 1 / 2)
  have h2 := Int.lt_floor_add_one (x / g + 1 / 2)
  have hA := mul_le_mul_of_nonneg_left h1 hg.le
  have hB := mul_lt_mul_of_pos_left h2 hg
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- **Rounding.** `dist(Q_δ z, z) ≤ g`, using `‖w‖ ≤ |re w| + |im w|` on `ℂ`. -/
theorem dist_roundC_le {g : ℝ} (hg : 0 < g) (z : ℂ) : dist (roundC g z) z ≤ g := by
  rw [dist_eq_norm]
  calc ‖roundC g z - z‖ ≤ |(roundC g z - z).re| + |(roundC g z - z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |(roundC g z).re - z.re| + |(roundC g z).im - z.im| := by
        simp [Complex.sub_re, Complex.sub_im]
    _ ≤ g / 2 + g / 2 := by
        have hre : (roundC g z).re = g * (⌊z.re / g + 1 / 2⌋ : ℝ) := rfl
        have him : (roundC g z).im = g * (⌊z.im / g + 1 / 2⌋ : ℝ) := rfl
        rw [hre, him]
        linarith [abs_round_coord_le hg z.re, abs_round_coord_le hg z.im]
    _ = g := by ring

/-- **Cell-size bound in pointwise form (`hsm` of `BandInduction68`).** For a bounded cell of diameter at most `d`
(the cell-size estimate `CellSizeEstimateStmt`, cells meeting `B_ρ`), any two points of its closure are within `d`. -/
theorem dist_le_of_diam_le {s : Set ℂ} {d : ℝ} (hb : Bornology.IsBounded s) (hdiam : diam s ≤ d)
    {u u' : ℂ} (hu : u ∈ closure s) (hu' : u' ∈ closure s) : dist u u' ≤ d := by
  have h := Metric.dist_le_diam_of_mem hb.closure hu hu'
  rw [Metric.diam_closure] at h
  linarith

end FrontierStart68

end MatedCRT

/-! ## Audit -/
#print axioms MatedCRT.FrontierStart68.start_dist_of_frontier
#print axioms MatedCRT.FrontierStart68.dist_roundC_le
#print axioms MatedCRT.FrontierStart68.dist_le_of_diam_le
