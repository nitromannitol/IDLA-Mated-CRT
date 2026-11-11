import MatedCRT.FirstPass.S4S6c.AnnulusGeometry68

/-!
# The open annulus of the good-annulus event

`IsGoodAnnulusEvent μ c₀ C r z` (Defs/Setting.lean:333) integrates over the open annulus
`A_{r,2r}(z) = B_{2r}(z) \ cl B_r(z)` (paper line 383: `A_{r1,r2}(z) = B_{r2}(z) \ cl(B_{r1}(z))`). The good-annulus
bound `hF` therefore lives on this open annulus `openAnnulus z R`, not on the closed `closedAnnulus z R`
(AnnulusGeometry68.lean:21), whose two boundary circles the event does not control.

The test disk `B_{R/4}(x)` and its `δ`-thickening, with `‖x - z‖ ∈ [4R/3 - R/100, 4R/3 + R/100]` and `δ ≤ R/100`,
lie strictly inside `A_{R,2R}(z)` (room `R/12` at both circles), and the sphere `sphere z (3R/2)` is an interior circle.

Terminology: Armitage-Gardiner potential kernel `log(1/|u - v|)`; Duplantier-Sheffield annulus; LQG measure `μ`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace MatedCRT

/-- The open annulus `A_{R,2R}(z) = B_{2R}(z) \ cl B_R(z)` of the good-annulus event (`HarmonicBalls.annulus z R (2 * R)`). -/
abbrev openAnnulus (z : ℂ) (R : ℝ) : Set ℂ := HarmonicBalls.annulus z R (2 * R)

theorem mem_openAnnulus {z u : ℂ} {R : ℝ} : u ∈ openAnnulus z R ↔ R < ‖u - z‖ ∧ ‖u - z‖ < 2 * R := by
  unfold openAnnulus HarmonicBalls.annulus
  simp only [mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm, not_le]
  exact and_comm

theorem isOpen_openAnnulus (z : ℂ) (R : ℝ) : IsOpen (openAnnulus z R) := by
  unfold openAnnulus HarmonicBalls.annulus
  rw [Set.sdiff_eq]
  exact isOpen_ball.inter isClosed_closedBall.isOpen_compl

theorem openAnnulus_subset_closedBall (z : ℂ) (R : ℝ) : openAnnulus z R ⊆ closedBall z (2 * R) := by
  intro u hu
  rw [mem_closedBall, dist_eq_norm]
  exact (mem_openAnnulus.1 hu).2.le

theorem sphere_subset_openAnnulus {z : ℂ} {R : ℝ} (hR : 0 < R) :
    sphere z (3 * R / 2) ⊆ openAnnulus z R := by
  intro u hu
  have h : ‖u - z‖ = 3 * R / 2 := by
    rw [mem_sphere, dist_eq_norm] at hu
    exact hu
  rw [mem_openAnnulus, h]
  constructor <;> linarith

/-- A point `u` with `‖u - x‖ ≤ R/4 + R/100`, where `‖x - z‖` lies in the window `4R/3 ± R/100`, lies in the open
annulus `A_{R,2R}(z)`. -/
theorem mem_openAnnulus_of_dist_le {x z u : ℂ} {R : ℝ} (hR : 0 < R)
    (hx : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100)
    (hu : ‖u - x‖ ≤ R / 4 + R / 100) : u ∈ openAnnulus z R := by
  obtain ⟨hx1, hx2⟩ := hx
  rw [mem_openAnnulus]
  have h1 : ‖u - z‖ ≤ ‖u - x‖ + ‖x - z‖ := by
    have h := norm_add_le (u - x) (x - z)
    rwa [sub_add_sub_cancel] at h
  have h2 : ‖x - z‖ - ‖u - z‖ ≤ ‖u - x‖ := by
    have h := norm_sub_norm_le (x - z) (u - z)
    rwa [show (x - z) - (u - z) = -(u - x) by ring, norm_neg] at h
  constructor <;> linarith

theorem ball_subset_openAnnulus {x z : ℂ} {R : ℝ} (hR : 0 < R)
    (hx : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100) :
    ball x (R / 4) ⊆ openAnnulus z R := by
  intro u hu
  rw [mem_ball, dist_eq_norm] at hu
  exact mem_openAnnulus_of_dist_le hR hx (by linarith)

theorem thickening_ball_subset_openAnnulus {x z : ℂ} {R δ : ℝ} (hR : 0 < R)
    (hx : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100) (hδ : δ ≤ R / 100) :
    thickening δ (ball x (R / 4)) ⊆ openAnnulus z R := by
  intro u hu
  obtain ⟨y, hy, huy⟩ := (mem_thickening_iff).1 hu
  rw [mem_ball, dist_eq_norm] at hy
  rw [dist_eq_norm] at huy
  have h : ‖u - x‖ ≤ ‖u - y‖ + ‖y - x‖ := by
    have h' := norm_add_le (u - y) (y - x)
    rwa [sub_add_sub_cancel] at h'
  exact mem_openAnnulus_of_dist_le hR hx (by linarith)

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.mem_openAnnulus_of_dist_le
#print axioms MatedCRT.thickening_ball_subset_openAnnulus
