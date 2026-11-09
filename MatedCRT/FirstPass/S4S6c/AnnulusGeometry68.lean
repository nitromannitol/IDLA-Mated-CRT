import MatedCRT.FirstPass.S4S6c.PrintedGreen68

/-!
# LEMMA68 annulus geometry of the test disk (q2, task fp-S4S6c-envscaling-6-7-6-8; write-up B5, B6)

The closed annulus `A_{R,2R}(z) = {u : R ≤ |u - z| ≤ 2R}` (Terminology: the annulus of Lemma 1 of LEMMA68, eq (4)).
Write-up B5-B6: with `x` at distance `4R/3 ± d` from `z`, `d ≤ R/100` (cell-size bound), the test disk
`D = B_{R/4}(x)` and its `δ`-thickening `E = B_δ(D)` with `δ ≤ R/100` lie in `A_{R,2R}(z)`. Consequently the
potential supremum of `draft_sup_le_of_annulus` (PrintedGreen68.lean) applies with `A = A_{R,2R}(z)`, and only the
good-annulus bound `hF`, the integrability `hint` and the finiteness `μ A ≠ ⊤` remain as inputs.

Terminology: Armitage-Gardiner potential kernel `log(1/|u - v|)`; LQG measure `μ`; Duplantier-Sheffield annulus.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace MatedCRT

/-- The closed annulus `A_{R,2R}(z) = {u : R ≤ |u - z| ≤ 2R}` (LEMMA68 Lemma 1 domain, write-up B6). -/
def closedAnnulus (z : ℂ) (R : ℝ) : Set ℂ := {u | R ≤ ‖u - z‖ ∧ ‖u - z‖ ≤ 2 * R}

theorem isClosed_closedAnnulus (z : ℂ) (R : ℝ) : IsClosed (closedAnnulus z R) := by
  unfold closedAnnulus
  have hc : Continuous fun u : ℂ => ‖u - z‖ := continuous_norm.comp (continuous_id.sub continuous_const)
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

theorem closedAnnulus_subset_closedBall (z : ℂ) (R : ℝ) :
    closedAnnulus z R ⊆ closedBall z (2 * R) := by
  intro u hu
  rw [mem_closedBall, dist_eq_norm]
  exact hu.2

theorem sphere_subset_closedAnnulus {z : ℂ} {R : ℝ} (hR : 0 < R) :
    sphere z (3 * R / 2) ⊆ closedAnnulus z R := by
  intro u hu
  have h : ‖u - z‖ = 3 * R / 2 := by
    rw [mem_sphere, dist_eq_norm] at hu
    exact hu
  show R ≤ ‖u - z‖ ∧ ‖u - z‖ ≤ 2 * R
  rw [h]
  constructor <;> linarith

/-- A point within `e` of a centre `x` with `|x - z| ∈ [4R/3 - R/100, 4R/3 + R/100]` lies in `A_{R,2R}(z)`,
when `e ≤ R/4 + R/100`. -/
theorem mem_closedAnnulus_of_norm_sub_le {x z u : ℂ} {R e : ℝ} (hR : 0 < R)
    (hx : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100)
    (hu : ‖u - x‖ ≤ e) (he : e ≤ R / 4 + R / 100) :
    u ∈ closedAnnulus z R := by
  have hxz : ‖x - z‖ - ‖x - u‖ ≤ ‖u - z‖ := by
    have h := norm_sub_norm_le (x - z) (x - u)
    have e1 : (x - z) - (x - u) = u - z := by ring
    rw [e1] at h
    exact h
  have hxu : ‖x - u‖ = ‖u - x‖ := norm_sub_rev x u
  have hup : ‖u - z‖ ≤ ‖x - z‖ + ‖u - x‖ := by
    have h := norm_add_le (u - x) (x - z)
    have e1 : (u - x) + (x - z) = u - z := by ring
    rw [e1] at h
    linarith [norm_sub_rev u x]
  show R ≤ ‖u - z‖ ∧ ‖u - z‖ ≤ 2 * R
  constructor
  · linarith [hx.1]
  · linarith [hx.2]

/-- The test disk `D = B_{R/4}(x)` lies in the annulus `A_{R,2R}(z)` (write-up B6). -/
theorem ball_subset_closedAnnulus {x z : ℂ} {R : ℝ} (hR : 0 < R)
    (hx : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100) :
    ball x (R / 4) ⊆ closedAnnulus z R := by
  intro u hu
  have h : ‖u - x‖ ≤ R / 4 := by
    rw [mem_ball, dist_eq_norm] at hu
    exact hu.le
  exact mem_closedAnnulus_of_norm_sub_le hR hx h (by linarith)

/-- The `δ`-thickening `E = B_δ(B_{R/4}(x))` lies in the annulus `A_{R,2R}(z)` when `δ ≤ R/100` (write-up B6,
`E ⊂ A_{R,2R}(z)`). -/
theorem thickening_ball_subset_closedAnnulus {x z : ℂ} {R δ : ℝ} (hR : 0 < R)
    (hx : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100) (hδ : δ ≤ R / 100) :
    thickening δ (ball x (R / 4)) ⊆ closedAnnulus z R := by
  intro u hu
  obtain ⟨p, hp, hup⟩ := Metric.mem_thickening_iff.mp hu
  have h1 : dist u p < δ := hup
  have h2 : dist p x < R / 4 := Metric.mem_ball.mp hp
  have h3 : ‖u - x‖ ≤ R / 4 + R / 100 := by
    rw [dist_eq_norm] at h1 h2
    have t := norm_add_le (u - p) (p - x)
    have e1 : (u - p) + (p - x) = u - x := by ring
    rw [e1] at t
    linarith
  exact mem_closedAnnulus_of_norm_sub_le hR hx h3 le_rfl

/-- **Potential supremum on a test disk** (LEMMA68 eq (21), write-up B5-B6): for the test disk `D = B_{R/4}(x)` with
`|x - z| ∈ [4R/3 ± R/100]` and thickening `δ ≤ R/100`, the supremum of the Draft Lemma 2.18 kernel integral over
`E = B_δ(D)` is at most the Lemma 1 bound, with `A = A_{R,2R}(z)`. The inputs are the good-annulus bound `hF`, the
integrability `hint` and the finiteness `μ A ≠ ⊤`; the geometry is discharged here. -/
theorem draft_sup_le_of_centre {x z : ℂ} {R C mr δ : ℝ} (μ : Measure ℂ) [SFinite μ]
    (hR0 : 0 < R) (hR1 : R ≤ 1)
    (hx : 4 * R / 3 - R / 100 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 4 * R / 3 + R / 100)
    (hδ : δ ≤ R / 100)
    (hμA : μ (closedAnnulus z R) ≠ ⊤)
    (hC : 0 ≤ C) (hmr : 0 ≤ mr)
    (hint : ∀ v ∈ ball x (R / 4),
      IntegrableOn (fun u : ℂ => Real.log (R / ‖u - v‖) + 1) (closedAnnulus z R) μ)
    (hF : ∀ w ∈ closedAnnulus z R,
      ∫ u in closedAnnulus z R, (Real.log (R / ‖u - w‖) + 1) ∂μ ≤ C * mr) :
    (⨆ v ∈ ball x (R / 4), ∫⁻ u in thickening δ (ball x (R / 4)),
        ENNReal.ofReal (Real.log (1 / ‖v - u‖) + 1) ∂μ) ≤
      ENNReal.ofReal (C * mr * (1 + (Real.log 4 - 1)) * (1 + Real.log (1 / R)) / (1 - Real.log 2)) :=
  draft_sup_le_of_annulus μ hR0 hR1 (by linarith) (isClosed_closedAnnulus z R).measurableSet
    (closedAnnulus_subset_closedBall z R) hμA (sphere_subset_closedAnnulus hR0)
    (ball_subset_closedAnnulus hR0 hx) (thickening_ball_subset_closedAnnulus hR0 hx hδ) hC hmr hint hF

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.draft_sup_le_of_centre
#print axioms MatedCRT.thickening_ball_subset_closedAnnulus
