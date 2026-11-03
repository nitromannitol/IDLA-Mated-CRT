import MatedCRT.Defs.Setting

/-!
# Geometry of the annuli of Section 6.2 (eq:annulus, line 383)

Elementary facts about the open annuli `𝔸_{r₁,r₂}(z) = B_{r₂}(z) \ cl(B_{r₁}(z))` used in Lemmas 6.4 and 6.5: the
good annulus event `E_r(z)` (eq:good-annulus-event) only involves `μ_h` on its *region of dependence*
`𝔸_{r/3,3r}(z)`, which contains `𝔸_{r,2r}(z)` and the balls `B_{𝐜₀ r}(w)`, `w ∈ 𝔸_{r,2r}(z)`; on an admissible
region (`dist(𝔸_{r/3,3r}(z), 0) ≥ r/100`) the modulus `|·|` oscillates by a factor at most `601`.
-/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls
open scoped ENNReal

/-- Membership in the open annulus `𝔸_{r₁,r₂}(z)` through `|u - z|`. -/
theorem mem_annulus_iff_norm {z u : ℂ} {r₁ r₂ : ℝ} :
    u ∈ annulus z r₁ r₂ ↔ r₁ < ‖u - z‖ ∧ ‖u - z‖ < r₂ := by
  simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le, dist_eq_norm]
  tauto

/-- The open annulus is open. -/
theorem isOpen_annulus' (z : ℂ) (r₁ r₂ : ℝ) : IsOpen (annulus z r₁ r₂) := by
  have : annulus z r₁ r₂ = {u : ℂ | r₁ < ‖u - z‖} ∩ {u : ℂ | ‖u - z‖ < r₂} := by
    ext u; simp only [mem_annulus_iff_norm, mem_inter_iff, mem_ofPred_eq]
  rw [this]
  have hc : Continuous fun u : ℂ => ‖u - z‖ := continuous_norm.comp (continuous_id.sub continuous_const)
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

/-- The open annulus is measurable. -/
theorem measurableSet_annulus' (z : ℂ) (r₁ r₂ : ℝ) : MeasurableSet (annulus z r₁ r₂) :=
  (isOpen_annulus' z r₁ r₂).measurableSet

/-- `z + r ∈ 𝔸_{r/3,3r}(z)`: the region of dependence is nonempty. -/
theorem add_mem_region {z : ℂ} {r : ℝ} (hr : 0 < r) : z + (r : ℂ) ∈ annulus z (r / 3) (3 * r) := by
  rw [mem_annulus_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  constructor <;> linarith

/-- `𝔸_{r,2r}(z) ⊆ 𝔸_{r/3,3r}(z)`. -/
theorem annulus_subset_region {z : ℂ} {r : ℝ} (hr : 0 < r) :
    annulus z r (2 * r) ⊆ annulus z (r / 3) (3 * r) := by
  intro u hu
  rw [mem_annulus_iff_norm] at hu ⊢
  exact ⟨(div_lt_self hr (by norm_num)).trans hu.1, hu.2.trans (mul_lt_mul_of_pos_right (by norm_num) hr)⟩

/-- For `w ∈ 𝔸_{r,2r}(z)` and `𝐜₀ < 1/5`, `B_{𝐜₀ r}(w) ⊆ 𝔸_{r/3,3r}(z)`. -/
theorem ball_subset_region {z w : ℂ} {r c₀ : ℝ} (hr : 0 < r) (hc₀ : c₀ < 1 / 5)
    (hw : w ∈ annulus z r (2 * r)) : ball w (c₀ * r) ⊆ annulus z (r / 3) (3 * r) := by
  intro u hu
  rw [mem_annulus_iff_norm] at hw ⊢
  rw [mem_ball, dist_eq_norm] at hu
  have h1 := norm_sub_le_norm_sub_add_norm_sub u w z
  have h2 := norm_sub_le_norm_sub_add_norm_sub w u z
  rw [norm_sub_rev w u] at h2
  have hcr : c₀ * r < r / 5 := by nlinarith
  constructor <;> linarith [hw.1, hw.2]

/-- Admissibility of the annuli of Lemma 6.4 for Lemma 6.5: if `z ∈ B_{ρ - 3s} \ B_{10 s}` and `0 < r ≤ s`, then
`𝔸_{r/3,3r}(z) ⊆ B_ρ` and `dist(𝔸_{r/3,3r}(z), 0) ≥ r/100`. -/
theorem annulus_region_admissible {ρ s r : ℝ} {z : ℂ} (hr : 0 < r) (hrs : r ≤ s)
    (hz : z ∈ ball (0 : ℂ) (ρ - 3 * s) \ ball 0 (10 * s)) :
    annulus z (r / 3) (3 * r) ⊆ ball 0 ρ ∧ r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r)) := by
  simp only [mem_sdiff, mem_ball, dist_zero_right, not_lt] at hz
  refine ⟨fun u hu => ?_, ?_⟩
  · rw [mem_annulus_iff_norm] at hu
    rw [mem_ball, dist_zero_right]
    have h := norm_add_le (u - z) z
    rw [sub_add_cancel] at h
    linarith [hu.2]
  · refine (le_infDist ⟨_, add_mem_region hr⟩).2 fun u hu => ?_
    rw [mem_annulus_iff_norm] at hu
    rw [dist_zero_left]
    have h := norm_add_le (z - u) u
    rw [sub_add_cancel, norm_sub_rev] at h
    linarith [hu.2]

/-- On an admissible region of dependence the modulus oscillates by a factor at most `601`. -/
theorem norm_le_mul_norm_of_mem_region {r : ℝ} {z x y : ℂ}
    (hdist : r / 100 ≤ infDist 0 (annulus z (r / 3) (3 * r)))
    (hx : x ∈ annulus z (r / 3) (3 * r)) (hy : y ∈ annulus z (r / 3) (3 * r)) :
    ‖x‖ ≤ 601 * ‖y‖ ∧ r / 100 ≤ ‖y‖ := by
  have hy0 : r / 100 ≤ ‖y‖ := by
    have := infDist_le_dist_of_mem hy (x := (0 : ℂ))
    rw [dist_zero_left] at this
    linarith
  refine ⟨?_, hy0⟩
  rw [mem_annulus_iff_norm] at hx hy
  have h1 := norm_add_le (x - y) y
  rw [sub_add_cancel] at h1
  have h2 := norm_sub_le_norm_sub_add_norm_sub x z y
  rw [norm_sub_rev z y] at h2
  linarith [hx.2, hy.2]

end MatedCRT
