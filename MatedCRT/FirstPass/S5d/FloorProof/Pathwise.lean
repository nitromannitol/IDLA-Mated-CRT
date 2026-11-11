import MatedCRT.FirstPass.S5d.FloorProof.Geometry
import MatedCRT.FirstPass.S5d.FloorProof.MinPrinciple

/-!
# Pathwise floor on one cell

Deterministic estimates for one outcome `ω` and one mesh `ε`. With `w̃ = matedLeastSupersolution`, `g = ε⁻¹ g_{B_ρ}(0,·)`,
`w̄ = rescale (m_ε) ε η w̃`, `ḡ = rescale (m_ε) ε η g` (floor note (1)), an exclusive point `x` of a cell `H_a` has
`w̄(x) + t ḡ(x) = m_ε⁻¹ u(a)` (floor note (15), (20)). This file gives:
* the arithmetic of the three cases: the far cells (8.1, `floor_far_value`), the near cells (8.2, `floor_near_value`) and the
  pole bound on the boundary cells of `A^ε` (22, `floor_pole_value`);
* the geometry of the cells of `A^ε` (`cell_subset_ball_two`, `cell_norm_annulus`);
* the identities `stoppedOdometer = w̃ + (t/ε) gr` (`stoppedOdometer_eq_of_mem`) and `rescale` at an exclusive point
  (`rescale_exclusive_eq`).
-/

open MeasureTheory Set Metric Filter Topology

namespace MatedCRT

namespace FloorProof

/-- Floor note (21), far cells: if `|w̄ - αW| ≤ e`, `|ḡ - αG| ≤ e` and `s ≤ α(W + tG)` with `s ≥ 1/n` and
`(1+t)e ≤ 1/(4n)`, then `w̄ + tḡ ≥ 3s/4`. -/
theorem floor_far_value {s t e n α W0 G0 wb gb : ℝ} (ht : 0 < t)
    (hsn : 1 / n ≤ s) (hen : (1 + t) * e ≤ 1 / (4 * n))
    (hw : |wb - α * W0| ≤ e) (hg : |gb - α * G0| ≤ e) (hs : s ≤ α * (W0 + t * G0)) :
    3 * s / 4 ≤ wb + t * gb := by
  have hw' := abs_le.1 hw
  have hg' := abs_le.1 hg
  have h1 : t * (α * G0 - e) ≤ t * gb := mul_le_mul_of_nonneg_left (by linarith [hg'.1]) ht.le
  have e4 : 1 / (4 * n) = (1 / n) / 4 := by ring
  have h2 : (1 + t) * e ≤ s / 4 := by
    have : (1 / n) / 4 ≤ s / 4 := by linarith
    linarith
  nlinarith [h1, hw'.1, hs, h2]

/-- Floor note (21), near cells: if `|w̄ - αW| ≤ e`, `|αW| ≤ n`, `s ≤ 1`, `n ≥ 1`, `(1+t)e ≤ 1/(4n)` and
`n + 4 - te ≤ t ḡ`, then `s/2 ≤ w̄ + tḡ`. -/
theorem floor_near_value {s t e n α W0 wb g : ℝ} (hn1 : 1 ≤ n) (hs1 : s ≤ 1)
    (hen : (1 + t) * e ≤ 1 / (4 * n)) (hw : |wb - α * W0| ≤ e) (hW : |α * W0| ≤ n)
    (hg : n + 4 - t * e ≤ t * g) :
    s / 2 ≤ wb + t * g := by
  have hw' := abs_le.1 hw
  have hW' := abs_le.1 hW
  have h4 : 1 / (4 * n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hE : (1 + t) * e ≤ 1 := le_trans hen h4
  nlinarith [hw'.1, hW'.1, hg, hE, hs1]

/-- Floor note (22): if `|ḡ - αG| ≤ e`, `n + 4 ≤ αtG` then `n + 4 - te ≤ tḡ`. -/
theorem floor_pole_value {n α G0 t e g : ℝ} (ht : 0 < t) (hg : |g - α * G0| ≤ e)
    (hpole : n + 4 ≤ α * t * G0) :
    n + 4 - t * e ≤ t * g := by
  have hg' := abs_le.1 hg
  have h1 : t * (α * G0 - e) ≤ t * g := mul_le_mul_of_nonneg_left (by linarith [hg'.1]) ht.le
  nlinarith [h1, hpole]

/-- The stopped odometer at a vertex of `V^ε(cl B_ρ)`: `u^ε(a) = w̃^ε(a) + (t/ε) g_{B_ρ}(0, a)` (the definition
`stoppedOdometer`, Defs/Sandpile.lean:93, with `matedObstacle`, Defs/Sandpile.lean:~77). -/
theorem stoppedOdometer_eq_of_mem {m : ℤ → ℤ → ℕ} {ε ρ t : ℝ} {η : ℝ → ℂ} {a : ℤ}
    (ha : a ∈ cellVertices ε η (closedBall (0 : ℂ) ρ)) :
    stoppedOdometer m ε η ρ t a =
      matedLeastSupersolution m ε η ρ t a + t / ε * greenKernel m (ballInterior ε η ρ) 0 a := by
  unfold stoppedOdometer
  simp only [ha, ↓reduceIte]
  unfold matedObstacle
  ring

/-- The rescaling at an exclusive point of the cell `H_k`: `rescale m_ε ε η u x = m_ε⁻¹ u(k)` (floor note (14)-(15)). -/
theorem rescale_exclusive_eq {mε ε : ℝ} {η : ℝ → ℂ} (u : ℤ → ℝ) {k : ℤ} {x : ℂ}
    (hx : x ∈ cell ε η k) (hex : ∀ b : ℤ, x ∈ cell ε η b → b = k) :
    rescale mε ε η u x = mε⁻¹ * u k := by
  unfold rescale
  rw [vertexOf_eq_of_exclusive hx hex]

/-- A cell meeting `B_r` with diameter `< r` lies in `B_{2r}` (floor note, Step 8.2: "small cell diameter puts the entire cell
inside `B_{2r_n}`"). -/
theorem cell_subset_ball_two {ε r : ℝ} {η : ℝ → ℂ} {k : ℤ} (hb : Bornology.IsBounded (cell ε η k))
    (hdiam : diam (cell ε η k) < r) (hmeet : (cell ε η k ∩ ball (0 : ℂ) r).Nonempty) :
    cell ε η k ⊆ ball (0 : ℂ) (2 * r) := by
  obtain ⟨y, hyK, hy⟩ := hmeet
  intro x hx
  have h1 : dist x y < r := lt_of_lt_of_le (dist_lt_of_diam_lt hb hdiam hx hyK) le_rfl
  have h2 : dist y 0 < r := by
    rw [dist_zero_right]
    exact mem_ball_zero_iff.1 hy
  rw [mem_ball_zero_iff, ← dist_zero_right]
  linarith [dist_triangle x y (0 : ℂ)]

/-- A cell meeting the circle `∂B_{2r}` with diameter `< r/4` lies in the annulus `{r < |x| < 3r}` (floor note, Step 8.2, the
boundary cell "in `{x : r_n < |x| < 3 r_n}`"). -/
theorem cell_norm_annulus {ε r : ℝ} {η : ℝ → ℂ} {k : ℤ} (hb : Bornology.IsBounded (cell ε η k))
    (hdiam : diam (cell ε η k) < r / 4) (hmeet : (cell ε η k ∩ sphere (0 : ℂ) (2 * r)).Nonempty) :
    ∀ x ∈ cell ε η k, r < ‖x‖ ∧ ‖x‖ < 3 * r := by
  obtain ⟨y, hyK, hy⟩ := hmeet
  have hyn : ‖y‖ = 2 * r := by
    have := mem_sphere_zero_iff_norm.1 hy
    exact this
  intro x hx
  have h1 : dist x y < r / 4 := dist_lt_of_diam_lt hb hdiam hx hyK
  rw [dist_eq_norm] at h1
  have h2 := abs_norm_sub_norm_le x y
  have h3 := abs_le.1 (le_trans h2 h1.le)
  have h4 := abs_lt.1 (lt_of_le_of_lt h2 h1)
  constructor <;> linarith [h4.1, h4.2]

end FloorProof

end MatedCRT
