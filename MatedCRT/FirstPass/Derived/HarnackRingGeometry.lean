import MatedCRT.Defs.Map
import LatticeProb.Analysis.GridAnnulusApprox

/-!
# Grid circles around a circle of the Harnack inequality

Deterministic geometry of the union bound in Berestycki–Gwynne (2020), Lemma 3.11.  For a vertex `b` of the
mated-CRT map whose cell is small and meets `B_ρ`, with `z = η(εb)`, and a radius `s` between a small power of `ε` and
`(1 - ρ)/8`, there are a lattice point `z' = h (m + n i)` and a radius `s' = (√2)^a` with
* `∂B_s(z) ⊆ A_{s'/2, s'}(z')` (open annulus),
* the cell of `b` inside `B_{s'/4}(z')`,
* every vertex outside the killing domain `V(B_{(1+ρ)/2}) \ V(∂B_{(1+ρ)/2})` has a cell point farther than `2 s'`
  from `z'`,
* `2 s'` smaller than the distance from `z'` to the boundary of `B_{(1+ρ)/2}`.
-/

set_option autoImplicit false

namespace MatedCRT

open Set Metric

/-- The lattice point `h (m + n i)`. -/
noncomputable def latticePt (h : ℝ) (m n : ℤ) : ℂ := (h : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)

/-- The grid radius `(√2)^a`. -/
noncomputable def sqrt2Pow (a : ℤ) : ℝ := Real.sqrt 2 ^ a

/-- The embedded point of a vertex lies in its cell. -/
theorem vertexPoint_mem_cell {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * k, ⟨by rw [mul_sub, mul_one]; linarith, le_rfl⟩, rfl⟩

/-- A vertex outside `V(B_R) \ V(∂B_R)` has a cell point of norm `≥ R`. -/
theorem exists_mem_cell_le_norm_of_not_mem_interior {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) {R : ℝ} (hR : R ≠ 0)
    {k : ℤ} (hk : k ∉ interiorCellVertices ε η (ball (0 : ℂ) R)) : ∃ x ∈ cell ε η k, R ≤ ‖x‖ := by
  unfold interiorCellVertices at hk
  by_cases h1 : k ∈ cellVertices ε η (ball (0 : ℂ) R)
  · have h2 : k ∈ cellVertices ε η (frontier (ball (0 : ℂ) R)) := by
      by_contra h2
      exact hk ⟨h1, h2⟩
    obtain ⟨x, hx, hxf⟩ := h2
    rw [frontier_ball _ hR, mem_sphere_zero_iff_norm] at hxf
    exact ⟨x, hx, hxf.ge⟩
  · have hx := vertexPoint_mem_cell hε η k
    refine ⟨vertexPoint ε η k, hx, ?_⟩
    by_contra hlt
    exact h1 ⟨vertexPoint ε η k, hx, by rw [mem_ball_zero_iff]; exact not_le.1 hlt⟩

/-- A vertex whose cell is small and meets `B_ρ` is an interior vertex of `B_{ρ₀}` when `ρ + δ < ρ₀`. -/
theorem mem_interiorCellVertices_of_diam {ε : ℝ} (η : ℝ → ℂ) {ρ ρ₀ δ : ℝ} (hρρ₀ : ρ < ρ₀)
    (hδ : ρ + δ < ρ₀) (hρ0 : ρ₀ ≠ 0) {b : ℤ} (hb : (cell ε η b ∩ ball (0 : ℂ) ρ).Nonempty)
    (hdiam : ∀ x ∈ cell ε η b, ∀ x' ∈ cell ε η b, dist x x' ≤ δ) :
    b ∈ interiorCellVertices ε η (ball (0 : ℂ) ρ₀) := by
  obtain ⟨x0, hx0, hx0b⟩ := hb
  refine ⟨⟨x0, hx0, ball_subset_ball hρρ₀.le hx0b⟩, ?_⟩
  rintro ⟨x, hx, hxf⟩
  rw [frontier_ball _ hρ0, mem_sphere_zero_iff_norm] at hxf
  have h1 := norm_sub_norm_le x x0
  have h2 := hdiam x hx x0 hx0
  rw [dist_eq_norm] at h2
  have h3 : ‖x0‖ < ρ := mem_ball_zero_iff.1 hx0b
  linarith

/-- **Grid data for the circle `∂B_s(η(εb))`.** -/
theorem exists_ringData {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) {ρ δ h s : ℝ} (hρ : 0 < ρ) (hh : 0 < h) {b : ℤ}
    (hb : (cell ε η b ∩ ball (0 : ℂ) ρ).Nonempty)
    (hdiam : ∀ x ∈ cell ε η b, ∀ x' ∈ cell ε η b, dist x x' ≤ δ)
    (hs1 : 10 * h ≤ s) (hs2 : s ≤ (1 - ρ) / 8) (hδ1 : δ + h ≤ s / 4) :
    ∃ m n a : ℤ, ‖latticePt h m n‖ < ρ + δ + h ∧ s < sqrt2Pow a ∧
      2 * sqrt2Pow a < (1 + ρ) / 2 - ‖latticePt h m n‖ ∧
      (∀ x : ℂ, dist x (vertexPoint ε η b) = s →
        sqrt2Pow a / 2 < dist x (latticePt h m n) ∧ dist x (latticePt h m n) < sqrt2Pow a) ∧
      (∀ x ∈ cell ε η b, dist x (latticePt h m n) < sqrt2Pow a / 4) ∧
      (∀ k, k ∉ interiorCellVertices ε η (ball (0 : ℂ) ((1 + ρ) / 2)) →
        ∃ x ∈ cell ε η k, 2 * sqrt2Pow a < dist x (latticePt h m n)) := by
  have hz := vertexPoint_mem_cell hε η b
  set z := vertexPoint ε η b with hzdef
  obtain ⟨x0, hx0, hx0b⟩ := hb
  have hx0n : ‖x0‖ < ρ := mem_ball_zero_iff.1 hx0b
  have hzn : ‖z‖ < ρ + δ := by
    have h1 := norm_sub_norm_le z x0
    have h2 := hdiam z hz x0 hx0
    rw [dist_eq_norm] at h2
    linarith
  obtain ⟨m, n, hmn⟩ := LatticeProb.exists_lattice_point_norm_sub_le hh z
  have hzz : dist z (latticePt h m n) ≤ h := by rw [dist_eq_norm]; exact hmn
  have hz'n : ‖latticePt h m n‖ < ρ + δ + h := by
    have h1 := norm_sub_norm_le (latticePt h m n) z
    rw [← dist_eq_norm, dist_comm] at h1
    linarith
  have hqlo : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hqhi : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hxpos : 0 < s + 2 * h := by linarith
  obtain ⟨a, ha1, ha2⟩ := LatticeProb.exists_le_zpow_lt hqlo hxpos
  have hs' : sqrt2Pow a < 3 / 2 * (s + 2 * h) := by
    unfold sqrt2Pow
    calc Real.sqrt 2 ^ a < Real.sqrt 2 * (s + 2 * h) := ha2
      _ < 3 / 2 * (s + 2 * h) := mul_lt_mul_of_pos_right hqhi hxpos
  have hs'lo : s + 2 * h ≤ sqrt2Pow a := ha1
  have h3 : 2 * sqrt2Pow a < (1 + ρ) / 2 - ‖latticePt h m n‖ := by linarith
  refine ⟨m, n, a, hz'n, by linarith, h3, ?_, ?_, ?_⟩
  · intro x hx
    have d1 := dist_triangle x z (latticePt h m n)
    have d2 := dist_triangle x (latticePt h m n) z
    rw [dist_comm (latticePt h m n) z] at d2
    constructor <;> linarith
  · intro x hx
    have d1 := dist_triangle x z (latticePt h m n)
    have d2 := hdiam x hx z hz
    linarith
  · intro k hk
    obtain ⟨x, hx, hxn⟩ := exists_mem_cell_le_norm_of_not_mem_interior hε η (R := (1 + ρ) / 2)
      (by positivity) hk
    refine ⟨x, hx, ?_⟩
    have h1 := norm_sub_norm_le x (latticePt h m n)
    rw [← dist_eq_norm] at h1
    linarith

end MatedCRT
