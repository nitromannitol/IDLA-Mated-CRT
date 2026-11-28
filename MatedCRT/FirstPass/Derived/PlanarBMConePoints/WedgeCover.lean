import Mathlib

/-!
# Rational wedges around closed wedges of angle less than `π`

A closed planar wedge `{v | 0 ≤ ⟪a, v⟫, 0 ≤ ⟪b, v⟫}` with linearly independent inward normals `a`, `b`
has opening angle strictly less than `π`. We show that, after a rotation by a *rational* angle `φ`,
it is contained in the closed symmetric wedge of half-angle `θ / 2` around the positive first axis,
for some *rational* `θ ∈ (0, π)`.

The proof is quantitative and avoids angle geometry. On the wedge, `|v₁| + |v₂|` is bounded by a
constant multiple of `⟪a + b, v⟫`, so the first coordinate of the rotation of `v` by an angle
`φ₀` pointing in the direction of `a + b` is bounded below by a positive multiple of `|v₁| + |v₂|`.
This persists for a rational angle `φ` close to `φ₀`, and a rational `θ < π` close to `π` makes
the half-angle cone wide enough.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT.PlanarBMConePoints

/-- The vector `v` rotated by the angle `φ` (clockwise). -/
def rotateVec (φ : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos φ * v.1 + Real.sin φ * v.2, -Real.sin φ * v.1 + Real.cos φ * v.2)

/-- On the closed wedge cut out by `a` and `b`, the `ℓ¹` norm of `v` is controlled by `⟪a + b, v⟫`. -/
theorem abs_det_mul_le_of_mem_wedge (a b v : ℝ × ℝ)
    (hX : 0 ≤ a.1 * v.1 + a.2 * v.2) (hY : 0 ≤ b.1 * v.1 + b.2 * v.2) :
    |a.1 * b.2 - a.2 * b.1| * (|v.1| + |v.2|) ≤
      (|a.1| + |a.2| + |b.1| + |b.2|) *
        ((a.1 * v.1 + a.2 * v.2) + (b.1 * v.1 + b.2 * v.2)) := by
  set X := a.1 * v.1 + a.2 * v.2 with hXdef
  set Y := b.1 * v.1 + b.2 * v.2 with hYdef
  have h1 : (a.1 * b.2 - a.2 * b.1) * v.1 = b.2 * X - a.2 * Y := by
    rw [hXdef, hYdef]; ring
  have h2 : (a.1 * b.2 - a.2 * b.1) * v.2 = -(b.1 * X) + a.1 * Y := by
    rw [hXdef, hYdef]; ring
  have e1 : |a.1 * b.2 - a.2 * b.1| * |v.1| ≤ |b.2| * X + |a.2| * Y := by
    rw [← abs_mul, h1]
    calc |b.2 * X - a.2 * Y| ≤ |b.2 * X| + |a.2 * Y| := abs_sub _ _
      _ = |b.2| * X + |a.2| * Y := by
        rw [abs_mul, abs_mul, abs_of_nonneg hX, abs_of_nonneg hY]
  have e2 : |a.1 * b.2 - a.2 * b.1| * |v.2| ≤ |b.1| * X + |a.1| * Y := by
    rw [← abs_mul, h2]
    calc |-(b.1 * X) + a.1 * Y| ≤ |-(b.1 * X)| + |a.1 * Y| := abs_add_le _ _
      _ = |b.1| * X + |a.1| * Y := by
        rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hX, abs_of_nonneg hY]
  nlinarith [mul_nonneg (abs_nonneg a.1) hX, mul_nonneg (abs_nonneg a.2) hX,
    mul_nonneg (abs_nonneg b.1) hY, mul_nonneg (abs_nonneg b.2) hY]

/-- Every nonzero planar vector has a polar form `ρ (cos φ₀, sin φ₀)` with `ρ > 0`. -/
theorem exists_pos_mul_cos_sin_eq (u : ℝ × ℝ) (hu : u ≠ 0) :
    ∃ ρ φ₀ : ℝ, 0 < ρ ∧ ρ * Real.cos φ₀ = u.1 ∧ ρ * Real.sin φ₀ = u.2 := by
  have hz : (⟨u.1, u.2⟩ : ℂ) ≠ 0 := by
    intro h
    apply hu
    have h1 : u.1 = 0 := congrArg Complex.re h
    have h2 : u.2 = 0 := congrArg Complex.im h
    exact Prod.ext h1 h2
  refine ⟨‖(⟨u.1, u.2⟩ : ℂ)‖, Complex.arg ⟨u.1, u.2⟩, norm_pos_iff.2 hz, ?_, ?_⟩
  · exact Complex.norm_mul_cos_arg _
  · exact Complex.norm_mul_sin_arg _

/-- Rational angles approximate any real angle in the sense of `cos` and `sin` simultaneously. -/
theorem exists_rat_abs_cos_sub_lt_abs_sin_sub_lt (φ₀ ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℚ, |Real.cos (q : ℝ) - Real.cos φ₀| < ε ∧ |Real.sin (q : ℝ) - Real.sin φ₀| < ε := by
  have h1 : IsOpen {x : ℝ | |Real.cos x - Real.cos φ₀| < ε} :=
    isOpen_lt (by fun_prop) continuous_const
  have h2 : IsOpen {x : ℝ | |Real.sin x - Real.sin φ₀| < ε} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopen : IsOpen {x : ℝ | |Real.cos x - Real.cos φ₀| < ε ∧ |Real.sin x - Real.sin φ₀| < ε} :=
    h1.inter h2
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hopen
    ⟨φ₀, by simpa using And.intro hε hε⟩
  exact ⟨q, hq⟩

/-- Rational angles `θ < π` close to `π` have `cos (θ / 2)` arbitrarily small compared with
`sin (θ / 2)`. -/
theorem exists_rat_cos_half_lt_mul_sin_half (c : ℝ) (hc : 0 < c) :
    ∃ θ : ℚ, 0 < (θ : ℝ) ∧ (θ : ℝ) < Real.pi ∧
      Real.cos ((θ : ℝ) / 2) < c * Real.sin ((θ : ℝ) / 2) := by
  have hopen : IsOpen {x : ℝ | Real.cos (x / 2) < c * Real.sin (x / 2)} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  have hπ : Real.pi ∈ {x : ℝ | Real.cos (x / 2) < c * Real.sin (x / 2)} := by
    show Real.cos (Real.pi / 2) < c * Real.sin (Real.pi / 2)
    simp [hc]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen _ hπ
  have hπpos := Real.pi_pos
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
    (show Real.pi - min r (Real.pi / 2) < Real.pi by
      have : 0 < min r (Real.pi / 2) := lt_min hr (by positivity)
      linarith)
  have hm1 : min r (Real.pi / 2) ≤ r := min_le_left _ _
  have hm2 : min r (Real.pi / 2) ≤ Real.pi / 2 := min_le_right _ _
  refine ⟨q, by linarith, hq2, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Every closed wedge `{v | 0 ≤ ⟪a, v⟫, 0 ≤ ⟪b, v⟫}` with linearly independent inward normals `a`, `b`
lies, after a rotation by a rational angle, in the closed wedge of half-angle `θ / 2` around the positive
first axis, for a rational `θ ∈ (0, π)`. -/
theorem exists_rat_rotateVec_mem_symmetricWedge (a b : ℝ × ℝ) (hab : a.1 * b.2 - a.2 * b.1 ≠ 0) :
    ∃ φ θ : ℚ, 0 < (θ : ℝ) ∧ (θ : ℝ) < Real.pi ∧
      ∀ v : ℝ × ℝ, 0 ≤ a.1 * v.1 + a.2 * v.2 → 0 ≤ b.1 * v.1 + b.2 * v.2 →
        |Real.cos ((θ : ℝ) / 2) * (rotateVec φ v).2| ≤
          Real.sin ((θ : ℝ) / 2) * (rotateVec φ v).1 := by
  set N : ℝ := |a.1| + |a.2| + |b.1| + |b.2| with hN
  have hdet : 0 < |a.1 * b.2 - a.2 * b.1| := abs_pos.2 hab
  have hNpos : 0 < N := by
    by_contra hle
    have hN0 : N = 0 := le_antisymm (not_lt.1 hle) (by positivity)
    have h1 : |a.1| = 0 := by
      have := abs_nonneg a.1; have := abs_nonneg a.2; have := abs_nonneg b.1; have := abs_nonneg b.2
      linarith
    have h2 : |a.2| = 0 := by
      have := abs_nonneg a.1; have := abs_nonneg a.2; have := abs_nonneg b.1; have := abs_nonneg b.2
      linarith
    have h3 : |b.1| = 0 := by
      have := abs_nonneg a.1; have := abs_nonneg a.2; have := abs_nonneg b.1; have := abs_nonneg b.2
      linarith
    rw [abs_eq_zero] at h1 h2 h3
    apply hab
    rw [h1, h2, h3]; ring
  have hu : (a.1 + b.1, a.2 + b.2) ≠ 0 := by
    intro h
    apply hab
    have h1 : a.1 + b.1 = 0 := congrArg Prod.fst h
    have h2 : a.2 + b.2 = 0 := congrArg Prod.snd h
    have e1 : b.1 = -a.1 := by linarith
    have e2 : b.2 = -a.2 := by linarith
    rw [e1, e2]; ring
  obtain ⟨ρ, φ₀, hρ, hcos, hsin⟩ := exists_pos_mul_cos_sin_eq _ hu
  set c : ℝ := |a.1 * b.2 - a.2 * b.1| / (2 * N * ρ) with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨φ, hφc, hφs⟩ := exists_rat_abs_cos_sub_lt_abs_sin_sub_lt φ₀ c hcpos
  obtain ⟨θ, hθ0, hθπ, hθ⟩ := exists_rat_cos_half_lt_mul_sin_half c hcpos
  refine ⟨φ, θ, hθ0, hθπ, fun v hX hY => ?_⟩
  have hS : 0 ≤ |v.1| + |v.2| := by positivity
  have hbound := abs_det_mul_le_of_mem_wedge a b v hX hY
  -- first coordinate of the rotation by `φ₀`
  have hR0 : ρ * (Real.cos φ₀ * v.1 + Real.sin φ₀ * v.2) =
      (a.1 * v.1 + a.2 * v.2) + (b.1 * v.1 + b.2 * v.2) := by
    linear_combination v.1 * hcos + v.2 * hsin
  have hR0lower : 2 * c * (|v.1| + |v.2|) ≤ Real.cos φ₀ * v.1 + Real.sin φ₀ * v.2 := by
    have hρN : 0 < N * ρ := by positivity
    have : 2 * c * (|v.1| + |v.2|) * (N * ρ) ≤
        (Real.cos φ₀ * v.1 + Real.sin φ₀ * v.2) * (N * ρ) := by
      calc 2 * c * (|v.1| + |v.2|) * (N * ρ)
          = |a.1 * b.2 - a.2 * b.1| * (|v.1| + |v.2|) := by
            rw [hc]; field_simp
        _ ≤ N * ((a.1 * v.1 + a.2 * v.2) + (b.1 * v.1 + b.2 * v.2)) := hbound
        _ = (Real.cos φ₀ * v.1 + Real.sin φ₀ * v.2) * (N * ρ) := by
            rw [← hR0]; ring
    exact le_of_mul_le_mul_right this hρN
  -- first coordinate of the rotation by `φ`
  have hdiff : -(c * (|v.1| + |v.2|)) ≤
      (Real.cos φ - Real.cos φ₀) * v.1 + (Real.sin φ - Real.sin φ₀) * v.2 := by
    have e1 : |(Real.cos φ - Real.cos φ₀) * v.1| ≤ c * |v.1| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hφc.le (abs_nonneg _)
    have e2 : |(Real.sin φ - Real.sin φ₀) * v.2| ≤ c * |v.2| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hφs.le (abs_nonneg _)
    have := neg_abs_le ((Real.cos φ - Real.cos φ₀) * v.1)
    have := neg_abs_le ((Real.sin φ - Real.sin φ₀) * v.2)
    nlinarith
  have hR1 : c * (|v.1| + |v.2|) ≤ (rotateVec φ v).1 := by
    show _ ≤ Real.cos φ * v.1 + Real.sin φ * v.2
    nlinarith
  have hR2 : |(rotateVec φ v).2| ≤ |v.1| + |v.2| := by
    show |-Real.sin φ * v.1 + Real.cos φ * v.2| ≤ _
    calc |-Real.sin φ * v.1 + Real.cos φ * v.2|
        ≤ |-Real.sin φ * v.1| + |Real.cos φ * v.2| := abs_add_le _ _
      _ = |Real.sin φ| * |v.1| + |Real.cos φ| * |v.2| := by
        rw [abs_mul, abs_mul, abs_neg]
      _ ≤ 1 * |v.1| + 1 * |v.2| := by
        gcongr
        · exact Real.abs_sin_le_one _
        · exact Real.abs_cos_le_one _
      _ = |v.1| + |v.2| := by ring
  -- the half-angle bounds
  have hhalf0 : 0 < (θ : ℝ) / 2 := by linarith
  have hhalfπ : (θ : ℝ) / 2 < Real.pi := by linarith [Real.pi_pos]
  have hsinpos : 0 ≤ Real.sin ((θ : ℝ) / 2) := (Real.sin_pos_of_pos_of_lt_pi hhalf0 hhalfπ).le
  have hcosnn : 0 ≤ Real.cos ((θ : ℝ) / 2) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · linarith [Real.pi_pos]
    · linarith
  rw [abs_mul, abs_of_nonneg hcosnn]
  calc Real.cos ((θ : ℝ) / 2) * |(rotateVec φ v).2|
      ≤ Real.cos ((θ : ℝ) / 2) * (|v.1| + |v.2|) :=
        mul_le_mul_of_nonneg_left hR2 hcosnn
    _ ≤ (c * Real.sin ((θ : ℝ) / 2)) * (|v.1| + |v.2|) :=
        mul_le_mul_of_nonneg_right hθ.le hS
    _ = Real.sin ((θ : ℝ) / 2) * (c * (|v.1| + |v.2|)) := by ring
    _ ≤ Real.sin ((θ : ℝ) / 2) * (rotateVec φ v).1 :=
        mul_le_mul_of_nonneg_left hR1 hsinpos

end MatedCRT.PlanarBMConePoints

end
