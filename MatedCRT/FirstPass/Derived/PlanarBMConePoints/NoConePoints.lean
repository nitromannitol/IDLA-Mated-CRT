import MatedCRT.FirstPass.Derived.PlanarBMConePoints.FixedWedge
import MatedCRT.FirstPass.Derived.PlanarBMConePoints.Rotation
import MatedCRT.FirstPass.Derived.PlanarBMConePoints.WedgeCover

/-!
# Planar Brownian motion has no two-sided cone points of angle less than `π`

Let `μ` be the law of a two-sided standard planar Brownian motion `w` (`IsCorrelatedBM2 (√2) μ`).
Almost surely, for no time `t > 0` and no closed wedge `{v | 0 ≤ ⟪a, v⟫, 0 ≤ ⟪b, v⟫}` with
linearly independent inward normals `a`, `b` (a wedge of angle less than `π`) is there an `ε > 0`
with `w s - w t` in the wedge for all `s ∈ [t - ε, t + ε]` (`noTwoSidedConePoints`; Le Gall,
*Some properties of planar Brownian motion*, Lecture Notes in Math. 1527, Chapter III,
Theorem 3(i)).

Every such wedge lies, after a rotation by a rational angle `φ`, in the closed wedge of a rational
angle `θ < π` around the positive first axis (`exists_rat_rotateVec_mem_symmetricWedge`); the
rotated path is again a two-sided planar Brownian motion (`isCorrelatedBM2_map_rotatePath`); and
for one such wedge, one radius `2 / (j + 1)` and one time interval `[-K, K]` the cone points form
a null event (`measure_symmetricConePoint_eq_zero`). The countably many null events cover all cone
points.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open MatedCRTHarmonic.MatedCRT

namespace MatedCRT.PlanarBMConePoints

theorem rotatePath_sub_eq_rotateVec (φ : ℝ) (w : Path2) (u t : ℝ) :
    ((rotatePath φ w u).1 - (rotatePath φ w t).1, (rotatePath φ w u).2 - (rotatePath φ w t).2) =
      rotateVec φ ((w u).1 - (w t).1, (w u).2 - (w t).2) := by
  simp only [rotatePath, rotateVec, ContinuousMap.coe_mk, Prod.mk.injEq]
  constructor <;> ring

/-- Almost surely, for no rational rotation `φ`, rational angle `θ ∈ (0, π)`, radius `2 / (j + 1)`
and interval `[-K, K]` does the rotated path have a two-sided cone point. -/
theorem ae_forall_not_isSymmetricConePoint_rotatePath {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) :
    ∀ᵐ w ∂μ, ∀ (φ θ : ℚ) (j K : ℕ), 0 < (θ : ℝ) → (θ : ℝ) < Real.pi →
      ¬ ∃ t ∈ Icc (-(K : ℝ)) K,
        IsSymmetricConePoint θ (2 * ((j : ℝ) + 1)⁻¹) (rotatePath φ w) t := by
  rw [ae_all_iff]
  intro φ
  rw [ae_all_iff]
  intro θ
  rw [ae_all_iff]
  intro j
  rw [ae_all_iff]
  intro K
  by_cases h : 0 < (θ : ℝ) ∧ (θ : ℝ) < Real.pi
  · have hν := isCorrelatedBM2_map_rotatePath hμ (φ : ℝ)
    have h0 := measure_symmetricConePoint_eq_zero hν h.1 h.2
      (s := ((j : ℝ) + 1)⁻¹) (by positivity) K
    have h1 : μ (rotatePath φ ⁻¹' {w | ∃ t ∈ Icc (-(K : ℝ)) K,
        IsSymmetricConePoint θ (2 * ((j : ℝ) + 1)⁻¹) w t}) = 0 :=
      le_antisymm
        ((Measure.le_map_apply (continuous_rotatePath (φ : ℝ)).measurable.aemeasurable _).trans
          h0.le)
        zero_le
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with w hw _ _ hex
    exact hw hex
  · exact Eventually.of_forall fun _ h0 h1 => absurd ⟨h0, h1⟩ h

/-- **Planar Brownian motion has no two-sided cone points of angle less than `π`** (Le Gall,
*Some properties of planar Brownian motion*, Chapter III, Theorem 3(i)): almost surely, for no
time `t > 0` and no closed wedge with linearly independent inward normals `a`, `b` is there an
`ε ∈ (0, t)` with `w s - w t` in the wedge for all `s ∈ [t - ε, t + ε]`. -/
theorem noTwoSidedConePoints {μ : Measure Path2} (hμ : IsCorrelatedBM2 (Real.sqrt 2) μ) :
    ∀ᵐ w ∂μ, ∀ t : ℝ, 0 < t → ∀ a b : ℝ × ℝ, a.1 * b.2 - a.2 * b.1 ≠ 0 →
      ¬ ∃ ε : ℝ, 0 < ε ∧ ε < t ∧ ∀ s ∈ Icc (t - ε) (t + ε),
        0 ≤ a.1 * ((w s).1 - (w t).1) + a.2 * ((w s).2 - (w t).2) ∧
          0 ≤ b.1 * ((w s).1 - (w t).1) + b.2 * ((w s).2 - (w t).2) := by
  filter_upwards [ae_forall_not_isSymmetricConePoint_rotatePath hμ] with w hw
  rintro t ht a b hab ⟨ε, hε, -, hcone⟩
  obtain ⟨φ, θ, hθ0, hθπ, hcov⟩ := exists_rat_rotateVec_mem_symmetricWedge a b hab
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 2 * ((j : ℝ) + 1)⁻¹ ≤ ε := by
    obtain ⟨j, hj⟩ := exists_nat_gt (2 / ε)
    refine ⟨j, ?_⟩
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have h2 := (div_lt_iff₀ hε).1 hj
    nlinarith
  refine hw φ θ j ⌈t⌉₊ hθ0 hθπ
    ⟨t, ⟨by linarith [(Nat.cast_nonneg ⌈t⌉₊ : (0 : ℝ) ≤ ⌈t⌉₊)], Nat.le_ceil t⟩, fun u hu => ?_⟩
  have hu' : u ∈ Icc (t - ε) (t + ε) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨h1, h2⟩ := hcone u hu'
  have key := hcov ((w u).1 - (w t).1, (w u).2 - (w t).2) h1 h2
  rw [← rotatePath_sub_eq_rotateVec] at key
  exact key

end MatedCRT.PlanarBMConePoints
