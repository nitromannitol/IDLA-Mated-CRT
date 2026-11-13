import MatedCRT.FirstPass.Derived.StoppedWalkScaling
import MatedCRT.Proofs.Sec1.Scaling

/-!
# Cells, vertices and stopped walks of the cone-rescaled curve (Berestycki–Gwynne (2020), §6.4)

Let `η' s = R⁻¹ η (b s)` (`R, b > 0`; the curve of the cone-rescaled environment).  Then the
objects of the map at cell size `ε / b` for `η'` are the `R⁻¹`-dilates of the objects at cell size `ε`
for `η`:

* `vertexPoint_rescale`: `η'`-embedded vertex `k` at mesh `ε / b` is `R⁻¹` times the `η`-embedded
  vertex at mesh `ε`;
* `cellVertices_rescale`, `interiorCellVertices_rescale_ball`: the vertices whose cells meet (resp.
  are interior to) the disc `B_ρ` for `(ε / b, η')` are those whose cells meet (resp. are interior to)
  `B_{Rρ}` for `(ε, η)`;
* `stoppedInterp_rescale_ball`: the stopped interpolated walk of `(ε, η)` out of `B_{Rρ}` is the time
  dilation by `lam` of `R` times the stopped interpolated walk of `(ε / b, η')` out of `B_ρ`, with
  speeds `m = lam * m'`.
-/

set_option autoImplicit false

namespace MatedCRT
namespace ConeScaledWalkData

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MatedCRT.ExitCouplingGlue

theorem vertexPoint_rescale {ε b : ℝ} (hb : 0 < b) {R : ℂ} (η η' : ℝ → ℂ)
    (hη : ∀ s, η' s = R⁻¹ * η (b * s)) (k : ℤ) :
    vertexPoint (ε / b) η' k = R⁻¹ * vertexPoint ε η k := by
  unfold vertexPoint
  rw [hη]
  have : b * (ε / b * (k : ℝ)) = ε * k := by field_simp
  rw [this]

theorem vertexPoint_eq_mul_rescale {ε b : ℝ} (hb : 0 < b) {R : ℂ} (hR : R ≠ 0) (η η' : ℝ → ℂ)
    (hη : ∀ s, η' s = R⁻¹ * η (b * s)) (k : ℤ) :
    vertexPoint ε η k = R * vertexPoint (ε / b) η' k := by
  rw [vertexPoint_rescale hb η η' hη, mul_inv_cancel_left₀ hR]

theorem cellVertices_rescale {ε b : ℝ} (hb : 0 < b) {R : ℂ} (hR : R ≠ 0) (η η' : ℝ → ℂ)
    (hη : ∀ s, η' s = R⁻¹ * η (b * s)) (D : Set ℂ) :
    cellVertices (ε / b) η' D = cellVertices ε η ((fun x : ℂ => R * x) '' D) := by
  ext k
  simp only [cellVertices, mem_ofPred_eq, Set.Nonempty, mem_inter_iff, mem_image]
  constructor
  · rintro ⟨x, hxc, hxD⟩
    exact ⟨R * x, (Sec1.mem_cell_rescale hb hR η η' hη k x).1 hxc, x, hxD, rfl⟩
  · rintro ⟨z, hz, x, hx, rfl⟩
    exact ⟨x, (Sec1.mem_cell_rescale hb hR η η' hη k x).2 hz, hx⟩

theorem interiorCellVertices_rescale {ε b : ℝ} (hb : 0 < b) {R : ℂ} (hR : R ≠ 0) (η η' : ℝ → ℂ)
    (hη : ∀ s, η' s = R⁻¹ * η (b * s)) (D : Set ℂ) :
    interiorCellVertices (ε / b) η' D = interiorCellVertices ε η ((fun x : ℂ => R * x) '' D) := by
  unfold interiorCellVertices
  rw [cellVertices_rescale hb hR η η' hη, cellVertices_rescale hb hR η η' hη]
  have hf : (fun x : ℂ => R * x) '' frontier D = frontier ((fun x : ℂ => R * x) '' D) :=
    (Homeomorph.mulLeft₀ R hR).image_frontier D
  rw [hf]

theorem image_mul_ball_zero {R : ℝ} (hR : 0 < R) (ρ : ℝ) :
    (fun x : ℂ => (R : ℂ) * x) '' ball (0 : ℂ) ρ = ball (0 : ℂ) (R * ρ) := by
  ext z
  simp only [mem_image, mem_ball_zero_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact mul_lt_mul_of_pos_left hx hR
  · intro hz
    refine ⟨(R : ℂ)⁻¹ * z, ?_, mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 hR.ne') z⟩
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
    rw [inv_mul_lt_iff₀ hR]
    exact hz

theorem cellVertices_rescale_ball {ε b R : ℝ} (hb : 0 < b) (hR : 0 < R) (η η' : ℝ → ℂ)
    (hη : ∀ s, η' s = (R : ℂ)⁻¹ * η (b * s)) (ρ : ℝ) :
    cellVertices (ε / b) η' (ball (0 : ℂ) ρ) = cellVertices ε η (ball (0 : ℂ) (R * ρ)) := by
  rw [cellVertices_rescale hb (Complex.ofReal_ne_zero.2 hR.ne') η η' hη, image_mul_ball_zero hR]

theorem interiorCellVertices_rescale_ball {ε b R : ℝ} (hb : 0 < b) (hR : 0 < R) (η η' : ℝ → ℂ)
    (hη : ∀ s, η' s = (R : ℂ)⁻¹ * η (b * s)) (ρ : ℝ) :
    interiorCellVertices (ε / b) η' (ball (0 : ℂ) ρ) =
      interiorCellVertices ε η (ball (0 : ℂ) (R * ρ)) := by
  rw [interiorCellVertices_rescale hb (Complex.ofReal_ne_zero.2 hR.ne') η η' hη,
    image_mul_ball_zero hR]

/-- **The stopped interpolated walk of the rescaled curve.**  For `η' = R⁻¹ η(b ·)`, the walk at
mesh `ε`, speed `m = lam * m'`, stopped at its exit time from the interior vertices of `B_{Rρ}`,
is `t ↦ R * (walk at mesh ε / b, speed m', stopped at its exit time from the interior vertices of
B_ρ) (lam * t)`. -/
theorem stoppedInterp_rescale_ball {ε b R : ℝ} (hb : 0 < b) (hR : 0 < R) (η η' : ℝ → ℂ)
    (hη : ∀ s, η' s = (R : ℂ)⁻¹ * η (b * s)) (ρ : ℝ) (lam m' : ℝ≥0) (X : ℕ → ℤ) (t : ℝ≥0) :
    stoppedInterp (vertexPoint ε η) (lam * m') (interiorCellVertices ε η (ball (0 : ℂ) (R * ρ))) X t =
      (R : ℂ) * stoppedInterp (vertexPoint (ε / b) η') m'
        (interiorCellVertices (ε / b) η' (ball (0 : ℂ) ρ)) X (lam * t) := by
  rw [← interiorCellVertices_rescale_ball hb hR η η' hη]
  exact StoppedWalkScaling.stoppedInterp_scale R (vertexPoint ε η) (vertexPoint (ε / b) η')
    (fun k => vertexPoint_eq_mul_rescale hb (Complex.ofReal_ne_zero.2 hR.ne') η η' hη k) lam m' _ X t

end ConeScaledWalkData
end MatedCRT
