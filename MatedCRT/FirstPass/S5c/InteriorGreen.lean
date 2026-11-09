import MatedCRT.FirstPass.S5c.InteriorBall
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.KernelMonotonicity
import MatedCRT.Proofs.WalkPotential.GreenFirstStep

/-!
# FIRST PASS, interior-ball Green bound (GAP 2, operator note 20:31): Step 3 of CHATGPT-q3-questions §1.4

Step 3 (eqs. (10)-(12)) of the repair of the stopped surplus lower bound (IDLA Lemma 5.4 extended to `I_ε`).
Let `z = η(a)`, `J = K_ε(B_{r/2}(z))`, `I = K_ε(B_r(z))`. The Draft lower bound `GreenKernelLowerBoundStmt`
(Draft/Section2.lean:212, BG20 Lemma 4.4) is used with radius `r/2` on the domain `J`; the monotonicity of the Green
kernel in the domain (`greenKernel_mono_of_firstStep`, first-step equations from `mLaplacian_greenFn`) then transfers the
bound `≥ 1` from `J` to `I ⊇ J`, which is the inclusion of `cellVertices_half_ball_subset_interior` (eq. (9)).
-/

namespace MatedCRT.S5c

open Metric Set

/-- **Unit capped logarithm** (§1.4 Step 3, eq. (11)). If `‖x - y‖ ≤ 4cR`, `4c ≤ e^{-2C}` and `ε ≤ e^{-2C}`, then the
capped logarithm of the Draft form of the Green lower bound (Draft/Section2.lean:212, radius `R`), minus one, is at least
one. The capped quotient is `R/‖x - y‖`, and `ε⁻¹` at zero separation. -/
theorem one_le_log_capped {C c ε R : ℝ} {x y : ℂ} (hC : 0 < C) (hε : 0 < ε) (hR : 0 < R)
    (h4c : 4 * c ≤ Real.exp (-(2 * C))) (hεC : ε ≤ Real.exp (-(2 * C))) (hxy : ‖x - y‖ ≤ 4 * c * R) :
    1 ≤ C⁻¹ * Real.log (if x = y then ε⁻¹ else min (R / ‖x - y‖) ε⁻¹) - 1 := by
  have hC0 : C ≠ 0 := hC.ne'
  have hE : 0 < Real.exp (2 * C) := Real.exp_pos _
  have hEinv : Real.exp (2 * C) * Real.exp (-(2 * C)) = 1 := by
    rw [← Real.exp_add]; simp
  have hεE : Real.exp (2 * C) * ε ≤ 1 := by
    calc Real.exp (2 * C) * ε ≤ Real.exp (2 * C) * Real.exp (-(2 * C)) :=
          mul_le_mul_of_nonneg_left hεC hE.le
      _ = 1 := hEinv
  have h4cE : 4 * c * Real.exp (2 * C) ≤ 1 := by
    calc 4 * c * Real.exp (2 * C) ≤ Real.exp (-(2 * C)) * Real.exp (2 * C) :=
          mul_le_mul_of_nonneg_right h4c hE.le
      _ = 1 := by rw [mul_comm]; exact hEinv
  have hM : Real.exp (2 * C) ≤ (if x = y then ε⁻¹ else min (R / ‖x - y‖) ε⁻¹) := by
    split_ifs with hxy'
    · rw [← one_div, le_div_iff₀ hε]; exact hεE
    · have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy')
      refine le_min ?_ ?_
      · rw [le_div_iff₀ hpos]
        have h1 := mul_le_mul_of_nonneg_left hxy hE.le
        have h2 := mul_le_mul_of_nonneg_right h4cE hR.le
        nlinarith
      · rw [← one_div, le_div_iff₀ hε]; exact hεE
  have hlog : 2 * C ≤ Real.log (if x = y then ε⁻¹ else min (R / ‖x - y‖) ε⁻¹) := by
    have h := Real.log_le_log hE hM
    rwa [Real.log_exp] at h
  have hCinv : C⁻¹ * (2 * C) = 2 := by
    rw [mul_comm 2 C, ← mul_assoc, inv_mul_cancel₀ hC0]; norm_num
  have h := mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 hC.le)
  linarith

/-- **Green kernel of the interior ball is at least one** (§1.4 Steps 2-3, eqs. (9), (11), (12)). Pathwise, on the event
where the Draft lower bound (hypothesis `hGlow`, the conjunct of `GreenKernelLowerBoundStmt` at radius `r/2`) holds, and
with the cell-geometry inputs of the event: cells meeting `B_{r/2}(z)` have diameter at most `d ≤ cr` (`hdiam`, `hd`), and
`hIfin` the finiteness of `K_ε(B_r(z))`. Conclusion: `g_I ≥ 1` at every `b` whose cell meets `B_{cr}(z)` (eq. (12)). -/
theorem one_le_greenKernel_interior {m : ℤ → ℤ → ℕ} {ε d C c r : ℝ} {η : ℝ → ℂ} {a b : ℤ}
    (hr : 0 < r) (hε : 0 < ε) (hc6 : c ≤ 1 / 6) (hd : d ≤ c * r) (hC : 0 < C)
    (h4c : 4 * c ≤ Real.exp (-(2 * C))) (hεC : ε ≤ Real.exp (-(2 * C)))
    (hlf : ∀ x, {y | m x y ≠ 0}.Finite) (hcons : ∀ x, m x (x + 1) ≠ 0)
    (hIfin : (interiorCellVertices ε η (ball (vertexPoint ε η a) r)).Finite)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η a) (r / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d)
    (hvert : ∀ k : ℤ, vertexPoint ε η k ∈ cell ε η k)
    (hGlow : ∀ b' ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 2 / 3)),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b' then ε⁻¹
          else min ((r / 2) / ‖vertexPoint ε η a - vertexPoint ε η b'‖) ε⁻¹) - 1 ≤
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) (r / 2))) a b')
    (hb : (cell ε η b ∩ ball (vertexPoint ε η a) (c * r)).Nonempty) :
    1 ≤ greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a b := by
  set z := vertexPoint ε η a with hz
  have hdlt : d < r / 2 := by
    have := mul_le_mul_of_nonneg_right hc6 hr.le
    linarith
  have hJI : interiorCellVertices ε η (ball z (r / 2)) ⊆ interiorCellVertices ε η (ball z r) :=
    fun k hk => cellVertices_half_ball_subset_interior hr hdlt hdiam hk.1
  have hJfin : (interiorCellVertices ε η (ball z (r / 2))).Finite := hIfin.subset hJI
  have hmono : greenKernel m (interiorCellVertices ε η (ball z (r / 2))) a b ≤
      greenKernel m (interiorCellVertices ε η (ball z r)) a b :=
    greenKernel_mono_of_firstStep hlf hcons hJfin hJI
      (fun x => MatedCRT.WalkPotential.mLaplacian_greenFn hlf hcons hJfin x) (fun x => MatedCRT.WalkPotential.mLaplacian_greenFn hlf hcons hIfin x) a b
  obtain ⟨y, hyc, hyb⟩ := hb
  have hyz : dist y z < c * r := mem_ball.1 hyb
  have hcr : c * r ≤ r / 2 / 3 := by
    have := mul_le_mul_of_nonneg_right hc6 hr.le
    linarith
  have hbV : b ∈ cellVertices ε η (ball z (r / 2 / 3)) :=
    ⟨y, hyc, mem_ball.2 (lt_of_lt_of_le hyz hcr)⟩
  have hG := hGlow b hbV
  have hne : (cell ε η b ∩ ball z (r / 2)).Nonempty :=
    ⟨y, hyc, mem_ball.2 (by linarith)⟩
  have hdist : dist (vertexPoint ε η b) y ≤ d := hdiam b hne _ (hvert b) y hyc
  have hxy : ‖z - vertexPoint ε η b‖ ≤ 4 * c * (r / 2) := by
    rw [← dist_eq_norm]
    have h1 := dist_triangle z y (vertexPoint ε η b)
    have h2 := dist_comm z y
    have h3 := dist_comm (vertexPoint ε η b) y
    linarith
  have hlow := one_le_log_capped hC hε (half_pos hr) h4c hεC hxy
  linarith [hG, hlow, hmono]

end MatedCRT.S5c
