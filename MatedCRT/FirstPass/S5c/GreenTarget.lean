import MatedCRT.FirstPass.S5c.GreenCount
import MatedCRT.FirstPass.S5c.GreenRatio
import MatedCRT.FirstPass.S5c.MassPositive

/-!
# FIRST PASS, target (4) of GAP 2, pathwise

For a vertex `a` with `z = η(a)`, `I = K_ε(B_r(z))`, `|z| ≤ ρ`, and the event of Step 6 (`ε^{1/4} ≤ m_r`), the ratio
`∑_{b∈I} G_I(b,a) / G_I(a,a)` is at least `ε^{-1/4}` (eq. (4)). The pathwise chain is: the net lower bound
`m_r ≤ μ_h(B_{cr}(z))` (eqs. (13)-(15), `mass_ball_ge_of_net`, `exists_pos_ofReal_le_of_finite`), the mass count
(eqs. (16)-(17), `mass_le_green_sum`), and the reversibility ratio (eqs. (18)-(20), `green_ratio_ge_quarter`).

Inputs as hypotheses: the area parametrization `hap` (its surjectivity is used); symmetry and local finiteness of the
multiplicity `m` (`hsymm`, `hlf`, `hcons`); the finiteness of `I`; the cell-diameter bound `hdiam` with `d ≤ cr`; the
pathwise Draft lower bound `hGlow` (GreenKernelLowerBoundStmt at radius `r/2`); the upper bound (19) `hGup`; and the event
`hmrε : ε^{1/4} ≤ m_r`, whose probability tends to one (its source is not part of this file).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Net lower bound of the mass** (§1.4 Step 4, eqs. (13)-(15)): for a compact set `s` covered by a finite net of
balls of radius `cr/2` centred in `t`, with `μ_h(B_{cr/2}(x)) > 0` for the net points, there is `m_r > 0` with
`m_r ≤ μ_h(B_{cr}(z))` for all `z ∈ s`. -/
theorem mass_net_lower_bound {μ : Measure ℂ} {η : ℝ → ℂ} (hap : IsAreaParametrized μ η) {s : Set ℂ}
    (hs : IsCompact s) {R : ℝ} (hR : 0 < R) :
    ∃ mr : ℝ, 0 < mr ∧ ∀ z ∈ s, ENNReal.ofReal mr ≤ μ (ball z R) := by
  obtain ⟨t, htf, hcov⟩ := exists_net_of_compact hs (half_pos hR)
  obtain ⟨mr, hmr0, hnet⟩ := exists_pos_ofReal_le_of_finite htf
    (fun x _ => mass_ball_pos hap x (half_pos hR))
  exact ⟨mr, hmr0, fun z hz => mass_ball_ge_of_net (hcov z hz) hnet⟩

/-- **Target (4) of GAP 2, pathwise** (§1.4 Steps 1-6, eq. (4)). -/
theorem green_ratio_target {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε d C c r mr : ℝ} {a : ℤ}
    (hap : IsAreaParametrized μ η)
    (hr : 0 < r) (hε : 0 < ε) (hc6 : c ≤ 1 / 6) (hd : d ≤ c * r) (hC : 0 < C)
    (h4c : 4 * c ≤ Real.exp (-(2 * C))) (hεC : ε ≤ Real.exp (-(2 * C)))
    (hsymm : ∀ x y, m x y = m y x)
    (hlf : ∀ x, {y | m x y ≠ 0}.Finite) (hcons : ∀ x, m x (x + 1) ≠ 0)
    (hIfin : (interiorCellVertices ε η (ball (vertexPoint ε η a) r)).Finite)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η a) (r / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d)
    (hvert : ∀ k : ℤ, vertexPoint ε η k ∈ cell ε η k)
    (hGlow : ∀ b' ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 2 / 3)),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b' then ε⁻¹
          else min ((r / 2) / ‖vertexPoint ε η a - vertexPoint ε η b'‖) ε⁻¹) - 1 ≤
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) (r / 2))) a b')
    (hmr : ENNReal.ofReal mr ≤ μ (ball (vertexPoint ε η a) (c * r)))
    (hmrε : ε ^ (1 / 4 : ℝ) ≤ mr)
    (hGup : greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a a ≤ ε ^ (-(1 / 2) : ℝ)) :
    ε ^ (-(1 / 4) : ℝ) ≤
      (∑' b : interiorCellVertices ε η (ball (vertexPoint ε η a) r),
          greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) b a) /
        greenFn m (interiorCellVertices ε η (ball (vertexPoint ε η a) r)) a a := by
  have hdlt : d < r / 2 := by
    have := mul_le_mul_of_nonneg_right hc6 hr.le
    linarith
  have ha : a ∈ interiorCellVertices ε η (ball (vertexPoint ε η a) r) :=
    cellVertices_half_ball_subset_interior hr hdlt hdiam
      ⟨vertexPoint ε η a, hvert a, mem_ball_self (half_pos hr)⟩
  have hq := mass_le_green_sum hap hap.2.2.1 hr hε hc6 hd hC h4c hεC hlf hcons hIfin hdiam hvert hGlow hmr
  exact green_ratio_ge_quarter hsymm hlf hcons hIfin ha hε hq hmrε hGup

end MatedCRT.S5c
