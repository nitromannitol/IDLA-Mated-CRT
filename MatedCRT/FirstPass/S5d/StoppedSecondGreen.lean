import MatedCRT.FirstPass.S5c.GreenTarget
import MatedCRT.FirstPass.S5d.GreenEvent

/-!
# The second Green inequality of the stopped clause, pathwise

Pathwise form of the second Green inequality (5.7) of the stopped clause (Proposition 5.1 proof [C21]) on the killing domain `J` (the stopped killing set
`I^ε_t`) instead of the ball domain `B = K_ε(B_r(η(a)))` of `MatedCRT.S5c.green_ratio_target`.

Route: `B ⊆ J` and the first-step monotonicity of the Green kernel (`MatedCRT.greenKernel_mono_of_firstStep`) give
`g_B ≤ g_J` on `B`, so the kernel mass bound `m_r ε⁻¹ ≤ ∑_{b∈B} g_B(a,b)` of `MatedCRT.S5c.mass_le_green_sum` transfers to
`∑_{b∈J} g_J(a,b)`; then `MatedCRT.S5c.green_ratio_ge_quarter` (with `I := J`) gives the ratio bound. The diagonal upper
bound on `J` is a hypothesis `hGup` (the paper's Lemma 2.15 `GreenFunctionCrudeBoundStmt` with domain monotonicity; not
proved here). The inclusion `B ⊆ J` is the strict-cluster containment (5.6), a consequence of the floor input.
-/

namespace MatedCRT.S5d

open MeasureTheory Set Metric
open scoped ENNReal

/-- The Green kernel is nonnegative (`greenFn` is a `toReal` of a lower integral, `mdeg` is a natural number). -/
theorem greenKernel_nonneg_stopped (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ) : 0 ≤ greenKernel m A a b := by
  unfold greenKernel greenFn
  exact div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

/-- Domain monotonicity of the Green kernel for finite domains `B ⊆ J` (first-step equations from `mLaplacian_greenFn`). -/
theorem greenKernel_le_of_subset_stopped {m : ℤ → ℤ → ℕ} {B J : Set ℤ} (hlf : ∀ x, {y | m x y ≠ 0}.Finite)
    (hcons : ∀ x, m x (x + 1) ≠ 0) (hB : B.Finite) (hJ : J.Finite) (hBJ : B ⊆ J) (x b : ℤ) :
    greenKernel m B x b ≤ greenKernel m J x b :=
  MatedCRT.greenKernel_mono_of_firstStep hlf hcons hB hBJ
    (fun c a ha => MatedCRT.WalkPotential.mLaplacian_greenFn hlf hcons hB c a ha)
    (fun c a ha => MatedCRT.WalkPotential.mLaplacian_greenFn hlf hcons hJ c a ha) x b

/-- The kernel sum over a finite domain `B ⊆ J` is at most the kernel sum over `J`. -/
theorem kernel_sum_le_of_subset_stopped {m : ℤ → ℤ → ℕ} {B J : Set ℤ} (hlf : ∀ x, {y | m x y ≠ 0}.Finite)
    (hcons : ∀ x, m x (x + 1) ≠ 0) (hB : B.Finite) (hJ : J.Finite) (hBJ : B ⊆ J) (x : ℤ) :
    ∑' b : B, greenKernel m B x b ≤ ∑' b : J, greenKernel m J x b := by
  rw [tsum_subtype_eq_sum_finite hB (greenKernel m B x), tsum_subtype_eq_sum_finite hJ (greenKernel m J x)]
  calc ∑ b ∈ hB.toFinset, greenKernel m B x b ≤ ∑ b ∈ hB.toFinset, greenKernel m J x b :=
        Finset.sum_le_sum fun b _ => greenKernel_le_of_subset_stopped hlf hcons hB hJ hBJ x b
    _ ≤ ∑ b ∈ hJ.toFinset, greenKernel m J x b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Set.Finite.toFinset_subset_toFinset.2 hBJ
        · intro b _ _
          exact greenKernel_nonneg_stopped m J x b

/-- **The second Green inequality on the killing domain, pathwise** (referee section 5.3, equation (5.7), with the killing
domain `J = I^ε_t` in place of the ball domain). Hypotheses: the geometry and the local lower bound of
`MatedCRT.S5c.green_ratio_target` (Lemma 2.16 at radius `r/2`, the cell-diameter bound `hdiam`, the net mass bound `hmr`,
the event `hmrε : ε^{1/4} ≤ m_r`); the killing domain `J` is finite, contains the target `a` and the ball domain
`interiorCellVertices ε η (ball (η a) r)` (`hBJ`); the diagonal Green bound `hGup` on `J`. -/
theorem stoppedSecondGreen_pathwise {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε d C c r mr : ℝ} {a : ℤ}
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
    (J : Set ℤ) (hJfin : J.Finite) (haJ : a ∈ J)
    (hBJ : interiorCellVertices ε η (ball (vertexPoint ε η a) r) ⊆ J)
    (hGup : greenFn m J a a ≤ ε ^ (-(1 / 2) : ℝ)) :
    ε ^ (-(1 / 4) : ℝ) ≤ (∑' b : J, greenFn m J b a) / greenFn m J a a := by
  have hq := MatedCRT.S5c.mass_le_green_sum hap hap.2.2.1 hr hε hc6 hd hC h4c hεC hlf hcons hIfin hdiam hvert hGlow hmr
  have hqJ : mr * ε⁻¹ ≤ ∑' b : J, greenKernel m J a b :=
    hq.trans (kernel_sum_le_of_subset_stopped hlf hcons hIfin hJfin hBJ a)
  exact MatedCRT.S5c.green_ratio_ge_quarter hsymm hlf hcons hJfin haJ hε hqJ hmrε hGup

end MatedCRT.S5d
