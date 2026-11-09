import MatedCRT.FirstPass.S5c.GreenTarget
import MatedCRT.Proofs.Sec4.SubsequentialProperties.Subharmonic
import MatedCRT.Proofs.Infra.LocallyFinite

/-!
# FIRST PASS, GAP 2 Step (a): the upper bound (19) of `CHATGPT-q3-questions` §1.4, pathwise

Eq. (19): `G_I(a,a) ≤ G_{V^ε(B_ρ)}(a,a) ≤ ε^{-1/2}` for `I = K_ε(B_r(z))` with `B_r(z) ⊆ B_ρ` and `a ∈ I`. The first
inequality is domain monotonicity of the killed Green function on finite domains (`greenFn_mono_of_firstStep`); the second
is the crude bound of Lemma 2.15 (Draft `GreenFunctionCrudeBoundStmt`, at `ζ = 1/2`), taken as the pathwise hypothesis
`hcrude` on the event of that Lemma. Nothing here is probabilistic.

Killed Green functions of Armitage-Gardiner potential theory on the finite domains `K_ε(·) ⊆ ℤ` of the discrete lattice
(first-step equations from `mLaplacian_greenFn`).
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology

/-- Domain monotonicity of the diagonal Green function on finite domains (eq. (19), first inequality). -/
theorem greenFn_diag_le_of_finite_subset {m : ℤ → ℤ → ℕ} {A B : Set ℤ}
    (hlf : ∀ x, {y | m x y ≠ 0}.Finite) (hcons : ∀ x, m x (x + 1) ≠ 0)
    (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B) (a : ℤ) :
    greenFn m A a a ≤ greenFn m B a a :=
  greenFn_mono_of_firstStep hlf hcons hA hAB
    (fun b => WalkPotential.mLaplacian_greenFn hlf hcons hA b)
    (fun b => WalkPotential.mLaplacian_greenFn hlf hcons hB b) a a

/-- The cell vertices of a ball are finite, for a proper parametrization `η` (the cells of a compact set are finitely
many). -/
theorem cellVertices_ball_finite {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (z : ℂ) (r : ℝ) :
    (cellVertices ε η (ball z r)).Finite := by
  refine (MatedCRT.cellVertices_finite_of_isCompact hη hp hε (isCompact_closedBall z r)).subset ?_
  intro k hk
  obtain ⟨y, hy, hyb⟩ := hk
  exact ⟨y, hy, ball_subset_closedBall hyb⟩

/-- The interior cell vertices of a ball are finite (they are cell vertices of that ball). -/
theorem interiorCellVertices_finite_of_ball {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) (z : ℂ) (r : ℝ) :
    (interiorCellVertices ε η (ball z r)).Finite :=
  (cellVertices_ball_finite hη hp hε z r).subset fun _ hk => hk.1

/-- **Eq. (19) of CHATGPT-q3-questions §1.4, pathwise** (the hypothesis `hGup` of `green_ratio_target`). On the crude
bound `hcrude` (Lemma 2.15 at `ζ = 1/2`, on `V^ε(B_ρ)`), the diagonal Green function of `I = K_ε(B_r(z))` at `a ∈ I`
is at most `ε^{-1/2}`, when `B_r(z) ⊆ B_ρ`. -/
theorem greenFn_interior_diag_le_crude {ε r ρ : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {z : ℂ} {a : ℤ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hr : 0 < r) (hρ : 0 < ρ) (hball : ball z r ⊆ ball 0 ρ)
    (hlf : ∀ x, {y | m x y ≠ 0}.Finite) (hcons : ∀ x, m x (x + 1) ≠ 0)
    (hcrude : ∀ b ∈ cellVertices ε η (ball 0 ρ),
      greenFn m (interiorCellVertices ε η (ball 0 ρ)) b b ≤ ε ^ (-(1 / 2 : ℝ)))
    (ha : a ∈ interiorCellVertices ε η (ball z r)) :
    greenFn m (interiorCellVertices ε η (ball z r)) a a ≤ ε ^ (-(1 / 2 : ℝ)) := by
  have haD : a ∈ cellVertices ε η (ball 0 ρ) := by
    obtain ⟨y, hy, hyz⟩ := ha.1
    exact ⟨y, hy, hball hyz⟩
  have hmono := greenFn_diag_le_of_finite_subset hlf hcons
    (interiorCellVertices_finite_of_ball hη hp hε z r) (interiorCellVertices_finite_of_ball hη hp hε 0 ρ)
    (MatedCRT.interiorCellVertices_subset_of_ball_subset hη hr hρ hball) a
  exact hmono.trans (hcrude a haD)

/-- **Target (4) of GAP 2 with the upper bound (19) derived**: `green_ratio_target` with `hGup` replaced by the crude
bound `hcrude` on `V^ε(B_ρ)` and the ball inclusion `B_r(η(a)) ⊆ B_ρ`; the finiteness of `I` comes from properness. -/
theorem green_ratio_target_of_crude {μ : Measure ℂ} {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {ε d C c r mr ρ : ℝ} {a : ℤ}
    (hap : IsAreaParametrized μ η) (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hr : 0 < r) (hε : 0 < ε) (hρ : 0 < ρ) (hc6 : c ≤ 1 / 6) (hd : d ≤ c * r) (hC : 0 < C)
    (h4c : 4 * c ≤ Real.exp (-(2 * C))) (hεC : ε ≤ Real.exp (-(2 * C)))
    (hsymm : ∀ x y, m x y = m y x)
    (hlf : ∀ x, {y | m x y ≠ 0}.Finite) (hcons : ∀ x, m x (x + 1) ≠ 0)
    (hball : ball (vertexPoint ε η a) r ⊆ ball 0 ρ)
    (hdiam : ∀ k : ℤ, (cell ε η k ∩ ball (vertexPoint ε η a) (r / 2)).Nonempty →
      ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d)
    (hvert : ∀ k : ℤ, vertexPoint ε η k ∈ cell ε η k)
    (hGlow : ∀ b' ∈ cellVertices ε η (ball (vertexPoint ε η a) (r / 2 / 3)),
      C⁻¹ * Real.log (if vertexPoint ε η a = vertexPoint ε η b' then ε⁻¹
          else min ((r / 2) / ‖vertexPoint ε η a - vertexPoint ε η b'‖) ε⁻¹) - 1 ≤
        greenKernel m (interiorCellVertices ε η (ball (vertexPoint ε η a) (r / 2))) a b')
    (hmr : ENNReal.ofReal mr ≤ μ (ball (vertexPoint ε η a) (c * r)))
    (hmrε : ε ^ (1 / 4 : ℝ) ≤ mr)
    (hcrude : ∀ b ∈ cellVertices ε η (ball 0 ρ),
      greenFn m (interiorCellVertices ε η (ball 0 ρ)) b b ≤ ε ^ (-(1 / 2 : ℝ))) :
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
  exact green_ratio_target hap hr hε hc6 hd hC h4c hεC hsymm hlf hcons
    (interiorCellVertices_finite_of_ball hη hp hε _ r) hdiam hvert hGlow hmr hmrε
    (greenFn_interior_diag_le_crude hη hp hε hr hρ hball hlf hcons hcrude ha)

end MatedCRT.S5c
