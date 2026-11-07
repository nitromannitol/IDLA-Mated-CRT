import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ModulusApproximation
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExitValue

/-! # Discrete harmonicity of projected exit expectations -/

namespace MatedCRT

open MeasureTheory Set Metric _root_.HarmonicBalls

/-- Expected projected boundary value for a walk started at a vertex. -/
noncomputable def projectedExitVertexValue (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ)
    (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ) (a : ℤ) : ℝ :=
  ∫ x, ψ (ballRetraction z r (vertexPoint ε η
    (vExitPosition (interiorCellVertices ε η (ball z r)) x))) ∂srwLaw m a

/-- The projected exit expectation is discrete harmonic whenever the walk
exits the interior vertex set almost surely. -/
theorem matedLaplacian_projectedExitVertexValue (m : ℤ → ℤ → ℕ)
    (hlf : IsLocallyFiniteMult m) (ε : ℝ) (η : ℝ → ℂ) {r : ℝ} (hr : 0 < r)
    (z : ℂ) (ψ : ℂ → ℝ) {K : ℝ} (hψ : ∀ x ∈ closedBall z r, |ψ x| ≤ K)
    (hA : ∀ a ∈ interiorCellVertices ε η (ball z r),
      ∀ᵐ x ∂srwLaw m a, vExitTime (interiorCellVertices ε η (ball z r)) x ≠ ⊤)
    {a : ℤ} (ha : a ∈ interiorCellVertices ε η (ball z r)) (hdeg : mdeg m a ≠ 0) :
    matedLaplacian m (projectedExitVertexValue m ε η r z ψ) a = 0 := by
  have h := mLaplacian_integral_exitValue hlf hA ha hdeg
    (g := fun b => ψ (ballRetraction z r (vertexPoint ε η b)))
    (fun b => hψ _ (ballRetraction_mem z hr _))
  exact h

/-- At vertices outside the interior, the exit expectation is the boundary value. -/
theorem projectedExitVertexValue_of_not_mem (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ)
    (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ) {a : ℤ}
    (ha : a ∉ interiorCellVertices ε η (ball z r)) :
    projectedExitVertexValue m ε η r z ψ a =
      ψ (ballRetraction z r (vertexPoint ε η a)) := by
  unfold projectedExitVertexValue
  have heq : ∀ᵐ x ∂srwLaw m a,
      vExitPosition (interiorCellVertices ε η (ball z r)) x = a := by
    filter_upwards [srwLaw_ae_start m a] with x hx
    unfold vExitPosition
    rw [vExitTime_eq_zero_of_not_mem (by rw [hx]; exact ha)]
    simpa using hx
  calc
    _ = ∫ _x, ψ (ballRetraction z r (vertexPoint ε η a)) ∂srwLaw m a :=
      integral_congr_ae (heq.mono fun _ hx => by rw [hx])
    _ = _ := by simp

end MatedCRT
