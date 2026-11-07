import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedRepresentationVersion
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedGoodEventBoundary

/-! Boundary modulus from finite-domain representation and exit-time decay. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- The projected boundary-pair modulus follows from finite-domain Green
representation and ordinary exit-time boundary decay. -/
theorem projected_boundary_modulus_of_finiteDomain_and_exitTime_decay
    {𝒮 : SpaceFillingSLEModel} (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hm : MepsScalingInput 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (hfinite : FiniteDomainDirichletRepresentation)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (hsimply : SimplyConnectedSpace (ball z r))
    (ψ φ : ℂ → ℝ) (u : ℝ → Ω → ℤ → ℝ)
    (hdata : (∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M) ∧
      IsHolderContinuousOn ψ (ball z r) ∧ IsHolderContinuousOn φ (closedBall z r) ∧
      (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
        (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
          matedLaplacian (S.mult ε ω) (u ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
        ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
          u ε ω b = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b))))
    (hq : ∀ e : ℕ → ℝ, (∀ n, 0 < e n ∧ e n < (1 / 2) ^ n) →
      ∀ᵐ ω ∂S.P, ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
        ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, ‖x - y‖ ≤ δ →
          (S.mε (e n))⁻¹ * (expectedExitTime (S.mult (e n) ω)
            (interiorCellVertices (e n) (S.η ω) (ball z r))
            (vertexOf (e n) (S.η ω) x)).toReal ≤ k)
    (t : ℝ) (ht : 0 < t) {a : ℝ≥0∞} (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P {ω | ∃ x ∈ closedBall z r, ∃ y ∈ sphere z r, dist x y < δ ∧
        t < |rescale (S.mε ε) ε (S.η ω) (u ε ω) x -
          rescale (S.mε ε) ε (S.η ω) (u ε ω) y|} ≤ a := by
  apply projected_boundary_modulus_of_interior_good_event_versions hH hm h218 h217
    hγ hγ2 hρ hρ1 S hS hr hD hsimply ψ φ u hdata (fun _ => univ) ?_ ?_ ?_ hq t ht ha
  · intro ε hε
    exact MeasurableSet.nullMeasurableSet MeasurableSet.univ
  · simp
  · intro ε hε
    obtain ⟨v, hvm, hv⟩ := hS.exists_envSigma_projected_solution_of_finiteDomain
      hγ hγ2 hfinite ε hε hr ψ φ hdata.2.1 hdata.2.2.1 (u ε) (hdata.2.2.2 ε hε)
    exact ⟨v, hvm, hv.mono fun _ h _ => h⟩

end MatedCRT

#print axioms MatedCRT.projected_boundary_modulus_of_finiteDomain_and_exitTime_decay
