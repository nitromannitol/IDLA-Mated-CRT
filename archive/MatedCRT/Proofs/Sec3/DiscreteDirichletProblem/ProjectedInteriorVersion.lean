import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedLocalVersion
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedBoundaryDecayLocal

/-! Boundary-pair moduli from measurable interior versions. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- Projected boundary data remove the need to assume a measurable version
on boundary cells when deriving the boundary-pair probability modulus. -/
theorem projected_boundary_modulus_of_interior_version
    {𝒮 : SpaceFillingSLEModel} (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hm : MepsScalingInput 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
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
    (hu : ∀ ε, 0 < ε → ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices ε (S.η ω) (ball z r), v ω a = u ε ω a)
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
  apply projected_boundary_modulus_of_exitTime_boundary_decay_local hH hm h218 h217
    hγ hγ2 hρ hρ1 S hS hr hD hsimply ψ φ u hdata ?_ hq t ht ha
  intro ε hε
  obtain ⟨v, hvm, hv⟩ := hu ε hε
  apply hS.exists_envSigma_projected_closedDisk_version ε hr φ hdata.2.2.1 (u ε) v hvm hv
  filter_upwards [hdata.2.2.2 ε hε] with ω hω
  exact hω.2

end MatedCRT

#print axioms MatedCRT.projected_boundary_modulus_of_interior_version
