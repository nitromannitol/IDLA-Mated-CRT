import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryDecayProbability
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryPairMeasurable

/-! Probability boundary moduli from ordinary exit-time boundary decay. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- Along dyadically dominated scales, harmonic comparison and ordinary
exit-time boundary decay give the full mesh probability modulus. -/
theorem mesh_boundary_modulus_of_exitTime_boundary_decay_measurable
    {𝒮 : SpaceFillingSLEModel} (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hm : MepsScalingInput 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (hsimply : SimplyConnectedSpace (ball z r))
    (φ : ℂ → ℝ) (hφ : IsHolderContinuousOn φ (closedBall z r))
    (u h : ℝ → Ω → ℤ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hdata : ∀ e : ℕ → ℝ, (∀ n, 0 < e n ∧ e n < (1 / 2) ^ n) →
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
          |matedLaplacian (S.mult (e n) ω) (u (e n) ω) a| ≤ C) ∧
        (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
          matedLaplacian (S.mult (e n) ω) (h (e n) ω) a = 0) ∧
        (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), u (e n) ω b = h (e n) ω b) ∧
        (∀ b ∈ cellVertices (e n) (S.η ω) (frontier (ball z r)),
          h (e n) ω b = S.mε (e n) * φ (ballRetraction z r (vertexPoint (e n) (S.η ω) b))))
    (hq : ∀ e : ℕ → ℝ, (∀ n, 0 < e n ∧ e n < (1 / 2) ^ n) →
      ∀ᵐ ω ∂S.P, ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
        ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, ‖x - y‖ ≤ δ →
          (S.mε (e n))⁻¹ * (expectedExitTime (S.mult (e n) ω)
            (interiorCellVertices (e n) (S.η ω) (ball z r))
            (vertexOf (e n) (S.η ω) x)).toReal ≤ k)
    (t : ℝ) (ht : 0 < t)
    (hu : ∀ ε, 0 < ε → ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧ ∀ᵐ ω ∂S.P, v ω = u ε ω)
    {a : ℝ≥0∞} (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P {ω | ∃ x ∈ closedBall z r, ∃ y ∈ sphere z r, dist x y < δ ∧
        t < |rescale (S.mε ε) ε (S.η ω) (u ε ω) x -
          rescale (S.mε ε) ε (S.η ω) (u ε ω) y|} ≤ a := by
  apply mesh_boundary_modulus_of_exitTime_boundary_decay hH hm h218 h217
    hγ hγ2 hρ hρ1 S hS hr hD hsimply φ hφ u h hC hdata hq t ht ?_ ha
  intro δ ε hε
  obtain ⟨v, hvm, hv⟩ := hu ε hε
  exact hS.nullMeasurableSet_rescale_boundary_pair ε hε (u ε) v hvm hv
    (closedBall z r) (sphere z r) (isCompact_closedBall z r) (isCompact_sphere z r)
    sphere_subset_closedBall δ t

end MatedCRT

#print axioms MatedCRT.mesh_boundary_modulus_of_exitTime_boundary_decay_measurable
