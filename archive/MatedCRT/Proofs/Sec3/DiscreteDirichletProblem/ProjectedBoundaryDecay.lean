import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.HarmonicComparisonExistence
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryPairMeasurable
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryModulusProbability

/-! Probability boundary moduli for projected Dirichlet data. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls
open scoped ENNReal

/-- Projected Dirichlet data with measurable vertex versions have a
boundary-pair probability modulus whenever the ordinary exit-time barrier
decays at the boundary along dyadically dominated scales. -/
theorem projected_boundary_modulus_of_exitTime_boundary_decay
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
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧ ∀ᵐ ω ∂S.P, v ω = u ε ω)
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
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨C, hC⟩ := hdata.1
  apply mesh_boundary_pair_modulus_of_ae_dyadic_modulus S.P (closedBall z r) (sphere z r)
    (fun ε ω => rescale (S.mε ε) ε (S.η ω) (u ε ω)) t ?_ ?_ ha
  · intro δ ε hε
    obtain ⟨v, hvm, hv⟩ := hu ε hε
    exact hS.nullMeasurableSet_rescale_boundary_pair ε hε (u ε) v hvm hv
      (closedBall z r) (sphere z r) (isCompact_closedBall z r) (isCompact_sphere z r)
      sphere_subset_closedBall δ t
  · intro e he
    have he' := isPolySummableScales_of_lt_half_pow he
    filter_upwards [ae_projected_boundary_pair_modulus_of_exitTime_boundary_decay hH hm h218 h217
      hγ hγ2 hρ hρ1 S hS hr hD hsimply e he' he'.tendsto_zero ψ φ hdata.2.2.1
      (le_max_right C 0) (fun x hx => (hC x hx).trans (le_max_left C 0)) u hdata.2.2.2 (hq e he)]
      with ω hω
    obtain ⟨δ, hδ, hmod⟩ := hω t ht
    refine ⟨δ, hδ, ?_⟩
    filter_upwards [hmod] with n hn
    intro x hx y hy hxy
    exact hn x hx y hy (by simpa [dist_eq_norm] using hxy)

end MatedCRT

#print axioms MatedCRT.projected_boundary_modulus_of_exitTime_boundary_decay
