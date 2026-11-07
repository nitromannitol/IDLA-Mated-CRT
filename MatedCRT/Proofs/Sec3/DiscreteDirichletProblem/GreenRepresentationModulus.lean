import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.EnvSigmaRepresentation
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GoodEventBoundedModulus

/-! # Prepared Dirichlet modulus from Green representation -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- A finite-domain Green representation with measurable source and boundary
data on polynomially likely events implies the prepared Dirichlet modulus.
The representation itself remains a separate hypothesis. -/
theorem MatedCRTEnv.IsValid.dirichlet_modulus_of_green_representation
    {𝒮 : SpaceFillingSLEModel} (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) (hψ : ∃ C : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ C)
    (hφ : ∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s)))
    (F : ℝ → Ω → ℤ → ℝ) (E : ℝ → Set Ω)
    (hF : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b))
    (hE : PolyHighProb S.P E)
    (q g : ℝ → Ω → ℤ → ℝ)
    (hq : ∀ ε, 0 < ε → ∀ b, Measurable[S.envSigma] fun ω => q ε ω b)
    (hg : ∀ ε, 0 < ε → ∀ b, Measurable[S.envSigma] fun ω => g ε ω b)
    (hrep : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε →
      ∃ h : (interiorCellVertices ε (S.η ω) (ball z r)).Finite,
        ∀ a ∈ cellVertices ε (S.η ω) (ball z r),
          F ε ω a = (∫ x, g ε ω
              (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)
            ∂srwLaw (S.mult ε ω) a) -
            ∑ b ∈ h.toFinset, q ε ω b * greenFn (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball z r)) a b)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ ball z r)
    (t : ℝ) (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e := by
  classical
  have hv : ∀ ε, 0 < ε → ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      ∀ᵐ ω ∂S.P, ω ∈ E ε → ∀ a ∈ cellVertices ε (S.η ω) (ball z r), v ω a = F ε ω a := by
    intro ε hε
    exact hS.exists_envSigma_local_solution_on_event ε (ball z r) (Or.inl isOpen_ball)
      (E ε) (q ε) (g ε) (F ε) (hq ε hε) (hg ε hε) (hrep ε hε)
  let G : ℝ → Ω → ℤ → ℝ := fun ε => if h : 0 < ε then Classical.choose (hv ε h) else 0
  have hG : ∀ ε, 0 < ε → ∀ a, Measurable[S.envSigma] fun ω => G ε ω a := by
    intro ε hε a
    simpa [G, hε] using (Classical.choose_spec (hv ε hε)).1 a
  have heq : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε →
      ∀ a ∈ cellVertices ε (S.η ω) (ball z r), F ε ω a = G ε ω a := by
    intro ε hε
    have h := (Classical.choose_spec (hv ε hε)).2
    filter_upwards [h] with ω hω hEω a ha
    simpa [G, hε] using (hω hEω a ha).symm
  exact hS.dirichlet_modulus_of_good_event_versions h31 h28 hm h218 h217 hγ hγ2 hρ hρ1
    hr hD ψ φ hψ hφ F G E hF heq hG hE K hK hKD t ht he

end MatedCRT
