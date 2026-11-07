import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.RawRepresentationModulus
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedInteriorModuli

/-! # Prepared Dirichlet modulus from the finite-domain representation -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- The finite-domain representation needed for Lemma 3.5, Step 1,
in the corrected paper, lines 1532–1535. -/
def DirichletRawRepresentationPreparedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ∀ (ψ : ℂ → ℝ) (F : ℝ → Ω → ℤ → ℝ),
    (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      ∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) →
    ∃ E : ℝ → Set Ω, PolyHighProb S.P E ∧
      ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε →
        ∃ h : (interiorCellVertices ε (S.η ω) (ball z r)).Finite,
          ∀ a ∈ cellVertices ε (S.η ω) (ball z r),
            (∀ᵐ x ∂srwLaw (S.mult ε ω) a,
              vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x ∈
                cellVertices ε (S.η ω) (sphere z r)) ∧
            F ε ω a = (∫ x, (cellVertices ε (S.η ω) (sphere z r)).indicator (F ε ω)
                (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)
              ∂srwLaw (S.mult ε ω) a) -
              ∑ b ∈ h.toFinset, ψ (vertexPoint ε (S.η ω) b) * greenFn (S.mult ε ω)
                (interiorCellVertices ε (S.η ω) (ball z r)) a b

/-- The raw representation and explicit scaling and exit-time inputs give
the prepared discrete modulus used in the interior convergence reduction. -/
theorem dirichletDiscreteModulusPreparedStep_of_raw_representation
    (𝒮 : SpaceFillingSLEModel) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (hraw : DirichletRawRepresentationPreparedStep 𝒮) :
    DirichletDiscreteModulusPreparedStep 𝒮 := by
  intro h31 _ _ h28 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hD ψ φ hψb hψ hφ F hF
    r' hr' hlt t ht e he
  obtain ⟨s, hs, hφ⟩ := hφ
  have hsource : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      ∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a) := by
    intro ε hε
    filter_upwards [hF ε hε] with ω hdata
    exact hdata.1
  obtain ⟨E, hE, hrep⟩ := hraw γ hγ hγ2 Ω S hS r z hr ψ F hsource
  apply hS.dirichlet_modulus_of_raw_green_representation h31 h28 hm h218 h217
    hγ hγ2 hρ hρ1 hr hs hD ψ φ hψ hψb hφ F E hF hE hrep
    (closedBall z r') (isCompact_closedBall z r') ?_ t ht he
  rw [isClosed_closedBall.closure_eq]
  exact closedBall_subset_ball hlt

end MatedCRT
