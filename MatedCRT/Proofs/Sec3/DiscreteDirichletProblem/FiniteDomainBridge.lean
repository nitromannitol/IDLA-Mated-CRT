import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.RawRepresentationPrepared
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryStartingExit

/-! # Finite-domain reduction for the prepared Dirichlet representation -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- Finite-domain Green representation and boundary exit, for a locally finite
    graph containing the integer nearest-neighbour edges. -/
def FiniteDomainDirichletRepresentation : Prop :=
  ∀ (m : ℤ → ℤ → ℕ), IsLocallyFiniteMult m →
  (∀ k : ℤ, m k (k + 1) ≠ 0) → ∀ (A B : Set ℤ),
  ∀ (hA : A.Finite), B.Finite →
  (∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∈ A ∪ B) →
  (∀ a ∈ A, ∀ᵐ x ∂srwLaw m a, vExitTime A x ≠ ⊤) →
  ∀ (F g : ℤ → ℝ), (∀ a ∈ A, mLaplacian m F a = g a) →
  ∀ a ∈ A ∪ B,
    (∀ᵐ x ∂srwLaw m a, vExitPosition A x ∈ B) ∧
    F a = (∫ x, B.indicator F (vExitPosition A x) ∂srwLaw m a) -
      ∑ b ∈ hA.toFinset, g b * greenFn m A a b

/-- The general finite-domain representation supplies the prepared disk
    representation used in Lemma 3.5, corrected paper lines 1532–1535. -/
theorem dirichletRawRepresentationPreparedStep_of_finiteDomain
    (𝒮 : SpaceFillingSLEModel) (hfinite : FiniteDomainDirichletRepresentation) :
    DirichletRawRepresentationPreparedStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS r z hr ψ F hsource
  refine ⟨fun _ => univ, ?_, ?_⟩
  · refine ⟨1, by norm_num, 0, 1, by norm_num, ?_⟩
    intro ε hε hε1
    simp
  · intro ε hε
    filter_upwards [hsource ε hε, hS.ae_disk_dirichlet_decomposition_geometry hγ hγ2,
      hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hF hgeom hη hp hadj _
    obtain ⟨hA, hB, hnb, hsub, hexit⟩ := hgeom ε hε z r hr
    have hlf := Tightness.isLocallyFiniteMult_of_cells hη.1 hp hε (hadj ε hε)
    refine ⟨hA, fun a ha => ?_⟩
    exact hfinite (S.mult ε ω) hlf (S.mult_succ_ne_zero hε.le ω) _ _ hA hB hnb hexit
      (F ε ω) (fun b => ψ (vertexPoint ε (S.η ω) b)) hF a (hsub ha)

end MatedCRT
