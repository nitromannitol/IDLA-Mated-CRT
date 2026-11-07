import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.DirichletCutoffData
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.RepresentationCutoff
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GreenRepresentationModulus

/-! # Dirichlet modulus from the finite-domain representation -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology _root_.HarmonicBalls
open scoped ENNReal

/-- The finite-domain representation with the solution's boundary indicator
implies the prepared modulus without assuming that the solution or the
original planar data are globally measurable. -/
theorem MatedCRTEnv.IsValid.dirichlet_modulus_of_raw_green_representation
    {𝒮 : SpaceFillingSLEModel} (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hD : ball z r ⊆ ball 0 ρ)
    (ψ φ : ℂ → ℝ) (hψ : IsHolderContinuousOn ψ (ball z r))
    (hψb : ∃ C : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ C)
    (hφ : IsHolderContinuousOn φ (closedBall z (r + s)))
    (F : ℝ → Ω → ℤ → ℝ) (E : ℝ → Set Ω)
    (hF : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b))
    (hE : PolyHighProb S.P E)
    (hrep : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε →
      ∃ h : (interiorCellVertices ε (S.η ω) (ball z r)).Finite,
        ∀ a ∈ cellVertices ε (S.η ω) (ball z r),
          (∀ᵐ x ∂srwLaw (S.mult ε ω) a,
            vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x ∈
              cellVertices ε (S.η ω) (sphere z r)) ∧
          F ε ω a = (∫ x, (cellVertices ε (S.η ω) (sphere z r)).indicator (F ε ω)
              (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x)
            ∂srwLaw (S.mult ε ω) a) -
            ∑ b ∈ h.toFinset, ψ (vertexPoint ε (S.η ω) b) * greenFn (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) (ball z r)) a b)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ ball z r)
    (t : ℝ) (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e := by
  obtain ⟨q, g, hqm, hgm, _, hq, hg⟩ :=
    hS.exists_measurable_dirichlet_cutoff_data h28 hγ hγ2 hρ hρ1 hr hs hD S ψ φ hψ hφ
  let G : ℝ → Set Ω := fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
    g ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b)}
  have hgood : PolyHighProb S.P (fun ε => E ε ∩ G ε) :=
    polyHighProb_of_inter hE hg (fun _ => Subset.rfl)
  apply hS.dirichlet_modulus_of_green_representation h31 h28 hm h218 h217 hγ hγ2 hρ hρ1
    hr hD ψ φ hψb ⟨s, hs, hφ⟩ F (fun ε => E ε ∩ G ε) hF hgood q g
    (fun ε _ b => hqm ε b) (fun ε _ b => hgm ε b) ?_ K hK hKD t ht he
  intro ε hε
  filter_upwards [hF ε hε, hq ε hε, hrep ε hε] with ω hdata hsource hraw hgoodω
  obtain ⟨hfin, hraw⟩ := hraw hgoodω.1
  refine ⟨hfin, ?_⟩
  intro a ha
  obtain ⟨hexit, hrepr⟩ := hraw a ha
  apply green_representation_of_boundary_and_source_cutoffs hfin (F ε ω)
    (fun b => ψ (vertexPoint ε (S.η ω) b)) (q ε ω) (g ε ω) ?_ ?_ hexit hrepr
  · exact fun b hb => (hsource b hb).symm
  · intro b hb
    exact (hdata.2 b hb).trans (hgoodω.2 b hb).symm

end MatedCRT
