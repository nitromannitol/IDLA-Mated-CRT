import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellRadiusEvent
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.MeasurableRepresentation

/-! # Boundary cutoff on small-cell events -/

namespace MatedCRT

open Set Metric MeasureTheory _root_.HarmonicBalls

/-- With polynomially high probability, every marked point of a boundary
cell lies in an arbitrarily fixed neighbourhood of the closed disk. -/
theorem boundary_vertexPoints_polyHighProb
    {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮)
    {γ ρ r s : ℝ} {z : ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (hs : 0 < s) (hD : ball z r ⊆ ball 0 ρ)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) :
    PolyHighProb S.P (fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
      vertexPoint ε (S.η ω) b ∈ closedBall z (r + s)}) := by
  obtain ⟨a, ha, _, hrad⟩ := exists_vanishing_closedBall_cellRadius 𝒮 h28
    hγ hγ2 hρ hρ1 hr hD S hS
  obtain ⟨ε₀, hε₀, hsmall⟩ := exists_pos_rpow_lt ha hs
  apply polyHighProb_of_inter_subset hrad (G := Set.univ) (by simp) hε₀
  intro ε hε hεlt ω hω b hb
  obtain ⟨p, hpc, hps⟩ := hb
  have hb' : b ∈ cellVertices ε (S.η ω) (closedBall z r) :=
    ⟨p, hpc, sphere_subset_closedBall hps⟩
  have hd := hω.1 b hb' p hpc
  have hp := mem_sphere.mp hps
  rw [mem_closedBall]
  linarith [dist_triangle (vertexPoint ε (S.η ω) b) p z, hsmall ε hε hεlt]

/-- A measurable cutoff of Hölder boundary data agrees with the prescribed
data at every boundary vertex with polynomially high probability. -/
theorem exists_measurable_boundary_cutoff_polyHighProb
    {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮)
    {γ ρ r s : ℝ} {z : ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (hs : 0 < s) (hD : ball z r ⊆ ball 0 ρ)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (φ : ℂ → ℝ) (hφ : IsHolderContinuousOn φ (closedBall z (r + s))) :
    ∃ g : ℂ → ℝ, Measurable g ∧ PolyHighProb S.P
      (fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        g (vertexPoint ε (S.η ω) b) = φ (vertexPoint ε (S.η ω) b)}) := by
  obtain ⟨g, hgm, hg⟩ := exists_measurable_cutoff_of_holderOn isClosed_closedBall.measurableSet hφ
  refine ⟨g, hgm, ?_⟩
  exact polyHighProb_mono_ae (boundary_vertexPoints_polyHighProb h28 hγ hγ2 hρ hρ1 hr hs hD S hS)
    (ae_of_all _ fun _ => True.intro) (fun _ _ _ h _ b hb => hg _ (h b hb))

end MatedCRT
