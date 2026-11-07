import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryCutoffEvent

/-! # Bounded measurable boundary data -/

namespace MatedCRT

open Set Metric MeasureTheory _root_.HarmonicBalls

/-- Continuous data on a compact measurable set admit a bounded measurable
extension that vanishes outside the set. -/
theorem exists_bounded_measurable_cutoff_of_continuousOn
    {D : Set ℂ} {f : ℂ → ℝ} (hD : MeasurableSet D)
    (hcompact : IsCompact D) (hf : ContinuousOn f D) :
    ∃ g : ℂ → ℝ, Measurable g ∧ (∀ x ∈ D, g x = f x) ∧
      ∃ C : ℝ, ∀ x, |g x| ≤ C := by
  classical
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hf.abs
  refine ⟨D.piecewise f 0, hf.measurable_piecewise continuousOn_const hD, ?_,
    max C 0, ?_⟩
  · intro x hx
    simp [hx]
  · intro x
    by_cases hx : x ∈ D
    · simpa [hx] using (hC ⟨x, hx, rfl⟩).trans (le_max_left C 0)
    · simp [hx, le_max_right C 0]

/-- Hölder boundary data have a bounded measurable cutoff that agrees with
the data at boundary vertices with polynomially high probability. -/
theorem exists_bounded_measurable_boundary_cutoff_polyHighProb
    {𝒮 : SpaceFillingSLEModel} (h28 : CellSizeEstimateStmt 𝒮)
    {γ ρ r s : ℝ} {z : ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (hs : 0 < s) (hD : ball z r ⊆ ball 0 ρ)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (φ : ℂ → ℝ) (hφ : IsHolderContinuousOn φ (closedBall z (r + s))) :
    ∃ g : ℂ → ℝ, Measurable g ∧ (∃ C : ℝ, ∀ x, |g x| ≤ C) ∧
      PolyHighProb S.P (fun ε => {ω | ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        g (vertexPoint ε (S.η ω) b) = φ (vertexPoint ε (S.η ω) b)}) := by
  obtain ⟨L, χ, hχ, _, hh⟩ := hφ
  obtain ⟨g, hgm, hg, hbound⟩ := exists_bounded_measurable_cutoff_of_continuousOn
    isClosed_closedBall.measurableSet (isCompact_closedBall z (r + s)) (hh.continuousOn hχ)
  refine ⟨g, hgm, hbound, ?_⟩
  exact polyHighProb_mono_ae (boundary_vertexPoints_polyHighProb h28 hγ hγ2 hρ hρ1 hr hs hD S hS)
    (ae_of_all _ fun _ => True.intro) (fun _ _ _ h _ b hb => hg _ (h b hb))

end MatedCRT
