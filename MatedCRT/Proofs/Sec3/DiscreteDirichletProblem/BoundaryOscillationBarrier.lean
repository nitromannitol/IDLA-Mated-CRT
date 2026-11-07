import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedHarmonicComparison

/-! Boundary oscillation controlled by the ordinary exit-time barrier. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls

/-- For a point in the disk and a point on its boundary, the oscillation of a
bounded-source solution is bounded by that of its harmonic comparison plus
one ordinary expected-exit-time term. -/
theorem abs_rescale_boundary_pair_le_harmonic_add_expectedExitTime
    {m : ℤ → ℤ → ℕ} {ε r M : ℝ} {η : ℝ → ℂ} {z x y : ℂ}
    (hε : 0 < ε) (hr : 0 < r) (hM : 0 ≤ M⁻¹) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsucc : ∀ k, m k (k + 1) ≠ 0)
    (u h : ℤ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hlap : ∀ a ∈ interiorCellVertices ε η (ball z r), |matedLaplacian m u a| ≤ C)
    (hharm : ∀ a ∈ interiorCellVertices ε η (ball z r), matedLaplacian m h a = 0)
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r), u b = h b)
    (hQfin : ∀ a ∈ interiorCellVertices ε η (ball z r),
      expectedExitTime m (interiorCellVertices ε η (ball z r)) a ≠ ⊤)
    (hx : x ∈ closedBall z r) (hy : y ∈ sphere z r)
    (hxcell : x ∈ cell ε η (vertexOf ε η x))
    (hycell : y ∈ cell ε η (vertexOf ε η y)) :
    |rescale M ε η u x - rescale M ε η u y| ≤
      |rescale M ε η h x - rescale M ε η h y| +
        C * (M⁻¹ * (expectedExitTime m (interiorCellVertices ε η (ball z r))
          (vertexOf ε η x)).toReal) := by
  have hcomparison := abs_rescale_sub_harmonic_le_expectedExitTime hε hr hM hη hp hadj hsucc
    u h hC hlap hharm hbd hQfin hx hxcell
  have hboundary : rescale M ε η u y = rescale M ε η h y := by
    simp only [rescale]
    rw [hbd (vertexOf ε η y) ⟨y, hycell, hy⟩]
  rw [hboundary]
  have htriangle := abs_sub_le (rescale M ε η u x) (rescale M ε η h x)
    (rescale M ε η h y)
  linarith

/-- The boundary-pair estimate holds eventually on a common event along every
polynomially summable deterministic mesh sequence, uniformly over the data. -/
theorem ae_eventual_boundary_pair_harmonic_comparison_uniform
    {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (e : ℕ → ℝ) (he : IsPolySummableScales e) (he0 : Tendsto e atTop (𝓝 0)) :
    ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ∀ (u h : ℤ → ℝ) (C : ℝ), 0 ≤ C →
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (e n) ω) u a| ≤ C) →
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        matedLaplacian (S.mult (e n) ω) h a = 0) →
      (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), u b = h b) →
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r,
        |rescale (S.mε (e n)) (e n) (S.η ω) u x -
          rescale (S.mε (e n)) (e n) (S.η ω) u y| ≤
        |rescale (S.mε (e n)) (e n) (S.η ω) h x -
          rescale (S.mε (e n)) (e n) (S.η ω) h y| +
        C * ((S.mε (e n))⁻¹ * (expectedExitTime (S.mult (e n) ω)
          (interiorCellVertices (e n) (S.η ω) (ball z r))
          (vertexOf (e n) (S.η ω) x)).toReal) := by
  filter_upwards [ae_eventual_rescale_harmonic_comparison_uniform h218 h217 hγ hγ2 hρ hρ1
    S hS hr hD e he he0, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hcomp harea hp
  filter_upwards [hcomp] with n hn
  intro u h C hC hlap hharm hbd x hx y hy
  have hc := hn u h C hC hlap hharm hbd x hx
  have hycell := Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 (he.1 n) y
  have hboundary : rescale (S.mε (e n)) (e n) (S.η ω) u y =
      rescale (S.mε (e n)) (e n) (S.η ω) h y := by
    simp only [rescale]
    rw [hbd _ ⟨y, hycell, hy⟩]
  rw [hboundary]
  have ht := abs_sub_le (rescale (S.mε (e n)) (e n) (S.η ω) u x)
    (rescale (S.mε (e n)) (e n) (S.η ω) h x)
    (rescale (S.mε (e n)) (e n) (S.η ω) h y)
  linarith

end MatedCRT

#print axioms MatedCRT.abs_rescale_boundary_pair_le_harmonic_add_expectedExitTime

#print axioms MatedCRT.ae_eventual_boundary_pair_harmonic_comparison_uniform
