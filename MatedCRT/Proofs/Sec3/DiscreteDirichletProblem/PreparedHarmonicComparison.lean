import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.HarmonicComparison
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExpectedExitSize

/-! The ordinary exit-time barrier along prepared mesh scales. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls

/-- Along any polynomially summable sequence of meshes, the expected-exit-time
comparison holds eventually on the entire closed disk. Lemmas 2.17 and 2.18
supply the finiteness of the ordinary exit times on the same event. -/
theorem ae_eventual_rescale_harmonic_comparison
    {𝒮 : SpaceFillingSLEModel} (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (e : ℕ → ℝ) (he : IsPolySummableScales e) (he0 : Tendsto e atTop (𝓝 0))
    (u h : Ω → ℕ → ℤ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hdata : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (e n) ω) (u ω n) a| ≤ C) ∧
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        matedLaplacian (S.mult (e n) ω) (h ω n) a = 0) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), u ω n b = h ω n b)) :
    ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop, ∀ x ∈ closedBall z r,
      |rescale (S.mε (e n)) (e n) (S.η ω) (u ω n) x -
        rescale (S.mε (e n)) (e n) (S.η ω) (h ω n) x| ≤
        C * ((S.mε (e n))⁻¹ *
          (expectedExitTime (S.mult (e n) ω)
            (interiorCellVertices (e n) (S.η ω) (ball z r))
              (vertexOf (e n) (S.η ω) x)).toReal) := by
  filter_upwards [ae_eventual_expectedExit_size_of_statements h218 h217 hγ hγ2 hρ hρ1 S hS hD e he he0,
    hdata, hS.isAreaParametrized, hS.ae_tendsto_cocompact,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hq hdata harea hp hadj
  obtain ⟨_, hq⟩ := hq
  filter_upwards [hq, hdata] with n hn hd
  intro x hx
  have hε := he.1 n
  exact abs_rescale_sub_harmonic_le_expectedExitTime hε hr
    (inv_nonneg.2 (medianOf_nonneg _)) harea.1 hp (hadj (e n) hε)
    (S.mult_succ_ne_zero hε.le ω) (u ω n) (h ω n) hC hd.1 hd.2.1 hd.2.2
    (fun a ha => (hn a ha.1).1) hx
    (Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x)

/-- The same almost-sure event works for every pair of discrete functions and
source bound, including functions selected after the environment is sampled. -/
theorem ae_eventual_rescale_harmonic_comparison_uniform
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
      ∀ x ∈ closedBall z r,
        |rescale (S.mε (e n)) (e n) (S.η ω) u x -
          rescale (S.mε (e n)) (e n) (S.η ω) h x| ≤
          C * ((S.mε (e n))⁻¹ *
            (expectedExitTime (S.mult (e n) ω)
              (interiorCellVertices (e n) (S.η ω) (ball z r))
                (vertexOf (e n) (S.η ω) x)).toReal) := by
  filter_upwards [ae_eventual_expectedExit_size_of_statements h218 h217 hγ hγ2 hρ hρ1 S hS hD e he he0,
    hS.isAreaParametrized, hS.ae_tendsto_cocompact,
    adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hq harea hp hadj
  obtain ⟨_, hq⟩ := hq
  filter_upwards [hq] with n hn
  intro u h C hC hlap hharm hbd x hx
  have hε := he.1 n
  exact abs_rescale_sub_harmonic_le_expectedExitTime hε hr
    (inv_nonneg.2 (medianOf_nonneg _)) harea.1 hp (hadj (e n) hε)
    (S.mult_succ_ne_zero hε.le ω) u h hC hlap hharm hbd
    (fun a ha => (hn a ha.1).1) hx
    (Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x)

end MatedCRT

#print axioms MatedCRT.ae_eventual_rescale_harmonic_comparison

#print axioms MatedCRT.ae_eventual_rescale_harmonic_comparison_uniform
