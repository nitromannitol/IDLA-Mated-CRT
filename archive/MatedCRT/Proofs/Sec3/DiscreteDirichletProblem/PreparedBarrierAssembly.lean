import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.BoundaryBarrierModulus

/-! Common-event assembly of the projected Dirichlet boundary modulus. -/

namespace MatedCRT

open Set Metric Filter Topology MeasureTheory _root_.HarmonicBalls

/-- Along polynomially summable scales, the boundary-pair modulus follows
from the ordinary exit-time barrier modulus. The latter remains an explicit
assumption, not a consequence of the normalized exit-time estimates. -/
theorem ae_boundary_pair_modulus_of_exitTime_modulus
    {𝒮 : SpaceFillingSLEModel} (hH : DiscreteHolderContinuityCorrectedStep 𝒮)
    (hm : MepsScalingInput 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : ball z r ⊆ ball 0 ρ)
    (hsimply : SimplyConnectedSpace (ball z r))
    (e : ℕ → ℝ) (he : IsPolySummableScales e) (he0 : Tendsto e atTop (𝓝 0))
    (φ : ℂ → ℝ) (hφ : IsHolderContinuousOn φ (closedBall z r))
    (u h : Ω → ℕ → ℤ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hdata : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        |matedLaplacian (S.mult (e n) ω) (u ω n) a| ≤ C) ∧
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        matedLaplacian (S.mult (e n) ω) (h ω n) a = 0) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (sphere z r), u ω n b = h ω n b) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (frontier (ball z r)),
        h ω n b = S.mε (e n) * φ (ballRetraction z r (vertexPoint (e n) (S.η ω) b))))
    (hq : ∀ᵐ ω ∂S.P, Tightness.IsAsymptoticallyEquicontinuousOn
      (fun n x => (S.mε (e n))⁻¹ * (expectedExitTime (S.mult (e n) ω)
        (interiorCellVertices (e n) (S.η ω) (ball z r))
        (vertexOf (e n) (S.η ω) x)).toReal) (closedBall z r)) :
    ∀ᵐ ω ∂S.P, ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ closedBall z r, ∀ y ∈ sphere z r, ‖x - y‖ ≤ δ →
        |rescale (S.mε (e n)) (e n) (S.η ω) (u ω n) x -
          rescale (S.mε (e n)) (e n) (S.η ω) (u ω n) y| ≤ k := by
  have hhdata : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) (ball z r),
        matedLaplacian (S.mult (e n) ω) (h ω n) a = 0) ∧
      (∀ b ∈ cellVertices (e n) (S.η ω) (frontier (ball z r)),
        h ω n b = S.mε (e n) * φ (ballRetraction z r (vertexPoint (e n) (S.η ω) b))) := by
    filter_upwards [hdata] with ω hω
    filter_upwards [hω] with n hn
    exact ⟨hn.2.1, hn.2.2.2⟩
  filter_upwards [ae_projected_harmonic_spatial_modulus_of_holder_data hH hm h218 h217
    hγ hγ2 hρ hρ1 S hS hr hD hsimply e he he0 φ hφ h hhdata,
    ae_eventual_boundary_pair_harmonic_comparison_uniform h218 h217 hγ hγ2 hρ hρ1
      S hS hr hD e he he0, hq, hdata, hS.isAreaParametrized, hS.ae_tendsto_cocompact]
    with ω hh hcomp hqω hdataω harea hp
  apply boundary_pair_modulus_of_harmonic_and_barrier hC _ _ _ hh hqω
  · exact Eventually.of_forall fun n y hy =>
      rescale_expectedExitTime_eq_zero_on_sphere hr hy
        (Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 (he.1 n) y)
  · filter_upwards [hcomp, hdataω] with n hn hd
    exact hn (u ω n) (h ω n) C hC hd.1 hd.2.1 hd.2.2.1

end MatedCRT

#print axioms MatedCRT.ae_boundary_pair_modulus_of_exitTime_modulus
