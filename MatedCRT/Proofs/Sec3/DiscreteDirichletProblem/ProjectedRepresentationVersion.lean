import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.EnvSigmaRepresentation
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.FiniteDomainBridge
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedLocalVersion
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationTail

/-! Measurable versions of projected finite-domain Dirichlet solutions. -/

namespace MatedCRT

open Set Metric MeasureTheory _root_.HarmonicBalls

/-- Finite-domain representation yields an environment-measurable local version
for projected boundary data and a Hölder source on the disk. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_projected_solution_of_finiteDomain
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hfinite : FiniteDomainDirichletRepresentation)
    (ε : ℝ) (hε : 0 < ε) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (ψ φ : ℂ → ℝ) (hψ : IsHolderContinuousOn ψ (ball z r))
    (hφ : IsHolderContinuousOn φ (closedBall z r)) (F : Ω → ℤ → ℝ)
    (hdata : ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r),
        F ω b = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b))) :
    ∃ v : Ω → ℤ → ℝ, (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices ε (S.η ω) (ball z r), v ω a = F ω a := by
  classical
  obtain ⟨q, hqm, hq⟩ := exists_measurable_cutoff_of_holderOn isOpen_ball.measurableSet hψ
  obtain ⟨v, hvm, hv⟩ := hS.exists_envSigma_local_solution_on_event ε (ball z r)
    (Or.inl isOpen_ball) univ
    (fun ω b => q (vertexPoint ε (S.η ω) b))
    (fun ω b => S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) b))) F
    (fun b => by simpa only [one_mul] using S.measurable_envSigma_vertex_data ε 1 q hqm b)
    (fun b => S.measurable_envSigma_projected_vertex_data ε hr φ hφ b) (by
      filter_upwards [hdata, hS.ae_disk_dirichlet_decomposition_geometry hγ hγ2,
        hS.isAreaParametrized, hS.ae_tendsto_cocompact,
        adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω hF hgeom hη hp hadj _
      obtain ⟨hA, hB, hnb, hsub, hexit⟩ := hgeom ε hε z r hr
      have hlf := Tightness.isLocallyFiniteMult_of_cells hη.1 hp hε (hadj ε hε)
      refine ⟨hA, fun a ha => ?_⟩
      obtain ⟨hex, hrepr⟩ := hfinite (S.mult ε ω) hlf (S.mult_succ_ne_zero hε.le ω)
        _ _ hA hB hnb hexit (F ω) (fun b => ψ (vertexPoint ε (S.η ω) b)) hF.1 a (hsub ha)
      rw [hrepr]
      congr 1
      · apply integral_congr_ae
        filter_upwards [hex] with x hx
        rw [Set.indicator_of_mem hx, hF.2 _ hx]
      · apply Finset.sum_congr rfl
        intro b hb
        rw [hq _ (vertexPoint_mem_ball_of_mem_interior hε hη.1 (hA.mem_toFinset.mp hb))])
  exact ⟨v, hvm, hv.mono fun _ h => h (mem_univ _)⟩

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.exists_envSigma_projected_solution_of_finiteDomain
