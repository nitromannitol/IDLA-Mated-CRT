import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ClosedDiskLocalVersion
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedHarmonicSize

/-! Measurable local versions for projected Dirichlet boundary data. -/

namespace MatedCRT

open Set Metric MeasureTheory

/-- Projected Hölder boundary data have an environment-measurable vertex version. -/
theorem MatedCRTEnv.measurable_envSigma_projected_vertex_data
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ε : ℝ) {z : ℂ} {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : IsHolderContinuousOn φ (closedBall z r)) (a : ℤ) :
    Measurable[S.envSigma] fun ω =>
      S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) a)) := by
  obtain ⟨C, χ, hχ, _, hh⟩ := hφ
  have hc : Continuous (fun x => φ (ballRetraction z r x)) :=
    (hh.continuousOn hχ).comp_continuous (continuous_ballRetraction z hr)
      (fun x => ballRetraction_mem z hr x)
  have hη := Tightness.measurable_eta_of_envSigma S (ε * a)
  let : MeasurableSpace Ω := S.envSigma
  exact measurable_const.mul (hc.measurable.comp hη)

/-- An environment-measurable interior version extends to the closed disk
when the boundary values are given by projected Hölder data. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_projected_closedDisk_version
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) {z : ℂ} {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : IsHolderContinuousOn φ (closedBall z r)) (F v : Ω → ℤ → ℝ)
    (hvm : ∀ a, Measurable[S.envSigma] fun ω => v ω a)
    (hv : ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices ε (S.η ω) (ball z r), v ω a = F ω a)
    (hb : ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices ε (S.η ω) (sphere z r),
      F ω a = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) a))) :
    ∃ w : Ω → ℤ → ℝ, (∀ a, Measurable[S.envSigma] fun ω => w ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices ε (S.η ω) (closedBall z r), w ω a = F ω a := by
  apply hS.exists_envSigma_closedDisk_version ε hr F v
    (fun ω a => S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) a))) hvm
    (fun a => S.measurable_envSigma_projected_vertex_data ε hr φ hφ a) hv
  filter_upwards [hb] with ω hω a ha
  exact (hω a ha).symm

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.exists_envSigma_projected_closedDisk_version
