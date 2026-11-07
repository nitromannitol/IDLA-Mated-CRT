import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ProjectedLocalVersion

/-! Projected boundary data on good events. -/

namespace MatedCRT

open Set Metric MeasureTheory

/-- Measurable interior values on a good event glue to projected Hölder
boundary values on the same event. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_projected_closedDisk_version_on_event
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) {z : ℂ} {r : ℝ} (hr : 0 < r) (φ : ℂ → ℝ)
    (hφ : IsHolderContinuousOn φ (closedBall z r)) (F v : Ω → ℤ → ℝ)
    (hvm : ∀ a, Measurable[S.envSigma] fun ω => v ω a) (G : Set Ω)
    (hv : ∀ᵐ ω ∂S.P, ω ∈ G →
      ∀ a ∈ cellVertices ε (S.η ω) (ball z r), v ω a = F ω a)
    (hb : ∀ᵐ ω ∂S.P, ω ∈ G → ∀ a ∈ cellVertices ε (S.η ω) (sphere z r),
      F ω a = S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) a))) :
    ∃ w : Ω → ℤ → ℝ, (∀ a, Measurable[S.envSigma] fun ω => w ω a) ∧
      ∀ᵐ ω ∂S.P, ω ∈ G →
        ∀ a ∈ cellVertices ε (S.η ω) (closedBall z r), w ω a = F ω a := by
  classical
  obtain ⟨V, hVm, hVa⟩ := hS.exists_envSigma_measurable_cellVertices ε (sphere z r)
    (Or.inr isClosed_sphere)
  let g : Ω → ℤ → ℝ := fun ω a =>
    S.mε ε * φ (ballRetraction z r (vertexPoint ε (S.η ω) a))
  let w : Ω → ℤ → ℝ := fun ω a => if a ∈ V ω then g ω a else v ω a
  refine ⟨w, ?_, ?_⟩
  · intro a
    have hgm : Measurable[S.envSigma] fun ω => g ω a :=
      S.measurable_envSigma_projected_vertex_data ε hr φ hφ a
    let : MeasurableSpace Ω := S.envSigma
    exact Measurable.ite (measurableSet_setOfPred.mpr ((measurable_set_mem a).comp hVm))
      hgm (hvm a)
  · filter_upwards [hVa, hv, hb] with ω hV hvω hbω hg a ha
    rcases cellVertices_closedBall_subset_interior_union_sphere hr ha with hai | hab
    · by_cases hbd : a ∈ cellVertices ε (S.η ω) (sphere z r)
      · simpa [w, g, hV, hbd] using (hbω hg a hbd).symm
      · simpa [w, hV, hbd] using hvω hg a hai.1
    · simpa [w, g, hV, hab] using (hbω hg a hab).symm

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.exists_envSigma_projected_closedDisk_version_on_event
