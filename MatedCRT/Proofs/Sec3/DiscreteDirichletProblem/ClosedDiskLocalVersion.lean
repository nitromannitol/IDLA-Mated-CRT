import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentCells
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ClosedDomainGeometry

/-! Extending a measurable interior representative to the boundary cells. -/

namespace MatedCRT

open Set Metric MeasureTheory

/-- Measurable interior and boundary versions glue to a measurable version on
all cells meeting the closed disk. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_closedDisk_version
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (F v g : Ω → ℤ → ℝ)
    (hvm : ∀ a, Measurable[S.envSigma] fun ω => v ω a)
    (hgm : ∀ a, Measurable[S.envSigma] fun ω => g ω a)
    (hv : ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices ε (S.η ω) (ball z r), v ω a = F ω a)
    (hg : ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices ε (S.η ω) (sphere z r), g ω a = F ω a) :
    ∃ w : Ω → ℤ → ℝ, (∀ a, Measurable[S.envSigma] fun ω => w ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a ∈ cellVertices ε (S.η ω) (closedBall z r), w ω a = F ω a := by
  classical
  obtain ⟨V, hVm, hVa⟩ := hS.exists_envSigma_measurable_cellVertices ε (sphere z r)
    (Or.inr isClosed_sphere)
  let w : Ω → ℤ → ℝ := fun ω a => if a ∈ V ω then g ω a else v ω a
  refine ⟨w, ?_, ?_⟩
  · intro a
    let : MeasurableSpace Ω := S.envSigma
    exact Measurable.ite (measurableSet_setOfPred.mpr ((measurable_set_mem a).comp hVm))
      (hgm a) (hvm a)
  · filter_upwards [hVa, hv, hg] with ω hV hvω hgω
    intro a ha
    rcases cellVertices_closedBall_subset_interior_union_sphere hr ha with hai | hab
    · by_cases hbd : a ∈ cellVertices ε (S.η ω) (sphere z r)
      · simpa [w, hV, hbd] using hgω a hbd
      · simpa [w, hV, hbd] using hvω a hai.1
    · simpa [w, hV, hab] using hgω a hab

end MatedCRT

#print axioms MatedCRT.MatedCRTEnv.IsValid.exists_envSigma_closedDisk_version
