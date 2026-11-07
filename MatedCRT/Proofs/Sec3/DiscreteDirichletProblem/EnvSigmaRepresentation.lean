import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.MeasurableRepresentation
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentCells
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EnvSigmaEdge

/-! # Environment-measurable Green representatives -/

namespace MatedCRT

open Set MeasureTheory

/-- A finite-domain Green representation on a good event yields a version
measurable with respect to the environment sigma-algebra, even when the
solution itself is not measurable. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_local_solution_on_event
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (E : Set Ω)
    (q g F : Ω → ℤ → ℝ)
    (hq : ∀ b, Measurable[S.envSigma] fun ω => q ω b)
    (hg : ∀ b, Measurable[S.envSigma] fun ω => g ω b)
    (hrep : ∀ᵐ ω ∂S.P, ω ∈ E →
      ∃ h : (interiorCellVertices ε (S.η ω) D).Finite,
        ∀ a ∈ cellVertices ε (S.η ω) D,
          F ω a = (∫ x, g ω (vExitPosition (interiorCellVertices ε (S.η ω) D) x)
            ∂srwLaw (S.mult ε ω) a) -
            ∑ b ∈ h.toFinset, q ω b * greenFn (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) D) a b) :
    ∃ v : Ω → ℤ → ℝ, (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      ∀ᵐ ω ∂S.P, ω ∈ E → ∀ a ∈ cellVertices ε (S.η ω) D, v ω a = F ω a := by
  classical
  choose M hMm hMa using fun j k => hS.exists_envSigma_measurable_mult ε j k
  obtain ⟨V, hVm, hVa⟩ := hS.exists_envSigma_measurable_interiorCellVertices ε D hD
  have hMall : ∀ᵐ ω ∂S.P, ∀ j k, M j k ω = S.mult ε ω j k :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hMa j k
  let v : Ω → ℤ → ℝ := fun ω a =>
    (∫ x, g ω (vExitPosition (V ω) x) ∂srwLaw (fun j k => M j k ω) a) -
      ∑ᶠ b, if b ∈ V ω then q ω b * greenFn (fun j k => M j k ω) (V ω) a b else 0
  have hvm : ∀ a, Measurable[S.envSigma] fun ω => v ω a := by
    let : MeasurableSpace Ω := S.envSigma
    intro a
    exact (GreenEnvironment.measurable_expected_exitValue (fun ω j k => M j k ω) hMm V hVm g hg a).sub
      (GreenEnvironment.measurable_greenPotential (fun ω j k => M j k ω) hMm V hVm q hq a)
  refine ⟨v, hvm, ?_⟩
  filter_upwards [hMall, hVa, hrep] with ω hm hv hω he a ha
  have hm' : (fun j k => M j k ω) = S.mult ε ω := by funext j k; exact hm j k
  obtain ⟨hfin, hrepr⟩ := hω he
  dsimp [v]
  rw [hm', hv, GreenEnvironment.greenPotential_eq_sum hfin]
  exact (hrepr a ha).symm

/-- Measurable planar source and boundary data evaluated at a vertex are
environment-measurable, including deterministic boundary normalization. -/
theorem MatedCRTEnv.measurable_envSigma_vertex_data
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ε c : ℝ) (f : ℂ → ℝ) (hf : Measurable f) (a : ℤ) :
    Measurable[S.envSigma] fun ω => c * f (vertexPoint ε (S.η ω) a) := by
  have hη := Tightness.measurable_eta_of_envSigma S (ε * a)
  let : MeasurableSpace Ω := S.envSigma
  exact measurable_const.mul (hf.comp hη)

/-- The environment-measurable representative may be constructed directly
from measurable planar source and boundary data. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_local_solution_of_planar_data
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (E : Set Ω)
    (ψ φ : ℂ → ℝ) (hψ : Measurable ψ) (hφ : Measurable φ)
    (F : Ω → ℤ → ℝ)
    (hrep : ∀ᵐ ω ∂S.P, ω ∈ E →
      ∃ h : (interiorCellVertices ε (S.η ω) D).Finite,
        ∀ a ∈ cellVertices ε (S.η ω) D,
          F ω a = (∫ x, S.mε ε * φ (vertexPoint ε (S.η ω)
              (vExitPosition (interiorCellVertices ε (S.η ω) D) x))
            ∂srwLaw (S.mult ε ω) a) -
            ∑ b ∈ h.toFinset, ψ (vertexPoint ε (S.η ω) b) * greenFn (S.mult ε ω)
              (interiorCellVertices ε (S.η ω) D) a b) :
    ∃ v : Ω → ℤ → ℝ, (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      ∀ᵐ ω ∂S.P, ω ∈ E → ∀ a ∈ cellVertices ε (S.η ω) D, v ω a = F ω a := by
  apply hS.exists_envSigma_local_solution_on_event ε D hD E
    (fun ω b => ψ (vertexPoint ε (S.η ω) b))
    (fun ω b => S.mε ε * φ (vertexPoint ε (S.η ω) b)) F ?_ ?_ hrep
  · intro b
    simpa only [one_mul] using S.measurable_envSigma_vertex_data ε 1 ψ hψ b
  · exact fun b => S.measurable_envSigma_vertex_data ε (S.mε ε) φ hφ b

end MatedCRT
