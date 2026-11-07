import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.RandomExitMeasurable
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitTimeMeasurable

/-! Environment-measurable ordinary expected exit times. -/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory Topology
open scoped ENNReal

/-- Expected exit time is measurable in a random graph and killed domain. -/
theorem GreenEnvironment.measurable_expectedExitTime {Ω : Type} [MeasurableSpace Ω]
    (M : Ω → ℤ → ℤ → ℕ) (hM : ∀ j k, Measurable fun ω => M ω j k)
    (V : Ω → Set ℤ) (hV : Measurable V) (a : ℤ) :
    Measurable (fun ω => expectedExitTime (M ω) (V ω) a) := by
  let κ : Kernel Ω (ℕ → ℤ) := ⟨fun ω => srwLaw (M ω) a, GreenEnvironment.measurable_srwLaw M hM a⟩
  have : IsMarkovKernel κ := ⟨fun ω => isProbabilityMeasure_srwLaw _ _⟩
  have hm : Measurable (fun p : Ω × (ℕ → ℤ) => (vExitTime (V p.1) p.2 : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
      (GreenEnvironment.measurable_vExitTime_random_set V hV)
  exact hm.lintegral_kernel_prod_right' (κ := κ)

/-- The real ordinary expected exit time has an environment-measurable
version simultaneously at every starting vertex. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_expectedExitTime
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) :
    ∃ u : Ω → ℤ → ℝ, (∀ a, Measurable[S.envSigma] fun ω => u ω a) ∧
      ∀ᵐ ω ∂S.P, ∀ a, u ω a = (expectedExitTime (S.mult ε ω)
        (interiorCellVertices ε (S.η ω) D) a).toReal := by
  classical
  obtain ⟨B, hBm, hB⟩ := hS.exists_envSigma_measurable_bm
  obtain ⟨V, hVm, hV⟩ := hS.exists_envSigma_measurable_interiorCellVertices ε D hD
  let M : Ω → ℤ → ℤ → ℕ := fun ω j k =>
    bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k
  have hMm : ∀ j k, Measurable[S.envSigma] fun ω => M ω j k :=
    fun j k => (measurable_bmEdgeCount_path ε j k).comp hBm
  let u : Ω → ℤ → ℝ := fun ω a => (expectedExitTime (M ω) (V ω) a).toReal
  have hum : ∀ a, Measurable[S.envSigma] fun ω => u ω a := by
    let : MeasurableSpace Ω := S.envSigma
    intro a
    exact (GreenEnvironment.measurable_expectedExitTime M hMm V hVm a).ennreal_toReal
  refine ⟨u, hum, ?_⟩
  filter_upwards [hB, hV] with ω hb hv a
  have hM : M ω = S.mult ε ω := by
    funext j k
    simp only [M, MatedCRTEnv.mult, hb]
  simp only [u, hM, hv]

end MatedCRT

#print axioms MatedCRT.GreenEnvironment.measurable_expectedExitTime
#print axioms MatedCRT.MatedCRTEnv.IsValid.exists_envSigma_measurable_expectedExitTime
