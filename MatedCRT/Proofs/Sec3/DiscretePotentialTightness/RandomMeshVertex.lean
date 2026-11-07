import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RescaleMeasurable
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.SelectionStep
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentVertex

/-! # Measurable cell representatives at random mesh sizes -/

namespace MatedCRT

open Set MeasureTheory Filter Topology

/-- A measurable mesh valued in a fixed positive sequence admits an
    environment-measurable version of the cell containing a fixed point. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_vertexOf_randomMesh
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (E : Ω → ℝ)
    (hEm : Measurable[S.envSigma] E) (hEr : ∀ ω, E ω ∈ range e) (x : ℂ) :
    ∃ a : Ω → ℤ, Measurable[S.envSigma] a ∧
      ∀ᵐ ω ∂S.P, a ω = vertexOf (E ω) (S.η ω) x := by
  classical
  have hex : ∀ ω, ∃ j, E ω = e j := fun ω => by
    obtain ⟨j, hj⟩ := hEr ω
    exact ⟨j, hj.symm⟩
  let I : Ω → ℕ := fun ω => Nat.find (hex ω)
  have hI : Measurable[S.envSigma] I := by
    let : MeasurableSpace Ω := S.envSigma
    exact Tightness.measurable_natFind hex (fun j => hEm (measurableSet_singleton (e j)))
  choose a ham hae using fun j => hS.exists_envSigma_measurable_vertexOf (he j) x
  have ham' : Measurable[S.envSigma] (fun ω => a (I ω) ω) := by
    let : MeasurableSpace Ω := S.envSigma
    exact Tightness.measurable_comp_nat ham hI
  refine ⟨fun ω => a (I ω) ω, ham', ?_⟩
  filter_upwards [ae_all_iff.mpr hae] with ω hω
  rw [hω (I ω), ← Nat.find_spec (hex ω)]

/-- The rescaling of an environment-measurable vertex field has a measurable
    version at a fixed point, even when the mesh is random in a countable set. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_rescale_randomMesh
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (E : Ω → ℝ)
    (hEm : Measurable[S.envSigma] E) (hEr : ∀ ω, E ω ∈ range e)
    (u : Ω → ℤ → ℝ) (hu : ∀ a, Measurable[S.envSigma] fun ω => u ω a) (x : ℂ) :
    ∃ f : Ω → ℝ, Measurable[S.envSigma] f ∧ ∀ᵐ ω ∂S.P,
      f ω = rescale (S.mε (E ω)) (E ω) (S.η ω) (u ω) x := by
  obtain ⟨a, ham, hae⟩ := hS.exists_envSigma_measurable_vertexOf_randomMesh e he E hEm hEr x
  have hu' : Measurable[S.envSigma] (fun ω => u ω (a ω)) := by
    let : MeasurableSpace Ω := S.envSigma
    exact measurable_countable_evaluation a ham (fun b ω => u ω b) hu
  have hm : Measurable[S.envSigma] (fun ω => (S.mε (E ω))⁻¹) := by
    exact @Tightness.measurable_comp_range Ω S.envSigma e E hEm hEr
      (fun ε _ => (S.mε ε)⁻¹) (fun _ => measurable_const)
  refine ⟨fun ω => (S.mε (E ω))⁻¹ * u ω (a ω), hm.mul hu', ?_⟩
  filter_upwards [hae] with ω hω
  simp [rescale, hω]

/-- A single environment-measurable diagonal makes all bounded sampled values
    converge for a countable family of random-mesh fields. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_diagonal_rescale_randomMesh
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (e : ℕ → ℝ) (he : ∀ j, 0 < e j) (E : Ω → ℕ → ℝ)
    (hEm : ∀ n, Measurable[S.envSigma] fun ω => E ω n)
    (hEr : ∀ ω n, E ω n ∈ range e)
    (u : ℕ → Ω → ℕ → ℤ → ℝ)
    (hu : ∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a) (x : ℕ → ℂ) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∀ j i,
        (∃ M : ℝ, ∀ᶠ n in atTop,
          |rescale (S.mε (E ω n)) (E ω n) (S.η ω) (u j ω n) (x i)| ≤ M) →
        ∃ l : ℝ, Tendsto (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k))
          (S.η ω) (u j ω (Φ ω k)) (x i)) atTop (𝓝 l) := by
  choose f hfm hfa using fun (n c : ℕ) =>
    hS.exists_envSigma_measurable_rescale_randomMesh e he (fun ω => E ω n)
      (hEm n) (fun ω => hEr ω n) (fun ω => u c.unpair.1 ω n) (hu c.unpair.1 n)
      (x c.unpair.2)
  obtain ⟨Φ, hΦm, hΦ⟩ := @Tightness.exists_measurable_diagonal_subseq Ω S.envSigma
    (fun ω n c => f n c ω) (fun n c => hfm n c)
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hfa n))] with ω hω
  refine ⟨(hΦ ω).1, ?_⟩
  intro j i hb
  let c := Nat.pair j i
  have hb' : ∃ M : ℝ, ∀ᶠ n in atTop, |f n c ω| ≤ M := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, hM.mono fun n hn => ?_⟩
    simpa [hω n c, c] using hn
  obtain ⟨l, hl⟩ := (hΦ ω).2 c hb'
  exact ⟨l, by simpa only [hω, c, Nat.unpair_pair] using hl⟩

end MatedCRT
