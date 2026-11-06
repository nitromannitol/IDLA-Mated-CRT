import MatedCRT.Proofs.Sec4.ConvergenceDivisible.EnvSigmaLeastSupersolution
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentVertex
import MatedCRT.Draft.Section4Prepared
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Selection

/-! Environmental point evaluations for measurable odometer selection. -/

namespace MatedCRT

open MeasureTheory Set Filter Topology

/-- At a fixed mesh and spatial point, the rescaled least supersolution has an
environment-measurable version. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_rescaledOdometer_at
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) {ε : ℝ} (hε : 0 < ε)
    (ρ t : ℝ) (ht : 0 < t) (x : ℂ)
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite) :
    ∃ F : Ω → ℝ, Measurable[S.envSigma] F ∧ ∀ᵐ ω ∂S.P,
      F ω = rescaledMatedLeastSupersolution S ρ t ε ω x := by
  obtain ⟨a, ha, hae⟩ := hS.exists_envSigma_measurable_vertexOf hε x
  choose G hG hGa using fun b : ℤ =>
    hS.exists_envSigma_measurable_matedLeastSupersolution hγ hγ' hε ρ t ht b hlf
  have hmeas : Measurable[S.envSigma] (fun ω => G (a ω) ω) := by
    let : MeasurableSpace Ω := S.envSigma
    exact measurable_countable_evaluation a ha G hG
  refine ⟨fun ω => (S.mε ε)⁻¹ * G (a ω) ω, measurable_const.mul hmeas, ?_⟩
  filter_upwards [hae, ae_all_iff.mpr hGa] with ω haω hGω
  simp [haω, hGω, rescaledMatedLeastSupersolution, rescale]

/-- A measurable diagonal subsequence makes every sampled odometer evaluation
converge wherever each sampled sequence is eventually bounded. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_diagonal_rescaledOdometer
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) (e : ℕ → ℝ) (he : ∀ n, 0 < e n)
    (ρ t : ℝ) (ht : 0 < t) (x : ℕ → ℂ)
    (hlf : ∀ n, ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult (e n) ω b c ≠ 0}.Finite) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∀ i,
        (∃ M : ℝ, ∀ᶠ n in atTop, |rescaledMatedLeastSupersolution S ρ t (e n) ω (x i)| ≤ M) →
        ∃ l : ℝ, Tendsto (fun k => rescaledMatedLeastSupersolution S ρ t (e (Φ ω k)) ω (x i))
          atTop (𝓝 l) := by
  choose F hF hFa using fun n i =>
    hS.exists_envSigma_measurable_rescaledOdometer_at hγ hγ' (he n) ρ t ht (x i) (hlf n)
  obtain ⟨Φ, hΦm, hΦ⟩ := @Tightness.exists_measurable_diagonal_subseq Ω S.envSigma
    (fun ω n i => F n i ω) (fun n i => hF n i)
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hFa n))] with ω hω
  refine ⟨(hΦ ω).1, ?_⟩
  intro i hb
  have hb' : ∃ M : ℝ, ∀ᶠ n in atTop, |F n i ω| ≤ M := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, hM.mono fun n hn => by simpa [hω n i] using hn⟩
  obtain ⟨l, hl⟩ := (hΦ ω).2 i hb'
  exact ⟨l, by simpa only [hω] using hl⟩

end MatedCRT
