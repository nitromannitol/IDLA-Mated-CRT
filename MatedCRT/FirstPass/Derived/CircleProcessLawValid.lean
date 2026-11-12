import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import MatedCRT.Proofs.Sec6.IterativeBound.FieldSigma
import MatedCRT.FirstPass.Derived.JointMeasureLawTwoSpaces
import MatedCRT.FirstPass.LPBridge.InRepoProofs

/-!
# The law of the circle average process is the same for all valid environments

Let `S` (on `Ω`) and `S'` (on `Ω'`) be valid environments with the same cone parameter `γ`. Their circle average
processes `(r, z) ↦ h_r(z)`, `r > 0` (product σ-algebra on `(0, ∞) × ℂ → ℝ`), have the same law: on each side the
process is almost surely the circle version of a field-measurable distribution, and the `γ`-quantum cone determines
the joint law of the distribution and its circle versions (`MatedCRT.Sec1.map_distribution_circles_eq_of_cones`).

With the two-space joint law of the LQG measure (`identDistrib_circleProcess_lqgMeasure_of_identDistrib`), the pair
(circle averages, `γ`-LQG measure) then has the same law for all valid environments, for `0 < γ < 2`.

* `measurable_circleProcess_of_valid`
* `identDistrib_circleProcess_of_valid`
* `aemeasurable_mu_of_valid`
* `identDistrib_circleProcess_lqgMeasure_of_valid`
-/

open MeasureTheory ProbabilityTheory Set HarmonicBalls

namespace MatedCRT.FirstPass.Derived

/-- The circle average process of a valid environment is a random variable (product σ-algebra). -/
theorem measurable_circleProcess_of_valid {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    Measurable (fun ω => circleProcess (S.hcirc ω)) :=
  measurable_pi_iff.2 fun p => hS.isQuantumCone.measurable_circle p.1 p.2 p.1.2

/-- **The circle average process has the same law for all valid environments** with the same cone parameter, on
arbitrary carriers. -/
theorem identDistrib_circleProcess_of_valid {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'} {𝒮 𝒮' : SpaceFillingSLEModel} {γ : ℝ}
    (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ) :
    IdentDistrib (fun ω => circleProcess (S.hcirc ω)) (fun ω => circleProcess (S'.hcirc ω)) S.P S'.P := by
  obtain ⟨H, hHm, hH⟩ := MatedCRT.Sec1.exists_fieldMeasurable_distribution_with_circles hS
  obtain ⟨H', hHm', hH'⟩ := MatedCRT.Sec1.exists_fieldMeasurable_distribution_with_circles hS'
  have hHmeas : Measurable H := hHm.mono (MatedCRTEnv.fieldSigma_le S hS) le_rfl
  have hHmeas' : Measurable H' := hHm'.mono (MatedCRTEnv.fieldSigma_le S' hS') le_rfl
  have hc := measurable_circleProcess_of_valid hS
  have hc' := measurable_circleProcess_of_valid hS'
  have hjoint : S.P.map (fun ω => (H ω, circleProcess (S.hcirc ω))) =
      S'.P.map (fun ω => (H' ω, circleProcess (S'.hcirc ω))) :=
    MatedCRT.Sec1.map_distribution_circles_eq_of_cones hS hS' hHmeas hHmeas'
      (hH.mono fun _ h => h.1) (hH'.mono fun _ h => h.1)
  refine ⟨hc.aemeasurable, hc'.aemeasurable, ?_⟩
  calc S.P.map (fun ω => circleProcess (S.hcirc ω))
      = (S.P.map (fun ω => (H ω, circleProcess (S.hcirc ω)))).map Prod.snd := by
        rw [Measure.map_map measurable_snd (hHmeas.prodMk hc)]
        rfl
    _ = (S'.P.map (fun ω => (H' ω, circleProcess (S'.hcirc ω)))).map Prod.snd := by rw [hjoint]
    _ = S'.P.map (fun ω => circleProcess (S'.hcirc ω)) := by
        rw [Measure.map_map measurable_snd (hHmeas'.prodMk hc')]
        rfl

/-- The `γ`-LQG measure of a valid environment is a random measure (almost everywhere measurable), `0 < γ < 2`. -/
theorem aemeasurable_mu_of_valid {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) :
    AEMeasurable S.μ S.P := by
  obtain ⟨g, hg, hμg⟩ := frozenLQGMeasureFieldMeasurable_holds 𝒮 γ hγ0 hγ2 Ω S hS
  exact ⟨g, hg.mono (MatedCRTEnv.fieldSigma_le S hS) le_rfl, hμg⟩

/-- **The pair (circle averages, LQG measure) has the same law for all valid environments** with the same cone
parameter `0 < γ < 2`, on arbitrary carriers. -/
theorem identDistrib_circleProcess_lqgMeasure_of_valid {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {S : MatedCRTEnv Ω} {S' : MatedCRTEnv Ω'} {𝒮 𝒮' : SpaceFillingSLEModel} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hS : S.IsValid 𝒮 γ) (hS' : S'.IsValid 𝒮' γ) :
    IdentDistrib (fun ω => (circleProcess (S.hcirc ω), S.μ ω))
      (fun ω => (circleProcess (S'.hcirc ω), S'.μ ω)) S.P S'.P := by
  have := hS'.isProbabilityMeasure
  have hμ : ∀ᵐ ω ∂S.P, IsLQGLimit γ (S.hcirc ω) (S.μ ω) := hS.isLQGMeasure
  have hν : ∀ᵐ ω ∂S'.P, IsLQGLimit γ (S'.hcirc ω) (S'.μ ω) := hS'.isLQGMeasure
  exact identDistrib_circleProcess_lqgMeasure_of_identDistrib
    hS.isQuantumCone.ae_continuousOn_circle hS'.isQuantumCone.ae_continuousOn_circle hμ hν
    (aemeasurable_mu_of_valid hγ0 hγ2 hS) (aemeasurable_mu_of_valid hγ0 hγ2 hS')
    (identDistrib_circleProcess_of_valid hS hS')

end MatedCRT.FirstPass.Derived
