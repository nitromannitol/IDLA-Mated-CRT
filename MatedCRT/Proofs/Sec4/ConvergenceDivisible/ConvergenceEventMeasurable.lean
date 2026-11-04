import MatedCRT.Proofs.Sec4.ConvergenceDivisible.RandomSetRegularization
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellSampling

/-! # Reduction of the convergence event measurability -/

namespace MatedCRT

open Set Metric MeasureTheory HarmonicBalls Filter Topology

/-- The convergence error event is null measurable if the continuum least
supersolution has a jointly measurable version and rational-time harmonic-ball
membership is null measurable. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_convergenceError_of_versions
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) {ρ t δ ε : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (hε : 0 < ε)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite)
    (hmem : ∀ (q : ℚ), 0 < (q : ℝ) → ∀ (z : ℂ),
      NullMeasurableSet {ω | z ∈ Λ ω q} S.P)
    (f : Ω × ℂ → ℝ) (hf : Measurable f)
    (hfae : ∀ᵐ ω ∂S.P, ∀ x ∈ ball (0 : ℂ) ρ,
      f (ω, x) = S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
      δ < |rescaledMatedLeastSupersolution S ρ t ε ω x -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|} S.P := by
  have hloc : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) := by
    filter_upwards [hS.isLQGMeasure] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hexit := nullMeasurableSet_lt_clusterExitTime_of_membership S.P S.μ Λ hΛ hloc hmem ρ t ht
  obtain ⟨E, hEsub, hE, hEae⟩ := hexit.exists_measurable_subset_ae_eq
  have hfc : ∀ᵐ ω ∂S.P, ω ∈ E → ContinuousOn (fun x => f (ω, x)) (ball 0 ρ) := by
    filter_upwards [hΛ, hfae] with ω hω hfe hωE
    have hT : t < clusterExitTime (Λ ω) ρ := hEsub hωE
    have hc := (coneFamily_leastSupersolution_continuous hω hρ ht hT).mono ball_subset_closedBall
    have hc' : ContinuousOn (fun x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x)
        (ball 0 ρ) := continuousOn_const.mul hc
    exact hc'.congr (fun x hx => hfe x hx)
  have hm := hS.nullMeasurableSet_matedLeast_deviation_on_event hγ hγ' hε ρ t ht hlf
    isOpen_ball isBounded_ball f hf E hE hfc δ
  apply hm.congr
  filter_upwards [hEae, hfae] with ω he hfω
  apply propext
  have he' : ω ∈ E ↔ t < clusterExitTime (Λ ω) ρ := iff_of_eq he
  constructor
  · rintro ⟨hEω, x, hx, hd⟩
    exact ⟨he'.mp hEω, x, hx, by simpa [hfω x hx] using hd⟩
  · rintro ⟨hT, x, hx, hd⟩
    exact ⟨he'.mpr hT, x, hx, by simpa [hfω x hx] using hd⟩

/-- Pointwise measurable continuum least supersolutions supply the harmonic-ball
membership needed in the convergence event. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_convergenceError_of_leastSupersolutions
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (hγ : 0 < γ) (hγ' : γ < 2) {ρ t δ ε : ℝ}
    (hρ : 0 < ρ) (ht : 0 < t) (hε : 0 < ε)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (hlf : ∀ᵐ ω ∂S.P, ∀ b, {c | S.mult ε ω b c ≠ 0}.Finite)
    (hv : ∀ (q : ℚ), 0 < (q : ℝ) → ∀ (n : ℕ) (z : ℂ), AEMeasurable
      (fun ω => leastSupersolution (S.μ ω) ((n : ℝ) + 1) 0 q z) S.P)
    (f : Ω × ℂ → ℝ) (hf : Measurable f)
    (hfae : ∀ᵐ ω ∂S.P, ∀ x ∈ ball (0 : ℂ) ρ,
      f (ω, x) = S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) :
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
      δ < |rescaledMatedLeastSupersolution S ρ t ε ω x -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|} S.P := by
  apply hS.nullMeasurableSet_convergenceError_of_versions hγ hγ' hρ ht hε Λ hΛ hlf
  · intro q hq z
    exact nullMeasurableSet_mem_coneFamily_of_leastSupersolutions S.P S.μ Λ q hq hΛ
      (hv q hq) z
  · exact hf
  · exact hfae

end MatedCRT
