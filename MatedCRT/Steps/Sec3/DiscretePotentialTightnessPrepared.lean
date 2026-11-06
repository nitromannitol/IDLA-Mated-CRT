import MatedCRT.Draft.Section3Prepared

/-! Obligations in the corrected proof of Lemma 3.1, paper lines 1031–1185. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- Deterministic preparation gives one event on which all countable families
have a common pathwise convergent subsequence (corrected proof lines 1031–1185). -/
def PreparedTightnessPathwiseStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ A : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ A) ∧
    ∀ (D : ℕ → Set ℂ), (∀ j, D j ⊆ ball 0 ρ ∧ IsOpen (D j) ∧ IsConnected (D j)) →
    ∀ (E : Ω → ℕ → ℝ) (u : ℕ → Ω → ℕ → ℤ → ℝ) (C : ℕ → Ω → ℝ),
      (∀ n, Measurable[S.envSigma] fun ω => E ω n) →
      (∀ ω n, E ω n ∈ range (e ∘ φ)) → (∀ ω, Tendsto (E ω) atTop (𝓝 0)) →
      (∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a) →
      (∀ j, Measurable[S.envSigma] (C j)) →
      ∀ ω ∈ A, PreparedTightnessBounds S D E u C ω →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ j, PreparedTightnessLimit S (D j) E (u j) (fun _ => ψ) ω

/-- The pathwise simultaneous extraction admits an environment-measurable
selection on the prepared event (corrected proof of Lemma 3.1). -/
def PreparedTightnessSelectionStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ A : Set Ω, ∀ (D : ℕ → Set ℂ),
    (∀ j, D j ⊆ ball 0 ρ ∧ IsOpen (D j) ∧ IsConnected (D j)) →
  ∀ (E : Ω → ℕ → ℝ) (u : ℕ → Ω → ℕ → ℤ → ℝ) (C : ℕ → Ω → ℝ),
    (∀ n, Measurable[S.envSigma] fun ω => E ω n) →
    (∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a) →
    (∀ j, Measurable[S.envSigma] (C j)) →
    (∀ ω ∈ A, PreparedTightnessBounds S D E u C ω →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ j, PreparedTightnessLimit S (D j) E (u j) (fun _ => ψ) ω) →
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ ω ∈ A, PreparedTightnessBounds S D E u C ω →
        StrictMono (Φ ω) ∧ ∀ j, PreparedTightnessLimit S (D j) E (u j) Φ ω

/-- The prepared pathwise estimates and measurable selection give the
corrected Lemma 3.1. -/
theorem discretePotentialTightnessPrepared_of_steps {𝒮 : SpaceFillingSLEModel}
    (hp : PreparedTightnessPathwiseStep 𝒮) (hs : PreparedTightnessSelectionStep 𝒮) :
    DiscretePotentialTightnessPreparedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS e he he0
  obtain ⟨φ, hφ, A, hA, hpath⟩ := hp γ hγ hγ2 ρ hρ hρ1 Ω S hS e he he0
  refine ⟨φ, hφ, A, hA, ?_⟩
  intro D hD E u C hEm hEr hE0 hum hCm
  exact hs γ hγ hγ2 ρ hρ hρ1 Ω S hS A D hD E u C hEm hum hCm
    (hpath D hD E u C hEm hEr hE0 hum hCm)

end MatedCRT
