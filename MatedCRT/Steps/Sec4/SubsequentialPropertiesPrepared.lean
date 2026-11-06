import MatedCRT.Draft.Section4PropertiesPrepared

/-! The every-limit identification obligation in Lemma 4.8, corrected paper lines 1974–2135. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- The identification of every uniform limit after deterministic preparation.
The separate comparison issue G3 remains an open part of this step. -/
def OdometerPropertiesPreparedIdentificationStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
    ∀ w : ℂ → ℝ,
      (ContinuousOn w (closedBall 0 ρ) ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (e (φ (ψ k))) ω)
          w atTop (closedBall 0 ρ)) →
      (∀ x ∈ closedBall (0 : ℂ) ρ, w x ≤ 0 ∧
        (x ≠ 0 → -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x ≤ w x)) ∧
      LaplacianGE w 0 (ball 0 ρ) ∧
      LaplacianLE w (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) (ball 0 ρ) ∧
      HasLaplacian w (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) 0
        {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x < w x}


/-- Lemma 4.8 from prepared compactness and prepared every-limit identification. -/
theorem subsequentialPropertiesPrepared_of_steps (𝒮 : SpaceFillingSLEModel)
    (h46 : SubsequentialConvergencePreparedStmt 𝒮)
    (hid : OdometerPropertiesPreparedIdentificationStep 𝒮) :
    SubsequentialPropertiesPreparedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS t ht e he he0
  obtain ⟨φ, hφ, hp⟩ := hid γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht e he he0
  obtain ⟨χ, hχ, hc, _⟩ := h46 γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht
    (e ∘ φ) (fun n => he _) (he0.comp hφ.tendsto_atTop)
  refine ⟨φ ∘ χ, hφ.comp hχ, ?_⟩
  filter_upwards [hp, hc] with ω hp hc
  refine ⟨hc.1, ?_⟩
  intro w hw
  obtain ⟨hwc, ψ, hψ, hconv⟩ := hw
  exact hp w ⟨hwc, χ ∘ ψ, hχ.comp hψ, hconv⟩

end MatedCRT
