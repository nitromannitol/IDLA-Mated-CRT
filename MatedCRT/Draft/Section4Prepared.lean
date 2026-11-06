import MatedCRT.Draft.Section4

/-! Corrected fixed-sequence formulation of Lemma 4.6, paper lines 1903–1910. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- Relative compactness and Hölder regularity of every uniform limit along a
prepared mesh sequence, expressed using subsequences. -/
def OdometerPreparedCompactness {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    (ρ t : ℝ) (e : ℕ → ℝ) (ω : Ω) : Prop :=
  (∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ,
    ContinuousOn w (closedBall 0 ρ) ∧
    TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t (e (ψ (θ n))) ω)
      w atTop (closedBall 0 ρ)) ∧
  (∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ w : ℂ → ℝ,
    TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t (e (ψ n)) ω)
      w atTop (closedBall 0 ρ) → IsHolderContinuousOn w (closedBall 0 ρ))

/-- Lemma 4.6 [C12]: fixed time and deterministic input precede the deterministic
thinning and its almost-sure event; the measurable selection uses that thinning. -/
def SubsequentialConvergencePreparedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
    (∀ᵐ ω ∂S.P, OdometerPreparedCompactness S ρ t (e ∘ φ) ω) ∧
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ w : ℂ → ℝ,
        ContinuousOn w (closedBall 0 ρ) ∧ IsHolderContinuousOn w (closedBall 0 ρ) ∧
        TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (e (φ (Φ ω k))) ω)
          w atTop (closedBall 0 ρ)

end MatedCRT
