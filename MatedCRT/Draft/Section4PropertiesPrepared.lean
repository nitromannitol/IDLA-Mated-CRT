import MatedCRT.Draft.Section4Prepared

/-! Lemma 4.8 on a prepared deterministic sequence, corrected paper lines 1956–1972. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- Lemma 4.8 [C11]: for fixed `t` and an input sequence, one deterministic
thinning gives relative compactness and the stated properties of every limit. -/
def SubsequentialPropertiesPreparedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t → ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
    (∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ w : ℂ → ℝ,
      ContinuousOn w (closedBall 0 ρ) ∧
      TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (e (φ (ψ (θ k)))) ω)
        w atTop (closedBall 0 ρ)) ∧
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

end MatedCRT
