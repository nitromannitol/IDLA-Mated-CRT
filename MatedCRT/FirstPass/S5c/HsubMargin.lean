import MatedCRT.FirstPass.S5c.MarginExact

/-!
# Countable family of margins for the auxiliary cover

`marginExact_proved` gives, at each fixed depth `d`, a measurable positive margin on the core
`{x ∈ B̄_ρ : d/2 ≤ dist(x, Λ_t(ω)ᶜ)}`. Taking one such margin for every depth `d n` of a deterministic
sequence and intersecting the countably many almost-sure conclusions gives one probability-one event on
which every margin holds simultaneously. No uncountable intersection over real depths is used, and no
new analytic premise is introduced: the hypotheses are exactly those of `marginExact_proved`.
-/

namespace MatedCRT.S5c

open HarmonicBalls MeasureTheory Filter Topology Set Metric

/-- **Countable margins (route note Step 2).** For a deterministic sequence of depths `d n > 0`, there are
measurable positive margins `b n` such that, almost surely on `{t < T}`, every margin `b n ω` lies below
`w_t - 2 w_{t/2}` on the core `{x ∈ B̄_ρ : d n / 2 ≤ dist(x, Λ_t(ω)ᶜ)}` (Armitage-Gardiner-style
core; each margin is `marginExact_proved` at its depth). -/
theorem marginExact_countable
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hF : FrozenLQGMeasureFieldMeasurable 𝒮)
    (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF3 : FrozenDiskGreenNonnegCont)
    (hG : FrozenGreenDiscPole)
    (hmin : FPStrongMinimumPrinciple)
    (hL : ConeScaleInvarianceCodedStmt)
    (hpos : ConeScaleRadiusPosStep)
    {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (d : ℕ → ℝ) (hd : ∀ n, 0 < d n) :
    ∃ b : ℕ → Ω → ℝ,
      (∀ n, Measurable[S.envSigma] (b n)) ∧
      (∀ n ω, 0 < b n ω) ∧
      ∀ᵐ ω ∂S.P,
        t < clusterExitTime (Λ ω) ρ →
        ∀ n : ℕ, ∀ x ∈ closedBall (0 : ℂ) ρ,
          d n / 2 ≤ infDist x (Λ ω t)ᶜ →
          b n ω ≤
            leastSupersolution (S.μ ω) ρ 0 t x -
              2 * leastSupersolution (S.μ ω) ρ 0 (t / 2) x := by
  classical
  have hn : ∀ n : ℕ, ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → ∀ x ∈ closedBall (0 : ℂ) ρ,
        d n / 2 ≤ infDist x (Λ ω t)ᶜ →
        c ω ≤ leastSupersolution (S.μ ω) ρ 0 t x -
          2 * leastSupersolution (S.μ ω) ρ 0 (t / 2) x :=
    fun n => marginExact_proved hγ0 hγ2 hF hF1 hF3 hG hmin hL hpos S hS Λ hΛ hρ (hd n) ht
  choose b hbm hbpos hbae using hn
  refine ⟨b, hbm, hbpos, ?_⟩
  filter_upwards [ae_all_iff.2 hbae] with ω hω
  intro hT n x hx hxd
  exact hω n hT x hx hxd

end MatedCRT.S5c
