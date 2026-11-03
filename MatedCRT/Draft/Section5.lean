import MatedCRT.Defs.Setting
import MatedCRT.Defs.Sandpile

/-!
# Section 5: statements of Proposition 5.1 and Lemmas 5.2-5.4 (lines 1952-2229)

The IDLA lower bound. Conventions: see `MatedCRT/Draft/Section1.lean` and `MatedCRT/Draft/Section4.lean`.
`ρ ∈ (0, 1)` is fixed and universally quantified. `G^ε_A` for a vertex set `A` is `greenFn (S.mult ε ω) A`
(Remark 2.12). Annealed probabilities of IDLA events restricted to an event `F` of the environment are
`∫⁻ ω in F, (conditional probability given (h, η)) ∂P`.

The condition `dist(η(a), ∂η(Λ^ε_t)) > δ` (lines 1999, 2009) is read with `η(Λ^ε_t)` the union of the cells of
`Λ^ε_t` (`fillCells`): for the finite point set `{η(a) : a ∈ Λ^ε_t}` the distance would be `0` and the lemmas empty
(ESCALATIONS E-A8).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Proposition 5.1** (prop:IDLA-lower-bound, line 1959). For each `δ ∈ (0, ρ)` and `t > 0`, on the event `{t < T}`,
except on an event of probability tending to `0` as `ε → 0`, `B⁻_δ(Λ_t) ⊆ Ā_ε(⌊t ε⁻¹⌋)`. Moreover this holds when the
walkers are stopped upon exiting `V^ε(Λ_t)`. -/
def IDLALowerBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    Tendsto (fun ε => ∫⁻ ω in {ω | t < clusterExitTime (Λ ω) ρ}, walkerSequenceLaw (S.mult ε ω) 0
        {xs | ¬ innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω) (idlaCluster xs ⌊t / ε⌋₊)} ∂S.P)
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => ∫⁻ ω in {ω | t < clusterExitTime (Λ ω) ρ}, walkerSequenceLaw (S.mult ε ω) 0
        {xs | ¬ innerNbhd δ (Λ ω t) ⊆
          fillCells ε (S.η ω) (stoppedIDLACluster (cellVertices ε (S.η ω) (Λ ω t)) xs ⌊t / ε⌋₊)} ∂S.P)
      (𝓝[>] 0) (𝓝 0)

/-- **Lemma 5.2** (lemma:general-idla-lower-bound, line 1974; reformulation of LBG92 Section 3). Suppose
`O₁^ε ⊆ O₂^ε ⊆ V^ε(B_ρ)` are `σ(h, η)`-measurable domains (connected vertex sets) containing the origin such that, for
`K_ε > 0`, a deterministic `q > 0` and a `σ(h, η)`-measurable finite random variable `𝔰 > 0`, with probability tending
to `1` as `ε → 0`,
`K_ε G^ε_{O₂}(0, a) ≥ (1 + 𝔰) ∑_{b ∈ O₂} G^ε_{O₂}(b, a)` and `∑_{b ∈ O₂} G^ε_{O₂}(b, a) / G^ε_{O₂}(a, a) ≥ ε^{-q}`
for all `a ∈ O₁` (eq:mean-value-ineq, eq:L-lower-bound). Then `O₁^ε ⊆ A_ε(⌊K_ε⌋)` with probability tending to `1`, also
when the walkers are stopped upon exiting `O₂^ε`. (`K_ε` is deterministic, as in the application `K_ε = t ε⁻¹`.) -/
def GeneralIDLALowerBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (O₁ O₂ : ℝ → Ω → Set ℤ) (K : ℝ → ℝ) (q : ℝ) (s : Ω → ℝ),
    (∀ ε k, MeasurableSet[S.envSigma] {ω | k ∈ O₁ ε ω}) → (∀ ε k, MeasurableSet[S.envSigma] {ω | k ∈ O₂ ε ω}) →
    (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, O₁ ε ω ⊆ O₂ ε ω ∧ O₂ ε ω ⊆ cellVertices ε (S.η ω) (ball 0 ρ) ∧ (0 : ℤ) ∈ O₁ ε ω ∧
      IsVConnected (S.mult ε ω) (O₁ ε ω) ∧ IsVConnected (S.mult ε ω) (O₂ ε ω)) →
    (∀ ε, 0 < K ε) → 0 < q → Measurable[S.envSigma] s → (∀ ω, 0 < s ω) →
    ProbTendsToOne S.P (fun ε => {ω | ∀ a ∈ O₁ ε ω,
      (1 + s ω) * ∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a ≤
        K ε * greenFn (S.mult ε ω) (O₂ ε ω) 0 a ∧
      ε ^ (-q) ≤ (∑' b : O₂ ε ω, greenFn (S.mult ε ω) (O₂ ε ω) b a) / greenFn (S.mult ε ω) (O₂ ε ω) a a}) →
    Tendsto (fun ε => ∫⁻ ω, walkerSequenceLaw (S.mult ε ω) 0
        {xs | ¬ O₁ ε ω ⊆ idlaCluster xs ⌊K ε⌋₊} ∂S.P) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => ∫⁻ ω, walkerSequenceLaw (S.mult ε ω) 0
        {xs | ¬ O₁ ε ω ⊆ stoppedIDLACluster (O₂ ε ω) xs ⌊K ε⌋₊} ∂S.P) (𝓝[>] 0) (𝓝 0)

/-- **Lemma 5.3** (lemma:mean-value-ineq, line 1995). For each `δ ∈ (0, ρ)` and `t > 0`, on the event `{t < T}`, there
is a `σ(h, η)`-measurable finite random variable `𝔰 = 𝔰(δ) > 0` such that, except on an event of probability tending
to `0` as `ε → 0`, `(t ε⁻¹) G^ε_{Λ^ε_t}(0, a) ≥ (1 + 𝔰) ∑_{b ∈ Λ^ε_t} G^ε_{Λ^ε_t}(b, a)` for all `a ∈ Λ^ε_t` with
`dist(η(a), ∂Λ̄^ε_t) > δ`. -/
def MeanValueInequalityStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
  ∃ s : Ω → ℝ, Measurable[S.envSigma] s ∧ (∀ ω, 0 < s ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ matedDiscreteCluster ε (S.η ω) ρ t,
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (matedDiscreteCluster ε (S.η ω) ρ t))) →
        (1 + s ω) * ∑' b : matedDiscreteCluster ε (S.η ω) ρ t,
            greenFn (S.mult ε ω) (matedDiscreteCluster ε (S.η ω) ρ t) b a ≤
          t / ε * greenFn (S.mult ε ω) (matedDiscreteCluster ε (S.η ω) ρ t) 0 a}

/-- **Lemma 5.4** (lemma:L-lower-bound, line 2005). There is a deterministic `q > 0` such that for each `δ ∈ (0, ρ)` and
`t > 0`, on the event `{t < T}`, except on an event of probability tending to `0` as `ε → 0`,
`∑_{b ∈ Λ^ε_t} G^ε_{Λ^ε_t}(b, a) / G^ε_{Λ^ε_t}(a, a) ≥ ε^{-q}` for all `a ∈ Λ^ε_t` with
`dist(η(a), ∂Λ̄^ε_t) > δ`. -/
def LLowerBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ q : ℝ, 0 < q ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ matedDiscreteCluster ε (S.η ω) ρ t,
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (matedDiscreteCluster ε (S.η ω) ρ t))) →
        ε ^ (-q) ≤ (∑' b : matedDiscreteCluster ε (S.η ω) ρ t,
            greenFn (S.mult ε ω) (matedDiscreteCluster ε (S.η ω) ρ t) b a) /
          greenFn (S.mult ε ω) (matedDiscreteCluster ε (S.η ω) ρ t) a a}

end MatedCRT
