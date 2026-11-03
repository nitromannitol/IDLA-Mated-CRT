import MatedCRT.Defs.Setting
import MatedCRT.Defs.Sandpile

/-!
# Section 7: statements of Proposition 7.1 and Lemmas 7.2-7.4 (lines 2913-3265)

The divisible sandpile upper bound. Conventions: see `MatedCRT/Draft/Section1.lean` and
`MatedCRT/Draft/Section4.lean`. `ρ ∈ (0, 1)` is fixed and universally quantified. `u^ε_t` is the stopped odometer
`stoppedOdometer ε η ρ t` (eq:stopped-odometer-de, line 2939, through `u^ε_t = w̃^ε_t + (t ε⁻¹) g^ε_{B_ρ}(0, ·)`,
line 2941); `Λ^ε_t` is `matedDiscreteCluster ε η ρ t`.

Cited: Lemma 7.4 (Levine-Peres 2009, Lemma 4.2; the paper gives a proof using GMS19 Lemma 2.6).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Proposition 7.1** (prop:div-sandpile-upper-bound, line 2917). For each `δ ∈ (0, ρ)` and `t > 0`, on the event
`{t < T}`, except on an event of probability tending to `0` as `ε → 0`, `D̄_ε(t ε⁻¹) ⊆ B⁺_δ(Λ_t)`. -/
def DivSandpileUpperBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε =>
      {ω | fillCells ε (S.η ω) (sandpileCluster (S.mult ε ω) (t / ε)) ⊆ outerNbhd δ (Λ ω t)}

/-- **Lemma 7.2** (lemma:mass-bound-odometer, line 2974). There are deterministic `C = C(ρ, γ) > 0` and
`𝐜₀ = 𝐜₀(ρ, γ) ∈ (0, 1)` such that with polynomially high probability as `ε → 0`: for all `t > 0`, all connected
`Θ ⊆ V^ε(B_ρ)` containing the origin, and all `s > 0`, `z ∈ ℂ` with `V^ε(B_s(z)) ⊆ V^ε(B_ρ) \ Θ`,
`|V^ε(B_{𝐜₀ s}(z)) ∩ Λ^ε_t| ≤ C sup_{∂Θ} u^ε_t`. -/
def MassBoundOdometerStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ c₀ < 1 ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω | ∀ t : ℝ, 0 < t → ∀ Θ : Set ℤ, Θ ⊆ cellVertices ε (S.η ω) (ball 0 ρ) →
    IsVConnected (S.mult ε ω) Θ → (0 : ℤ) ∈ Θ → ∀ (s : ℝ) (z : ℂ), 0 < s →
      cellVertices ε (S.η ω) (ball z s) ⊆ cellVertices ε (S.η ω) (ball 0 ρ) \ Θ →
      ((cellVertices ε (S.η ω) (ball z (c₀ * s)) ∩ matedDiscreteCluster ε (S.η ω) ρ t).ncard : ℝ) ≤
        C * ⨆ b : vBoundary (S.mult ε ω) Θ, stoppedOdometer ε (S.η ω) ρ t b}

/-- **Lemma 7.3** (lemma:odometer-bound-mass, line 3018). For all `t > 0` and all `B ⊆ V^ε(B_ρ) \ {0}`,
`u^ε_t(b) ≤ (sup_{∂B} u^ε_t) P[X^{b,ε} exits B before hitting B \ Λ^ε_t | h, η]` for all `b ∈ B`. Stated almost
surely, for all `ε > 0`. -/
def OdometerBoundMassStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ ε t : ℝ, 0 < ε → 0 < t → ∀ B : Set ℤ, B ⊆ cellVertices ε (S.η ω) (ball 0 ρ) \ {0} →
    ∀ b ∈ B, stoppedOdometer ε (S.η ω) ρ t b ≤
      (⨆ c : vBoundary (S.mult ε ω) B, stoppedOdometer ε (S.η ω) ρ t c) *
        (srwLaw (S.mult ε ω) b {x | vExitTime B x < vHitTime (B \ matedDiscreteCluster ε (S.η ω) ρ t) x}).toReal

/-- **Lemma 7.4** (lemma:crude-upper-bound, line 3058; Levine-Peres 2009, Lemma 4.2). For all `t > 0`, with
polynomially high probability as `ε → 0`: for every `a ∈ Λ^ε_t \ {0}` there is a path `a = a₀ ∼ a₁ ∼ ⋯ ∼ a_m = 0` in
`Λ^ε_t` with `u^ε_t(a_{i+1}) ≥ u^ε_t(a_i) + log(ε⁻¹)⁻²`.

Review-S (S4): the printed statement takes `a` and the path in `D_ε(t ε⁻¹) = cl(Λ^ε_t)` (eq:cluster-contained-in)
for the stopped odometer `u^ε_t`, which is defined on `V^ε(B_ρ)` only; read with `D_ε` the true sandpile cluster it
is false (when `D_ε(t ε⁻¹) ⊄ V^ε(B_{2ρ})`, which has positive probability, `u^ε_t = 0` at and around its far points).
The paper's object is the stopped odometer with its own cluster `Λ^ε_t = {u^ε_t > 0}` (`matedDiscreteCluster`,
inside `V^ε(B_ρ) \ V^ε(∂B_ρ)`, where the degree bound eq:degree-bound holds), and its use (Step 3 of the proof of
Proposition 7.1, lines 3236-3244: paths from the support of `u^ε_t`) needs exactly the points of the support. The
points of `cl(Λ^ε_t) \ Λ^ε_t` are not covered: there the printed proof (lines 3074-3076) only gives
`u^ε_t(a₁) > 0`, not the increment `log(ε⁻¹)⁻²`. -/
def CrudeUpperBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ t : ℝ, 0 < t →
  PolyHighProb S.P fun ε => {ω | ∀ a ∈ matedDiscreteCluster ε (S.η ω) ρ t \ {0}, ∃ p : List ℤ,
    IsVPathIn (S.mult ε ω) (matedDiscreteCluster ε (S.η ω) ρ t) p a 0 ∧
    p.IsChain fun c d => stoppedOdometer ε (S.η ω) ρ t c + (Real.log ε⁻¹)⁻¹ ^ 2 ≤ stoppedOdometer ε (S.η ω) ρ t d}

end MatedCRT
