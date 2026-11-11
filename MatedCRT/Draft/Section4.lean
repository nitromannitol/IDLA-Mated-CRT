import MatedCRT.Defs.Setting
import MatedCRT.Defs.Sandpile

/-!
# Section 4: statements of Theorem 4.1, Proposition 4.2 and Lemmas 4.3-4.8 (lines 1535-1951)

Convergence of the divisible sandpile odometer. Conventions: see `MatedCRT/Draft/Section1.lean` and
`MatedCRT/Draft/Section3.lean`. `ρ ∈ (0, 1)` is fixed (line 1536) and universally quantified.

Objects, for the map `𝒢^ε` with edge multiplicity `m = S.mult ε ω` (Definition 1.1) and the cells of `η = S.η ω`:
* `w̃^ε_t` = `matedLeastSupersolution m ε η ρ t` (eq:discrete-least-supersolution), its rescaling
  `w̄^ε_t = rescale (S.mε ε) ε η w̃^ε_t`;
* `Λ^ε_t` = `matedDiscreteCluster m ε η ρ t` (eq:discrete-cluster);
* `q^ε_{B_ρ}` = `normExitTime m (ballInterior ε η ρ)`, `g^ε_{B_ρ}(0, ·)` = `greenKernel … 0`;
* `D_ε(t ε⁻¹)` = `sandpileCluster m (t / ε)`;
* `w̄^{B_ρ}_t` = `HarmonicBalls.leastSupersolution μ_h ρ 0 t` (eq:least-super-solution), `G_{B_ρ}` =
  `HarmonicBalls.greenFunction (ball 0 ρ)`;
* `T = clusterExitTime Λ ρ = sup {t > 0 : Λ_t ⊆ B_{ρ/3}}` (eq:cluster-stopping-time).
A deterministic sequence `ε_n → 0` is `εs : ℕ → ℝ` with `εs n > 0`, `εs n → 0`.
The constant of Theorem 4.1 and Lemma 4.8 is `c₀/6` with `c₀ = 2/m₀` (`MatedCRTEnv.c₀`), CORRECTION [C1]
(ESCALATIONS E-A3: the printed `m₀/6` is false).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The rescaled discrete least supersolution `w̄^ε_t` (eq:discrete-scaling applied to `w̃^ε_t`). -/
noncomputable def rescaledMatedLeastSupersolution {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ t ε : ℝ)
    (ω : Ω) : ℂ → ℝ :=
  rescale (S.mε ε) ε (S.η ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t)

/-- **Theorem 4.1** (theorem:convergence-divisible, line 1594). For each `t > 0`, on the event `{t < T}`, `w̄^ε_t`
converges uniformly on `B_ρ` as `ε → 0` to `(c₀/6) w̄^{B_ρ}_t` in probability: for each `δ > 0`,
`P[t < T, sup_{B_ρ} |w̄^ε_t - (c₀/6) w̄^{B_ρ}_t| > δ] → 0`. CORRECTION [C1]: `c₀ = 2/m₀` (`MatedCRTEnv.c₀`) in
place of the printed `m₀`. -/
def ConvergenceDivisibleStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ δ : ℝ, 0 < δ →
    Tendsto (fun ε => S.P {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
        δ < |rescaledMatedLeastSupersolution S ρ t ε ω x - S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|})
      (𝓝[>] 0) (𝓝 0)

/-- **Proposition 4.2** (prop:div-sandpile-lower-bound, line 1611). For each `δ ∈ (0, ρ)` and `t > 0`, on the event
`{t < T}`, except on an event of probability tending to `0` as `ε → 0`, `B⁻_δ(Λ_t) ⊆ D̄_ε(t ε⁻¹)`. -/
def DivSandpileLowerBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε =>
      {ω | innerNbhd δ (Λ ω t) ⊆ fillCells ε (S.η ω) (sandpileCluster (S.mult ε ω) (t / ε))}

/-- **Lemma 4.3** (lemma:discrete-basic-properties, line 1679). For all `t > 0` and `ε > 0`,
`max(-q^ε_{B_ρ}, -(t ε⁻¹) g^ε_{B_ρ}(0, ·)) ≤ w̃^ε_t ≤ 0` (on `V^ε(cl(B_ρ))`, the domain of `w̃^ε_t`) and
`Δ^ε w̃^ε_t ≤ (deg^ε)⁻¹` on `V^ε(B_ρ) \ V^ε(∂B_ρ)`. Stated almost surely (the map is then locally finite). -/
def DiscreteBasicPropertiesStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε →
    (∀ a ∈ cellVertices ε (S.η ω) (closedBall 0 ρ),
      max (-normExitTime (S.mult ε ω) (ballInterior ε (S.η ω) ρ) a) (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t a) ≤
        matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a ∧
          matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a ≤ 0) ∧
    ∀ a ∈ ballInterior ε (S.η ω) ρ,
      matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a ≤
        ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹

/-- **Lemma 4.4** (lemma:discrete-laplacian-bound, line 1697). For all `t > 0` and `ε > 0`, `Δ^ε w̃^ε_t = (deg^ε)⁻¹` on
`Λ^ε_t` and `0 ≤ Δ^ε w̃^ε_t ≤ (deg^ε)⁻¹` on `V^ε(B_ρ) \ V^ε(∂B_ρ)`. Moreover `Λ^ε_t` is connected (`IsVPreconnected`; `Λ^ε_t = ∅` when `t ε⁻¹ ≤ 1`), and if
`t ε⁻¹ > 1` then `0 ∈ Λ^ε_t`. Stated almost surely. -/
def DiscreteLaplacianBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε →
    (∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
      matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a =
        ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹) ∧
    (∀ a ∈ ballInterior ε (S.η ω) ρ,
      0 ≤ matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a ∧
      matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a ≤
        ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹) ∧
    IsVPreconnected (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) ∧
    (1 < t / ε → (0 : ℤ) ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)

/-- **Lemma 4.5** (lemma:discrete-conservation-of-mass, line 1705). For all `t > 0` and `ε > 0`, `|Λ^ε_t| ≤ t ε⁻¹`.
Moreover, if `Λ^ε_t ⊆ int(V^ε(B_ρ) \ V^ε(∂B_ρ))`, then
`∑_{a ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)} Δ^ε w̃^ε_t(a) deg^ε(a) = t ε⁻¹`. Stated almost surely; `|Λ^ε_t|` is the cardinality
(`Set.ncard`; `Λ^ε_t` is finite). -/
def DiscreteConservationOfMassStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε →
    (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).Finite ∧
    ((matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).ncard : ℝ) ≤ t / ε ∧
    (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆ vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) →
      ∑' a : ballInterior ε (S.η ω) ρ,
        matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a *
          (matedDeg (S.mult ε ω) a : ℝ) = t / ε)

/-- **Lemma 4.6** (lemma:subsequential-convergence, line 1720). Almost surely, for each `t > 0` and each deterministic
sequence `ε_n → 0`, there are a subsequence and a Hölder continuous `w̄*_t ∈ C(cl(B_ρ))` with `w̄^ε_t → w̄*_t`
uniformly on `cl(B_ρ)` along it; the subsequence is `σ(h, η)`-measurable. Formalized as the conjunction of
(i) one almost sure event on which, for all `t` and all sequences, a convergent subsequence exists, and (ii) for each
`t` and each sequence, a `σ(h, η)`-measurable choice of the subsequence which a.s. has this property. -/
def SubsequentialConvergenceStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  (∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t → ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → ℝ, ContinuousOn w (closedBall 0 ρ) ∧
      IsHolderContinuousOn w (closedBall 0 ρ) ∧
      TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εs (φ k)) ω) w atTop
        (closedBall 0 ρ)) ∧
  ∀ t : ℝ, 0 < t → ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧ ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧
      ∃ w : ℂ → ℝ, ContinuousOn w (closedBall 0 ρ) ∧ IsHolderContinuousOn w (closedBall 0 ρ) ∧
        TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εs (Φ ω k)) ω) w atTop
          (closedBall 0 ρ)

/-- **Lemma 4.7** (lemma:equibounded, line 1729). A.s., for each deterministic sequence `ε_n → 0` there are a
deterministic subsequence `𝓔` and a random constant `C` with `sup_{x ∈ B_ρ} |w̄^ε_t(x)| ≤ C` for all `ε ∈ 𝓔` and all
`t > 0`. The subsequence being deterministic, it is chosen before the almost sure event. -/
def EquiboundedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ n : ℕ, ∀ x ∈ ball (0 : ℂ) ρ,
      |rescaledMatedLeastSupersolution S ρ t (εs (φ n)) ω x| ≤ C

/-- **Lemma 4.8** (lemma:subsequential-properties, line 1761). A.s., for each deterministic sequence `ε_n → 0` there is
a deterministic subsequence such that a subsequential limit `w̄*_t` of `w̄^ε_t` along it (as in Lemma 4.6: uniform on
`cl(B_ρ)`) satisfies
1. `0 ≥ w̄*_t ≥ -t (c₀/6) G_{B_ρ}(0, ·)` on `cl(B_ρ)`;
2. `Δw̄*_t ≥ 0` on `B_ρ`;
3. `Δw̄*_t ≤ (c₀/6) μ_h` on `B_ρ`, and `Δw̄*_t = (c₀/6) μ_h` on `{x ∈ B_ρ : w̄*_t(x) > -t (c₀/6) G_{B_ρ}(0, x)}` (the
   pole `0`, where `G = +∞`, included).
Read for every `t > 0` and every subsequential limit along the subsequence. CORRECTION [C1]: `c₀ = 2/m₀`
(`MatedCRTEnv.c₀`) in place of the printed `m₀`. Review-S (S3): the lower bound of item 1 is stated off the pole,
for `x ≠ 0`; at the pole the printed bound is `-∞` (no constraint), while HB's `greenFunction` has the junk value
`G(0, 0) = 0`, with which item 1 would force `w̄*_t(0) = 0` and make the lemma false. -/
def SubsequentialPropertiesStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t → ∀ w : ℂ → ℝ,
      (ContinuousOn w (closedBall 0 ρ) ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        TendstoUniformlyOn (fun k => rescaledMatedLeastSupersolution S ρ t (εs (φ (ψ k))) ω) w atTop
          (closedBall 0 ρ)) →
      (∀ x ∈ closedBall (0 : ℂ) ρ, w x ≤ 0 ∧ (x ≠ 0 → -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x ≤ w x)) ∧
      LaplacianGE w 0 (ball 0 ρ) ∧
      LaplacianLE w (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) (ball 0 ρ) ∧
      HasLaplacian w (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) 0
        {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x < w x}

/-! ## Corrected statements of Lemmas 4.4 and 4.5 (ESCALATIONS E-c1-1) -/

/-- **Lemma 4.4**, corrected: the claim `0 ∈ Λ^ε_t` needs `0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)` (the origin of Appendix A). -/
def DiscreteLaplacianBoundCorrectedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε →
    (∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
      matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a = ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹) ∧
    (∀ a ∈ ballInterior ε (S.η ω) ρ,
      0 ≤ matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a ∧
      matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a ≤ ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹) ∧
    IsVPreconnected (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) ∧
    (1 < t / ε → (0 : ℤ) ∈ ballInterior ε (S.η ω) ρ → (0 : ℤ) ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)

/-- **Lemma 4.5**, corrected: the mass identity needs `0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`. -/
def DiscreteConservationOfMassCorrectedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε →
    (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).Finite ∧
    ((matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).ncard : ℝ) ≤ t / ε ∧
    ((0 : ℤ) ∈ ballInterior ε (S.η ω) ρ →
      matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t ⊆ vInterior (S.mult ε ω) (ballInterior ε (S.η ω) ρ) →
      ∑' a : ballInterior ε (S.η ω) ρ,
        matedLaplacian (S.mult ε ω) (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) a * (matedDeg (S.mult ε ω) a : ℝ) = t / ε)

end MatedCRT
