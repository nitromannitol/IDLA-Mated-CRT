import HarmonicBalls.Defs.Notation
import HarmonicBalls.Defs.Brownian
import Mathlib.Topology.MetricSpace.Holder

/-!
# Notation and conventions (Section 1.5, lines 370-391; eq:outer-inner-neighborhoods, lines 238-243)

Euclidean neighbourhoods of sets in `ℂ`, the probabilistic phrases of the paper ("with probability tending to 1",
"on the event `F`, except on an event of probability tending to `0`", "in probability"), medians of laws on
`[0, ∞]`, and the local uniform distance between paths `[0, ∞) → ℂ` (Theorem 2.11).

Reused from the harmonic-balls formalization (`HarmonicBalls/Defs/Notation.lean`): the annulus
`𝔸_{r₁,r₂}(z)` (`HarmonicBalls.annulus`, eq:annulus, line 383), the LQG constant `Q = 2/γ + γ/2`
(`HarmonicBalls.lqgQ`, eq:Q, line 421) and "with polynomially high probability" (`HarmonicBalls.PolyHighProb`,
line 387). The ball `B_r(D) = {x : dist(x, D) < r}` (line 380) is Mathlib's `Metric.thickening r D`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

/-- The `δ`-outer neighbourhood `B⁺_δ(X) = {x ∈ ℂ : dist(x, X) ≤ δ}` (eq:outer-inner-neighborhoods, line 240). The
distance to a set is `Metric.infEDist` (it is `+∞` to the empty set, as is the paper's `inf ∅`). -/
def outerNbhd (δ : ℝ) (X : Set ℂ) : Set ℂ :=
  {x | Metric.infEDist x X ≤ ENNReal.ofReal δ}

/-- The `δ`-inner neighbourhood `B⁻_δ(X) = {y ∈ X : dist(y, Xᶜ) ≥ δ}` (eq:outer-inner-neighborhoods, line 241). -/
def innerNbhd (δ : ℝ) (X : Set ℂ) : Set ℂ :=
  {y ∈ X | ENNReal.ofReal δ ≤ Metric.infEDist y Xᶜ}

/-- An event depending on `ε > 0` holds *with probability tending to `1` as `ε → 0`*: the (outer) probability of
its complement tends to `0` as `ε → 0⁺`. -/
def ProbTendsToOne {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → Set Ω) : Prop :=
  Tendsto (fun ε => P (E ε)ᶜ) (𝓝[>] 0) (𝓝 0)

/-- *On the event `F`, `E ε` holds except on an event of probability tending to `0` as `ε → 0`* (e.g. Proposition
4.2, line 1612): `P[F ∩ (E ε)ᶜ] → 0` as `ε → 0⁺`. -/
def TendsToOneOn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω) (E : ℝ → Set Ω) : Prop :=
  Tendsto (fun ε => P (F ∩ (E ε)ᶜ)) (𝓝[>] 0) (𝓝 0)

/-- Real random variables `X ε` *converge in probability* to `Y` as `ε → 0`: for each `δ > 0`,
`P[|X ε - Y| > δ] → 0` as `ε → 0⁺`. -/
def TendstoInProbability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ → Ω → ℝ) (Y : Ω → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → Tendsto (fun ε => P {ω | δ < |X ε ω - Y ω|}) (𝓝[>] 0) (𝓝 0)

/-- Functions `u ε ω : ℂ → ℝ` *converge uniformly on `K`, in probability*, to `v ω` as `ε → 0` (e.g. Theorem 4.1,
line 1595): for each `δ > 0`, `P[sup_{x ∈ K} |u ε ω x - v ω x| > δ] → 0` as `ε → 0⁺`. The supremum is written as
"there is `x ∈ K` with `|u ε ω x - v ω x| > δ`". -/
def TendstoUniformlyOnInProbability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (u : ℝ → Ω → ℂ → ℝ)
    (v : Ω → ℂ → ℝ) (K : Set ℂ) : Prop :=
  ∀ δ : ℝ, 0 < δ → Tendsto (fun ε => P {ω | ∃ x ∈ K, δ < |u ε ω x - v ω x|}) (𝓝[>] 0) (𝓝 0)

/-- The (lower) *median* of a `[0, ∞]`-valued random variable `τ` with distribution function
`cdf m = P[τ ≤ m]`: `inf {m ≥ 0 : P[τ ≤ m] ≥ 1/2}` (eq:mo, line 727; eq:meps, line 731). It is the smallest median
when `τ` has a probability law. -/
noncomputable def medianOf (cdf : ℝ → ℝ≥0∞) : ℝ :=
  sInf {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ cdf m}

/-- The *local uniform distance* between two paths `f, g : [0, ∞) → ℂ`,
`d(f, g) = ∑_{k ≥ 1} 2^{-k} min(1, sup_{t ∈ [0, k]} |f t - g t|)`, which metrizes local uniform convergence on
continuous paths (the "local uniform metric on curves `[0, ∞) → ℂ`" of Theorem 2.11, line 738). -/
noncomputable def localUniformDist (f g : ℝ≥0 → ℂ) : ℝ :=
  ∑' k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) *
    (min 1 (⨆ t : Icc (0 : ℝ≥0) (k + 1 : ℕ), ENNReal.ofReal ‖f t - g t‖)).toReal

/-- A *bounded Lipschitz functional* of paths for the local uniform distance: `|F| ≤ 1` and
`|F f - F g| ≤ L d(f, g)`. Convergence of laws of continuous paths in the Prokhorov topology induced by the local
uniform metric is equivalent to convergence of the integrals of every such functional (Portmanteau theorem;
Dudley, Real Analysis and Probability, Theorem 11.3.3). -/
def IsBoundedLipschitzPathFunctional (F : (ℝ≥0 → ℂ) → ℝ) : Prop :=
  (∀ f, |F f| ≤ 1) ∧ ∃ L : ℝ, ∀ f g, |F f - F g| ≤ L * localUniformDist f g

/-- `f` is *Hölder continuous* on `s`: `|f x - f y| ≤ C |x - y|^χ` on `s` for some `C ≥ 0` and exponent `χ ∈ (0, 1]`
(Mathlib's `HolderOnWith`). -/
def IsHolderContinuousOn (f : ℂ → ℝ) (s : Set ℂ) : Prop :=
  ∃ C χ : ℝ≥0, 0 < χ ∧ χ ≤ 1 ∧ HolderOnWith C χ f s

end MatedCRT
