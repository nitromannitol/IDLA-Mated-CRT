import HarmonicBalls.Defs.Notation
import HarmonicBalls.Defs.Brownian
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

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

/-- The *outer integral* `∫* f dP = inf {∫ g dP : g ≥ f, g measurable}` of a function `f : Ω → [0, ∞]` which need
not be measurable (the outer expectation of Hoffmann-Jørgensen; van der Vaart-Wellner, Section 1.2). It is `∫⁻ f dP`
when `f` is measurable, monotone and countably subadditive in `f`. (Mathlib's `∫⁻` of a non-measurable function is
the *lower* integral, which is only superadditive.) -/
noncomputable def outerLIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (g : Ω → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁻ ω, g ω ∂P

/-- The outer integral of the quenched probabilities of the sections of an event.
This auxiliary quantity is useful for bounds proved separately in each environment. -/
noncomputable def sectionwiseOuterProb {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (κ : Ω → Measure X) (E : Set (Ω × X)) : ℝ≥0∞ :=
  outerLIntegral P fun ω => κ ω (Prod.mk ω ⁻¹' E)

/-- Outer measure under the joint law determined by the measurable conditional law.
The zero measure totalizes the definition when the proposed conditional law is not measurable. -/
noncomputable def jointOuterProb {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (κ : Ω → Measure X) (E : Set (Ω × X)) : ℝ≥0∞ := by
  classical
  exact if h : Measurable κ then Measure.compProd P (⟨κ, h⟩ : ProbabilityTheory.Kernel Ω X) E else 0

/-- The *annealed outer probability* of an event `E ⊆ Ω × X` of the environment `ω` (law `P`) and of a random
object `x` whose conditional law given the environment is `κ ω` (the quenched law): the outer integral of the
quenched probability `ω ↦ κ ω (E_ω)` of the section `E_ω = {x | (ω, x) ∈ E}`.

This is the current convention in the Draft statements, pending the review-S (S5) change to the outer measure under
the joint law. As a function of `E` it is an
outer measure on `Ω × X` (countably subadditive, so union bounds apply), and it is `∫⁻ κ ω (E_ω) dP` whenever the
quenched probability is measurable. When `κ` is a measurable kernel, so that the joint law `P ⊗ κ` exists, it is
`(P ⊗ κ)(E)` for every measurable `E`, and at most the outer measure `(P ⊗ κ)*(E)` for every `E`. The map `ω ↦ κ ω` is
not assumed to be measurable (the environment does not make `ω ↦ 𝒢^ε` measurable), so the joint law itself is not
formed. For probabilities `κ ω`, if `κ ω (E_ω) ≤ θ` for `ω ∈ G` then this is at most `θ + P(Gᶜ)` (outer measure). -/
noncomputable def annealedOuterProb {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (κ : Ω → Measure X) (E : Set (Ω × X)) : ℝ≥0∞ :=
  outerLIntegral P fun ω => κ ω (Prod.mk ω ⁻¹' E)

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
