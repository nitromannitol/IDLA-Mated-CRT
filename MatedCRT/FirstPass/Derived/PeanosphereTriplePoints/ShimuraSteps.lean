import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.PathProperties
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The steps of Shimura's theorem for the correlated Brownian pair

For `0 < γ < 2` and the law `μ` of the `γ`-correlated two-sided Brownian pair `(L, R)` (`IsCorrelatedBM2 γ μ`),
almost surely no time is a minimum of one coordinate on a left neighbourhood and of the other on a right
neighbourhood (`NoOppositeSideMin`, both orders). This is Shimura's theorem on meandering points (M. Shimura,
*Meandering points of two-dimensional Brownian motion*, Kodai Math. J. 11 (1988), 169–176, Theorem 1), applied to
the projections `L`, `R` of a planar Brownian motion onto two unit vectors at angle `π - πγ²/4`.

The printed proof omits the obtuse case of its Lemma 2 and refers to Dvoretzky–Erdős–Kakutani (1961) for the
second-moment steps; the complete argument is followed here. This file states its steps as named propositions and proves the theorem from them
(`ae_noOppositeSideMin_of_shimuraSteps`):

* `ShimuraLocalization γ`: the theorem follows from the nullity of the unit event `UnitOppositeSideMin` (a time of
  `[0, 1]` which is a minimum of `L` on `[t - 2, t]` and of `R` on `[t, t + 2]`) for every law of the pair, by
  translation, scaling and time reversal.
* `ShimuraCellBounds γ`: the cells `[(k - 1)/n, k/n]` carry Shimura's event `A^n_k` (`cellEvent n k`) with probability
  at most `C/n` (Shimura, Lemma 1, p. 171; the summation uses only the upper bound).
* `ShimuraOccupancy γ`: given the first occupied cell `k` (`firstCellEvent n k`), the cell `k + j` is occupied with
  conditional probability at least `c/(j - 1)` (Shimura (4.2)–(4.7), pp. 174–176).
* `ShimuraSummation γ`: with the upper bound for a cell only, these bounds give
  `P(⋃_{k ≤ n} A^n_k) ≤ 2/n + 2C/(c Σ_{1 + 6 log n < j ≤ n} 1/(j - 1)) → 0`, hence the nullity of the unit event
  (Shimura §2 (2.1), §4); this simplifies the argument that bounds `P(S_{2n} > 0)` through `E[S_{2n} | S_{2n} > 0]`.

The steps `ShimuraCellBounds` and `ShimuraOccupancy` rest on the following statements, also named here:
`ReflectionBarrier` (the survival bound `P(min_{[0,T]} B > -a) ≤ a √(2/(πT))`, DEK (4.2)),
`KilledBarrierPositive` (the killed interval kernel limit, Karatzas–Shreve §2.8.C),
`PlanarTubePositive` (planar Brownian motion follows a straight path within any tube with positive probability) and `ShimuraLemmaTwo` (Shimura, Lemma 2, (3.5), p. 172, for every angle).
-/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2)
open scoped NNReal ENNReal

namespace MatedCRT.PeanosphereTriplePoints

/-! ### Events -/

/-- A time of `[0, 1]` that is a minimum of `X` on `[t - 2, t]` and of `Y` on `[t, t + 2]`. -/
def UnitOppositeSideMin (X Y : ℝ → ℝ) : Prop :=
  ∃ t ∈ Icc (0 : ℝ) 1, (∀ s ∈ Icc (t - 2) t, X t ≤ X s) ∧ ∀ s ∈ Icc t (t + 2), Y t ≤ Y s

/-- Shimura's event `A^n_k` for the cell `[(k - 1)/n, k/n]`: the minimum of `X` on the cell is at most its minimum on
the window `[k/n - 2, (k - 1)/n]` to the left, and the minimum of `Y` on the cell is at most its minimum on the window
`[k/n, (k - 1)/n + 2]` to the right. -/
def ShimuraCell (n k : ℕ) (X Y : ℝ → ℝ) : Prop :=
  (∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
      ∀ u ∈ Icc ((k : ℝ) / n - 2) (((k : ℝ) - 1) / n), X s ≤ X u) ∧
    ∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
      ∀ u ∈ Icc ((k : ℝ) / n) (((k : ℝ) - 1) / n + 2), Y s ≤ Y u

/-- The pairs whose cell `k` at mesh `1/n` carries Shimura's event, for `(X, Y) = (L, R)`. -/
def cellEvent (n k : ℕ) : Set Path2 :=
  {p | ShimuraCell n k (fun t => (p t).1) (fun t => (p t).2)}

/-- The pairs whose first cell carrying Shimura's event is `k` (Shimura's `B^n_k`). -/
def firstCellEvent (n k : ℕ) : Set Path2 :=
  cellEvent n k \ ⋃ i ∈ Finset.Ico 1 k, cellEvent n i

/-! ### The steps -/

/-- **Localization**: if the unit event is null for every law of the `γ`-correlated pair, then
almost surely no time is a minimum of one coordinate on a left neighbourhood and of the other on a right
neighbourhood. Translation and time reversal (`isCorrelatedBM2_map_recenterPath`), Brownian scaling
(`isCorrelatedBM2_map_unitRescalePath`) preserve the law class; the second order comes from the first by time
reversal (`recenterPath 0 (-1)`). -/
def ShimuraLocalization (γ : ℝ) : Prop :=
  (∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      μ {p | UnitOppositeSideMin (fun t => (p t).1) (fun t => (p t).2)} = 0) →
    ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ᵐ p ∂μ, NoOppositeSideMin (fun t => (p t).1) (fun t => (p t).2) ∧
        NoOppositeSideMin (fun t => (p t).2) (fun t => (p t).1)

/-- **The probability of a cell** (Shimura, Lemma 1, p. 171, and (4.1), p. 174): `P(A^n_k) ≤ C/n` for
every cell of `[0, 2]`, for `n ≥ N`. -/
def ShimuraCellBounds (γ : ℝ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ n : ℕ, N ≤ n →
    ∀ k : ℕ, 1 ≤ k → k ≤ 2 * n → μ (cellEvent n k) ≤ ENNReal.ofReal (C / n)

/-- **The occupation of a later cell** (Shimura (4.2)–(4.7), pp. 174–176): if the first
occupied cell is `k ≤ n`, of probability at least `2/n²`, then the cell `k + j`, for `1 + 6 log n < j` and
`k + j ≤ 2n`, is occupied with conditional probability at least `c/(j - 1)`. -/
def ShimuraOccupancy (γ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ n : ℕ, N ≤ n →
    ∀ k j : ℕ, 1 ≤ k → k ≤ n → ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k) →
      1 + 6 * Real.log n < j → k + j ≤ 2 * n →
        ENNReal.ofReal (c / ((j : ℝ) - 1)) * μ (firstCellEvent n k) ≤
          μ (firstCellEvent n k ∩ cellEvent n (k + j))

/-- **Summation** (Shimura (2.1) and §4): the cell bounds and the occupation bound give
`P(⋃_{k ≤ n} A^n_k) ≤ 2/n + 2C/(c Σ_{1 + 6 log n < j ≤ n} 1/(j - 1)) → 0` (the first occupied cells of probability
below `2/n²` contribute at most `2/n`; the others satisfy `P(B_k) c Σ_j 1/(j - 1) ≤ E[1_{B_k} S_{2n}]`, which sums to at
most `E S_{2n} ≤ 2C`); since a witness of the unit event occupies one of the first `n` cells at every mesh `1/n`, the
unit event is null. -/
def ShimuraSummation (γ : ℝ) : Prop :=
  ShimuraCellBounds γ → ShimuraOccupancy γ → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
    μ {p | UnitOppositeSideMin (fun t => (p t).1) (fun t => (p t).2)} = 0

/-! ### The statements behind the cell and occupation bounds -/

/-- **The survival bound of real Brownian motion** (Dvoretzky–Erdős–Kakutani (4.2), p. 106):
`P(min_{s ≤ T} (B s - B 0) > -a) ≤ a √(2/(πT))`, from the reflection principle
`P(min_{s ≤ T} (B s - B 0) ≤ -a) ≥ 2 P(B T - B 0 < -a)`. -/
def ReflectionBarrier : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ),
    ProbabilityTheory.IsBrownianReal B P → ∀ T : ℝ≥0, 0 < T → ∀ a : ℝ, 0 ≤ a →
      P {ω | ∀ s ≤ T, -a < B s ω - B 0 ω} ≤ ENNReal.ofReal (a * Real.sqrt (2 / (Real.pi * T)))

/-- **The killed interval kernel near the lower barrier** (Karatzas–Shreve, *Brownian Motion and
Stochastic Calculus*, §2.8.C, Proposition 8.10): for `0 < y₁ < y₂ < H`, real Brownian motion stays in `(-e, H)` up
to time `T` and ends in `(y₁, y₂)` with probability at least `c e`, for `0 < e ≤ 1`. -/
def KilledBarrierPositive : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ),
    ProbabilityTheory.IsBrownianReal B P → ∀ (T : ℝ≥0) (H y₁ y₂ : ℝ), 0 < T → 0 < y₁ → y₁ < y₂ → y₂ < H →
      ∃ c : ℝ, 0 < c ∧ ∀ e : ℝ, 0 < e → e ≤ 1 →
        ENNReal.ofReal (c * e) ≤
          P {ω | (∀ s ≤ T, -e < B s ω - B 0 ω ∧ B s ω - B 0 ω < H) ∧ B T ω - B 0 ω ∈ Ioo y₁ y₂}

/-- **Tube positivity**: planar Brownian motion, given as the uncorrelated pair (`γ = √2`, independent
standard coordinates), stays within `ε` of the straight path from `0` to `w` up to time `T` with positive
probability. -/
def PlanarTubePositive : Prop :=
  ∀ μ : Measure Path2, IsCorrelatedBM2 (Real.sqrt 2) μ → ∀ (T : ℝ) (w : ℝ × ℝ) (ε : ℝ), 0 < T → 0 < ε →
    0 < μ {p | ∀ s ∈ Icc (0 : ℝ) T, dist (p s - p 0) ((s / T) • w) < ε}

/-- **Shimura's Lemma 2 for every angle** ((3.5), p. 172, proved here also for `π/2 < θ ≤ π`):
`G(Δ, δ) ≥ c Δ δ` for `0 < Δ, δ ≤ 1`, where `G(Δ, δ)` is the probability that on `[0, 1]` the coordinate `R` stays
above `-Δ` and ends above `1`, while `L` stays above its final value minus `δ` and ends below `-1`. -/
def ShimuraLemmaTwo (γ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ Δ δ : ℝ, 0 < Δ → Δ ≤ 1 → 0 < δ → δ ≤ 1 →
    ENNReal.ofReal (c * Δ * δ) ≤
      μ {p | (∀ s ∈ Icc (0 : ℝ) 1, -Δ ≤ (p s).2 - (p 0).2) ∧ 1 ≤ (p 1).2 - (p 0).2 ∧
        (∀ s ∈ Icc (0 : ℝ) 1, (p 1).1 - δ ≤ (p s).1) ∧ (p 1).1 - (p 0).1 ≤ -1}

/-! ### Shimura's theorem from the steps -/

/-- **Shimura's theorem for the correlated pair, from its steps**: almost surely no time is a minimum of one
coordinate on a left neighbourhood and of the other on a right neighbourhood, in both orders. -/
theorem ae_noOppositeSideMin_of_shimuraSteps {γ : ℝ} (hloc : ShimuraLocalization γ)
    (hsum : ShimuraSummation γ) (hcell : ShimuraCellBounds γ) (hocc : ShimuraOccupancy γ)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ p ∂μ, NoOppositeSideMin (fun t => (p t).1) (fun t => (p t).2) ∧
      NoOppositeSideMin (fun t => (p t).2) (fun t => (p t).1) :=
  hloc (fun ν hν => hsum hcell hocc ν hν) μ hμ

end MatedCRT.PeanosphereTriplePoints
