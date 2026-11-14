import MatedCRT.FirstPass.Derived.MatingTriplePointsCone
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Size of the set of triple points of the mating relation

For a `γ`-correlated planar Brownian motion `Z = (L, R)` on `ℝ` with `0 < γ < 2`, the triple points of the mating
relation `matingTriplePoints ω` (Duplantier-Miller-Sheffield (2014), Section 8.1) form almost surely a countable set,
or a set of Hausdorff dimension at most some `d < 1/2`.

* The triple points that are not cone triple points form a countable set as soon as the times of mixed type do
  (`countable_matingTriplePoints_diff_coneTriplePoints`).
* For `γ ≤ √2` (cone opening angle `θ = πγ²/4 ≤ π/2`), the forward and backward `π/2`-cone times are countable, hence
  so are the cone triple points (`countable_coneTriplePoints`).
* For `√2 < γ < 2` the cone triple points have Hausdorff dimension at most `1 - 2/γ²` (Gwynne-Holden-Miller,
  `GHMConeDimInput`), and `1 - 2/γ² < 1/2` because `γ² < 4`.

Main statements.

* `GHMConeDimInput`: literature input, the Hausdorff dimension of the cone triple points (GHM Theorem 6.3, `m = 3`).
* `hZ3_of_inputs`: the almost sure dichotomy for the triple points, from `GHMConeDimInput`, the countability of the
  times of mixed type, and the countability of the cone times for `γ ≤ √2`.
-/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT (lrCoord Path2 IsCorrelatedBM2)
open scoped ENNReal

namespace MatedCRT

/-- **Literature input: Hausdorff dimension of the cone triple points** (Gwynne-Holden-Miller, *An almost sure KPZ
relation for SLE and Brownian motion*, arXiv 1512.01223, Theorem 6.3, p. 39, with `m = 3` and `κ' = 16/γ² ∈ (4, 8)`).
For `√2 < γ < 2` and a `γ`-correlated planar Brownian motion `Z = (L, R)`, almost surely the cone times of `Z`
together with their direct `L`- and `R`-partners (`coneTriplePoints`) form a set of Hausdorff dimension at most
`1/2 - (m - 2)(κ'/8 - 1/2) = 1 - 2/γ²`.

GHM state the dimension of the set `𝒯̃(3)` of times and of the set `𝕋̃(3)` of vectors of type I and II. They are
applied to `Z` and to its time reversal `t ↦ Z(-t)`, which has the same law: a forward cone time `s` gives the vector
`(v(s), s)` of type II for `Z` and `(-u(s), -s)` of type I for the reversal, a backward cone time `s` gives
`(u^R(s), s)` of type I for `Z` and `(-v^R(s), -s)` of type II for the reversal, so the apex and both partners are
covered; coordinate projections are Lipschitz, and countable sets do not change the Hausdorff dimension. GHM's `u(t)` is
read with the `L`-infimum over `[t, s]` (typo in print, where the infimum is written over `[s, t]`). GHM's `Z` has the
covariance of `IsCorrelatedBM2 γ` up to a constant factor, and both sets are invariant under this scaling. The
cone-time part of GHM uses no Liouville quantum gravity. -/
def GHMConeDimInput : Prop :=
  ∀ γ : ℝ, Real.sqrt 2 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
    ∀ᵐ ω ∂μ, dimH (coneTriplePoints ω) ≤ ENNReal.ofReal (1 - 2 / γ ^ 2)

/-- The exponent `1 - 2/γ²` of `GHMConeDimInput` is below `1/2` for `0 < γ < 2`. -/
theorem ofReal_one_sub_two_div_sq_lt_half {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ENNReal.ofReal (1 - 2 / γ ^ 2) < 1 / 2 := by
  have hpos : 0 < γ ^ 2 := by positivity
  have hsq : γ ^ 2 < 4 := by nlinarith
  have hhalf : (1 : ℝ) / 2 < 2 / γ ^ 2 := by
    rw [lt_div_iff₀ hpos]
    linarith
  have hlt : 1 - 2 / γ ^ 2 < (1 : ℝ) / 2 := by linarith
  calc ENNReal.ofReal (1 - 2 / γ ^ 2) < ENNReal.ofReal (1 / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hlt
    _ = 1 / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

/-- **Triple points of the mating relation.** Let `0 < γ < 2` and let `μ` be the law of a `γ`-correlated planar
Brownian motion `Z = (L, R)`. Assume that almost surely the times of mixed type of `Z` (a forward direct partner for one
coordinate and a backward direct partner for the other) form countable sets, that for `γ ≤ √2` the forward and backward
cone times of `Z` almost surely form countable sets, and the Gwynne-Holden-Miller bound `GHMConeDimInput` on the
Hausdorff dimension of the cone triple points for `√2 < γ < 2`. Then almost surely the triple points of the mating
relation of `Z` form a countable set, or a set of Hausdorff dimension at most some `d < 1/2` (`d = 1 - 2/γ²`). -/
theorem hZ3_of_inputs (hGHM : GHMConeDimInput)
    (hMix : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ᵐ ω ∂μ, (mixTimes (fun u => lrCoord 0 u ω) (fun u => lrCoord 1 u ω)).Countable ∧
        (mixTimes (fun u => lrCoord 1 u ω) (fun u => lrCoord 0 u ω)).Countable)
    (hCone : ∀ γ : ℝ, 0 < γ → γ ≤ Real.sqrt 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ᵐ ω ∂μ, (forwardConeTimes ω).Countable ∧ (backwardConeTimes ω).Countable) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ᵐ ω ∂μ, (matingTriplePoints ω).Countable ∨ ∃ d : ℝ≥0∞, dimH (matingTriplePoints ω) ≤ d ∧ d < 1 / 2 := by
  intro γ hγ0 hγ2 μ hμ
  have hrest : ∀ᵐ ω ∂μ, (matingTriplePoints ω \ coneTriplePoints ω).Countable := by
    filter_upwards [hMix γ hγ0 hγ2 μ hμ] with ω hω
    exact countable_matingTriplePoints_diff_coneTriplePoints ω hω.1 hω.2
  have hsub : ∀ ω : Path2,
      matingTriplePoints ω ⊆ coneTriplePoints ω ∪ (matingTriplePoints ω \ coneTriplePoints ω) := by
    intro ω x hx
    by_cases h : x ∈ coneTriplePoints ω
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  rcases le_or_gt γ (Real.sqrt 2) with hγ | hγ
  · filter_upwards [hrest, hCone γ hγ0 hγ μ hμ] with ω hω hC
    exact Or.inl (((countable_coneTriplePoints ω hC.1 hC.2).union hω).mono (hsub ω))
  · filter_upwards [hrest, hGHM γ hγ hγ2 μ hμ] with ω hω hD
    refine Or.inr ⟨ENNReal.ofReal (1 - 2 / γ ^ 2), ?_, ofReal_one_sub_two_div_sq_lt_half hγ0 hγ2⟩
    calc dimH (matingTriplePoints ω)
        ≤ dimH (coneTriplePoints ω ∪ (matingTriplePoints ω \ coneTriplePoints ω)) := dimH_mono (hsub ω)
      _ = dimH (coneTriplePoints ω) := by rw [dimH_union, hω.dimH_zero, max_zero]
      _ ≤ ENNReal.ofReal (1 - 2 / γ ^ 2) := hD

end MatedCRT
