import MatedCRT.FirstPass.Derived.BlockExitWalkAvoidChain

/-!
# Both walk-side block-exit bounds at prescribed tolerances

Freeze the block-exit chains off the open grid rectangle `R = (a₁ s, a₂ s) × (c₁ s, c₂ s)`. For a
prescribed radius `δ₀ > 0` and error `κ > 0` there is a number of blocks `N₀` such that for every
`N ≥ N₀` and every sufficiently small one-step tolerance `δ`, every walk started at a vertex whose
embedded position lies in `R`, and satisfying the one-step closeness `hclose` at tolerance `δ`, has

* the law of its first `N + 1` block-exit positions `(δ₀, κ)`-close, in the one-sided
  Lévy-Prokhorov sense, to the law of the first `N + 1` block-exit positions of planar Brownian
  motion started at the embedded start, and
* probability at most `κ` that its first `N` block-exit positions all stay in `R`.

The number `N₀` depends only on `s`, the rectangle and `κ`; the threshold for `δ` depends only on
`s`, `δ₀`, `κ` and `N`. Neither depends on the walk or on its starting vertex.

## Main results

* `prokhorovLE_mono`: monotonicity of the one-sided Lévy-Prokhorov relation in the radius and in
  the error.
* `norm_sub_le_of_mem_gridRectOpen`: two points of `R` are at distance at most
  `(|a₂ - a₁| + |c₂ - c₁|) s`.
* `exists_blockExit_frozen_walk_bounds`: the two bounds for a measurable grid-line stable frozen
  set whose complement is bounded;
* `exists_blockExit_gridRect_walk_bounds`: the two bounds for the grid rectangle.
-/

set_option autoImplicit false

open MeasureTheory Set Metric MarkovProcess Filter ProbabilityTheory
open scoped ENNReal NNReal Topology
open HarmonicBalls HarmonicBalls.Section6 LatticeProb LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

/-- The one-sided Lévy-Prokhorov relation is monotone in the radius and in the error. -/
theorem prokhorovLE_mono {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ ν : Measure E} {r r' e e' : ℝ} (h : ProkhorovLE μ ν r e)
    (hr : r ≤ r') (he : e ≤ e') : ProkhorovLE μ ν r' e' := fun A hA =>
  (h A hA).trans (add_le_add (measure_mono (thickening_mono hr A)) (ENNReal.ofReal_le_ofReal he))

/-- Two points of the open grid rectangle `(a₁ s, a₂ s) × (c₁ s, c₂ s)` are at distance at most
`(|a₂ - a₁| + |c₂ - c₁|) s`. -/
theorem norm_sub_le_of_mem_gridRectOpen {s : ℝ} (hs : 0 < s) {a₁ a₂ c₁ c₂ : ℤ} {y z : ℂ}
    (hy : y ∈ gridRectOpen s a₁ a₂ c₁ c₂) (hz : z ∈ gridRectOpen s a₁ a₂ c₁ c₂) :
    ‖y - z‖ ≤ (|(a₂ : ℝ) - a₁| + |(c₂ : ℝ) - c₁|) * s := by
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  have ha := mul_le_mul_of_nonneg_right (le_abs_self ((a₂ : ℝ) - a₁)) hs.le
  have hc := mul_le_mul_of_nonneg_right (le_abs_self ((c₂ : ℝ) - c₁)) hs.le
  have hre : |(y - z).re| ≤ |(a₂ : ℝ) - a₁| * s := by
    rw [Complex.sub_re, abs_le]
    constructor <;> linarith
  have him : |(y - z).im| ≤ |(c₂ : ℝ) - c₁| * s := by
    rw [Complex.sub_im, abs_le]
    constructor <;> linarith
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by rw [add_mul]; exact add_le_add hre him)

/-- **Both walk-side block-exit bounds at prescribed tolerances, frozen-set form.** Freeze the
block-exit chains on a measurable grid-line stable set `F` whose complement has diameter at most
`D`, and fix `δ₀ > 0`, `κ > 0`. There is `N₀ > 0` such that for every `N ≥ N₀` there is `δ₁ > 0`
with the following property. For every `0 < δ ≤ δ₁`, every walk (locally finite multiplicities `m`
with consecutive vertices adjacent, embedding `vertexPoint ε η`, speed `c > 0`) started at a vertex
`x₀` whose embedded position is off `F`, and every `0 ≤ θ ≤ s / 2` such that the edges meeting the
complement of `F` have length at most `θ` and the one-step closeness `hclose` holds at tolerance `δ`
against `frozenBlockExitKernel s hF` from the vertices within `θ` of points off `F`, satisfies
* the law of its first `N + 1` block-exit positions is within `(δ₀, κ)` of the law of the first
  `N + 1` block-exit positions of planar Brownian motion started at `vertexPoint ε η x₀`, in the
  one-sided Lévy-Prokhorov sense;
* the probability that its first `N` block-exit positions all avoid `F` is at most `κ`.
The numbers `N₀` and `δ₁` do not depend on `θ`; `N₀` depends only on `s`, `D` and `κ`. -/
theorem exists_blockExit_frozen_walk_bounds {s : ℝ} (hs : 0 < s) {F : Set ℂ}
    (hF : MeasurableSet F) (hFs : GridLineStable s F) {D : ℝ} (hD0 : 0 ≤ D)
    (hFD : ∀ y ∉ F, ∀ z ∉ F, ‖y - z‖ ≤ D) {δ₀ κ : ℝ} (hδ₀ : 0 < δ₀) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∀ (m : ℤ → ℤ → ℕ), IsLocallyFiniteMult m → (∀ k : ℤ, m k (k + 1) ≠ 0) →
      ∀ (ε : ℝ), 0 < ε → ∀ (η : ℝ → ℂ), Continuous η → Tendsto η (cocompact ℝ) (cocompact ℂ) →
      ∀ (c : ℝ) (hc : 0 < c) (x₀ : ℤ), vertexPoint ε η x₀ ∉ F →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ s / 2 →
      (∀ b b' : ℤ, m b b' ≠ 0 →
        (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'), z ∉ F) →
        dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ θ) →
      (∀ y ∉ F, ∀ u : ℤ, dist (vertexPoint ε η u) y ≤ θ →
        ProkhorovLE (walkNextBlockExitKernel m (vertexPoint ε η) hc.le s F (y, u))
          (frozenBlockExitKernel s hF y) δ δ) →
      ProkhorovLE
        ((srwLaw m x₀).map (fun x => blockExitPositions s F N
          (interpPathCM (vertexPoint ε η) hc.le x)))
        ((planarBrownianMotion (vertexPoint ε η x₀)).map (blockExitPositions s F N)) δ₀ κ ∧
      srwLaw m x₀ {x | ∀ n < N,
          interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x)) ∉ F} ≤
        ENNReal.ofReal κ := by
  obtain ⟨C, hC⟩ :=
    srwLaw_blockExit_avoid_frozen_le_of_hclose_frozen (ζ := 1 / 2) (by norm_num) (by norm_num) 1
  -- the radius `a` and the scale `r`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = D + 4 * s + 1 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ,
      r = min (1 / 2) (min (κ / (2 * (|C| + 1))) (s / (8 * a))) := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr]
    exact lt_min (by norm_num) (lt_min (by positivity) (div_pos hs (by linarith)))
  have hr1 : r < 1 := by rw [hr]; exact (min_le_left _ _).trans_lt (by norm_num)
  have hrC : C * r ^ 1 ≤ κ / 2 := by
    rw [pow_one]
    have hr2 : r ≤ κ / (2 * (|C| + 1)) := by
      rw [hr]; exact (min_le_right _ _).trans (min_le_left _ _)
    have h' : r * (2 * (|C| + 1)) ≤ κ := (le_div_iff₀ (by positivity)).1 hr2
    have h'' : C * r ≤ |C| * r := mul_le_mul_of_nonneg_right (le_abs_self C) hr0.le
    linarith
  have hra : r * (8 * a) ≤ s := by
    have hr3 : r ≤ s / (8 * a) := by
      rw [hr]; exact (min_le_right _ _).trans (min_le_right _ _)
    exact (le_div_iff₀ (by linarith)).1 hr3
  have hN₀ : 0 < ⌊r ^ (-(2 + 1 / 2 : ℝ))⌋₊ :=
    Nat.floor_pos.2 (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1.le (by norm_num))
  refine ⟨⌊r ^ (-(2 + 1 / 2 : ℝ))⌋₊, hN₀, fun N hN => ?_⟩
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hE : 0 < (N : ℝ) + 60 * (N : ℝ) ^ 3 / s + 1 := by
    have := div_nonneg (by positivity : (0 : ℝ) ≤ 60 * (N : ℝ) ^ 3) hs.le
    linarith
  refine ⟨min (δ₀ / (N + 1)) (min (s / (8 * (N + 1)))
      (min (1 / (2 * (N + 1))) (κ / (2 * ((N : ℝ) + 60 * (N : ℝ) ^ 3 / s + 1))))),
    lt_min (div_pos hδ₀ hN1) (lt_min (div_pos hs (by positivity))
      (lt_min (by positivity) (div_pos hκ (by positivity)))),
    fun δ hδ hδ₁ m hlf hcons ε hε η hη hp c hc x₀ hz θ hθ hθs hM hclose => ?_⟩
  have h1 : ((N : ℝ) + 1) * δ ≤ δ₀ := by
    rw [mul_comm]; exact (le_div_iff₀ hN1).1 (hδ₁.trans (min_le_left _ _))
  have h2 : ((N : ℝ) + 1) * δ ≤ s / 8 := by
    have := (le_div_iff₀ (by positivity)).1
      (hδ₁.trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have h3 : ((N : ℝ) + 1) * δ ≤ 1 / 2 := by
    have := (le_div_iff₀ (by positivity)).1
      (hδ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    linarith
  have h4 : (N : ℝ) * δ + 60 * (N : ℝ) ^ 3 * δ / s ≤ κ / 2 := by
    have := (le_div_iff₀ (by positivity)).1
      (hδ₁.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have heq : (N : ℝ) * δ + 60 * (N : ℝ) ^ 3 * δ / s + δ =
        δ * ((N : ℝ) + 60 * (N : ℝ) ^ 3 / s + 1) := by ring
    linarith
  have hNpos : 0 < N := hN₀.trans_le hN
  refine ⟨prokhorovLE_mono (prokhorovLE_srwLaw_blockExitPositions_of_hclose_frozen hlf hcons hε hη
    hp hc x₀ hs hF hFs hz hθ hθs hM hδ hclose hNpos (by linarith)) h1 (by linarith), ?_⟩
  -- the avoidance bound at `N₀ = ⌊r ^ (-(2 + 1/2))⌋`, then monotonicity in the number of blocks
  have hN₀N : ((⌊r ^ (-(2 + 1 / 2 : ℝ))⌋₊ : ℕ) : ℝ) ≤ N := Nat.cast_le.2 hN
  have h5 : (((⌊r ^ (-(2 + 1 / 2 : ℝ))⌋₊ : ℕ) : ℝ) + 1) * δ ≤ ((N : ℝ) + 1) * δ :=
    mul_le_mul_of_nonneg_right (by linarith) hδ.le
  have h6 : ((⌊r ^ (-(2 + 1 / 2 : ℝ))⌋₊ : ℕ) : ℝ) * δ +
      60 * ((⌊r ^ (-(2 + 1 / 2 : ℝ))⌋₊ : ℕ) : ℝ) ^ 3 * δ / s ≤ κ / 2 := by
    have h7 : ((⌊r ^ (-(2 + 1 / 2 : ℝ))⌋₊ : ℕ) : ℝ) * δ ≤ (N : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hN₀N hδ.le
    have h8 : 60 * ((⌊r ^ (-(2 + 1 / 2 : ℝ))⌋₊ : ℕ) : ℝ) ^ 3 * δ / s ≤
        60 * (N : ℝ) ^ 3 * δ / s :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hN₀N 3) (by norm_num)) hδ.le) hs.le
    linarith
  have hK : ∀ y ∉ F, ‖y - vertexPoint ε η x₀‖ +
      (((⌊r ^ (-(2 + 1 / 2 : ℝ))⌋₊ : ℕ) : ℝ) + 1) * δ < a - 4 * s := by
    intro y hy
    have := hFD y hy _ hz
    linarith
  have hA := hC m hlf hcons ε hε η hη hp c hc x₀ s hs F hF hFs hz θ hθ hθs hM a r δ _ rfl hN₀ ha0 hr0
    hr1 hδ (by linarith) (by linarith) hK hclose
  calc _ ≤ srwLaw m x₀ {x | ∀ n < ⌊r ^ (-(2 + 1 / 2 : ℝ))⌋₊,
          interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s F n (interpPathCM (vertexPoint ε η) hc.le x)) ∉ F} :=
        measure_mono (by intro x hx n hn; exact hx n (hn.trans_le hN))
    _ ≤ _ := hA
    _ ≤ ENNReal.ofReal (κ / 2) + ENNReal.ofReal (κ / 2) :=
        add_le_add (ENNReal.ofReal_le_ofReal hrC) (ENNReal.ofReal_le_ofReal h6)
    _ = ENNReal.ofReal κ := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith), add_halves]

/-- **Both walk-side block-exit bounds at prescribed tolerances.** Freeze the block-exit chains off
the open grid rectangle `R = (a₁ s, a₂ s) × (c₁ s, c₂ s)` and fix `δ₀ > 0`, `κ > 0`. There is
`N₀ > 0` such that for every `N ≥ N₀` there is `δ₁ > 0` with the following property. For every
`0 < δ ≤ δ₁`, every walk (locally finite multiplicities `m` with consecutive vertices adjacent,
embedding `vertexPoint ε η`, speed `c > 0`) started at a vertex `x₀` whose embedded position lies in
`R`, whose edges meeting `R` have length at most `s / 2`, and which satisfies the one-step closeness
`hclose` at tolerance `δ`:

* the law of the first `N + 1` block-exit positions of the interpolated walk is within `(δ₀, κ)`
  of the law of the first `N + 1` block-exit positions of planar Brownian motion started at
  `vertexPoint ε η x₀`, in the one-sided Lévy-Prokhorov sense;
* the probability that the first `N` block-exit positions of the walk all stay in `R` is at most
  `κ`. -/
theorem exists_blockExit_gridRect_walk_bounds {s : ℝ} (hs : 0 < s) (a₁ a₂ c₁ c₂ : ℤ)
    {δ₀ κ : ℝ} (hδ₀ : 0 < δ₀) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∀ (m : ℤ → ℤ → ℕ), IsLocallyFiniteMult m → (∀ k : ℤ, m k (k + 1) ≠ 0) →
      ∀ (ε : ℝ), 0 < ε → ∀ (η : ℝ → ℂ), Continuous η → Tendsto η (cocompact ℝ) (cocompact ℂ) →
      ∀ (c : ℝ) (hc : 0 < c) (x₀ : ℤ), vertexPoint ε η x₀ ∈ gridRectOpen s a₁ a₂ c₁ c₂ →
      (∀ b b' : ℤ, m b b' ≠ 0 →
        (∃ z ∈ segment ℝ (vertexPoint ε η b) (vertexPoint ε η b'),
          z ∉ (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ) →
        dist (vertexPoint ε η b) (vertexPoint ε η b') ≤ s / 2) →
      (∀ y ∈ gridRectOpen s a₁ a₂ c₁ c₂, ∀ u : ℤ, dist (vertexPoint ε η u) y ≤ s / 2 →
        ProkhorovLE
          (walkNextBlockExitKernel m (vertexPoint ε η) hc.le s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ
            (y, u))
          (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ y) δ δ) →
      ProkhorovLE
        ((srwLaw m x₀).map (fun x => blockExitPositions s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ N
          (interpPathCM (vertexPoint ε η) hc.le x)))
        ((planarBrownianMotion (vertexPoint ε η x₀)).map
          (blockExitPositions s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ N)) δ₀ κ ∧
      srwLaw m x₀ {x | ∀ n < N,
          interpPathCM (vertexPoint ε η) hc.le x
            (blockExitTimes s (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ n
              (interpPathCM (vertexPoint ε η) hc.le x)) ∉ (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ} ≤
        ENNReal.ofReal κ := by
  obtain ⟨N₀, hN₀, h⟩ := exists_blockExit_frozen_walk_bounds hs
    (isOpen_gridRectOpen s a₁ a₂ c₁ c₂).measurableSet.compl
    (gridLineStable_compl_gridRectOpen hs a₁ a₂ c₁ c₂)
    (mul_nonneg (by positivity) hs.le : (0 : ℝ) ≤ (|(a₂ : ℝ) - a₁| + |(c₂ : ℝ) - c₁|) * s)
    (fun y hy z hz => norm_sub_le_of_mem_gridRectOpen hs (by simpa using hy) (by simpa using hz))
    hδ₀ hκ
  refine ⟨N₀, hN₀, fun N hN => ?_⟩
  obtain ⟨δ₁, hδ₁, h'⟩ := h N hN
  exact ⟨δ₁, hδ₁, fun δ hδ hδδ₁ m hlf hcons ε hε η hη hp c hc x₀ hz hM hclose =>
    h' δ hδ hδδ₁ m hlf hcons ε hε η hη hp c hc x₀ (fun h => h hz) (s / 2)
      (div_nonneg hs.le zero_le_two) le_rfl hM
      (fun y hy => hclose y (by simpa using hy))⟩

end BlockExit

end MatedCRT
