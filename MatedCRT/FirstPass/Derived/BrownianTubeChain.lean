import MatedCRT.FirstPass.Derived.BrownianOneStepWindow
import MatedCRT.FirstPass.Derived.BrownianTubeMarkov

/-!
# Chains of one-step windows for planar Brownian motion

A step of the tube (support-theorem) argument behind the Brownian disconnection estimate in the
proof of the invariance principle of Gwynne-Miller-Sheffield (Lemma 3.14 of arXiv:1807.07515).

A *window* `tubeStep ε Δ y` is the event that a path stays in the square of half-side `3ε/4`
around its starting point up to time `Δ` and ends in the square of half-side `ε/16` around `y`.
A *chain* `tubeChain ε Δ n y` asks that the path shifted by `i Δ` lies in the window aimed at
`y (i + 1)`, for every `i < n`.

* `measurableSet_tubeStep`: a window belongs to the canonical filtration at time `Δ`.
* `tubeChain_succ`: a chain of `n + 1` windows is the first window intersected with the
  time-`Δ` shift of a chain of `n` windows aimed at the shifted targets.
* `ofReal_oneStepConst_pow_le_planarBrownianMotion_tubeChain`: if consecutive targets differ by
  at most `ε/16` in both coordinates and the start is within `ε/16` of `y 0`, then planar Brownian
  motion follows the chain with probability at least `oneStepConst ε Δ ^ (2n)`. The proof is an
  induction on `n` by the simple Markov property at the deterministic time `Δ`.
* `tubeChain_inter_subset_tube`: a path started near `g 0` that follows the chain aimed at the
  points `g (i Δ)` of a curve `g` stays in a tube of explicit width around `g` up to time `N Δ`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls MatedCRTHarmonic.Brownian

namespace MatedCRT

/-- **One window of a Brownian tube chain.** The path stays in the square of half-side `3ε/4`
around its starting point up to time `Δ` and ends in the square of half-side `ε/16` around
`y`. -/
def tubeStep (ε : ℝ) (Δ : ℝ≥0) (y : ℂ) : Set (ContinuousPath ℂ) :=
  {ω | (∀ t ≤ Δ, |(ω t - ω 0).re| < 3 * ε / 4 ∧ |(ω t - ω 0).im| < 3 * ε / 4) ∧
    |(ω Δ - y).re| < ε / 16 ∧ |(ω Δ - y).im| < ε / 16}

/-- **A chain of `n` windows aimed at the targets `y 1, …, y n`.** For every `i < n`, the path
shifted by `i Δ` lies in the window aimed at `y (i + 1)`. -/
def tubeChain (ε : ℝ) (Δ : ℝ≥0) (n : ℕ) (y : ℕ → ℂ) : Set (ContinuousPath ℂ) :=
  {ω | ∀ i < n, ContinuousPath.shift ((i : ℝ≥0) * Δ) ω ∈ tubeStep ε Δ (y (i + 1))}

/-- The time-`t` evaluation is measurable for the canonical filtration at any time `T ≥ t`. -/
theorem measurable_eval_canonicalFiltration {t T : ℝ≥0} (ht : t ≤ T) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) T]
      (fun ω : ContinuousPath ℂ => ω t) :=
  (ContinuousPath.measurable_coordinateProcess_canonicalFiltration t).mono
    ((ContinuousPath.canonicalFiltration (alpha := ℂ)).mono ht) le_rfl

/-- **A window is adapted.** `tubeStep ε Δ y` belongs to the canonical filtration at time `Δ`. -/
theorem measurableSet_tubeStep (ε : ℝ) (Δ : ℝ≥0) (y : ℂ) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) Δ] (tubeStep ε Δ y) := by
  have hset : tubeStep ε Δ y =
      {ω | ∀ t ≤ Δ, max |(ω t - ω 0).re| |(ω t - ω 0).im| < 3 * ε / 4} ∩
        ((fun ω : ContinuousPath ℂ => |(ω Δ - y).re|) ⁻¹' Iio (ε / 16) ∩
          (fun ω : ContinuousPath ℂ => |(ω Δ - y).im|) ⁻¹' Iio (ε / 16)) := by
    ext ω
    simp only [tubeStep, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio, max_lt_iff]
  have hmax : Continuous fun z : ℂ => max |z.re| |z.im| :=
    (continuous_abs.comp Complex.continuous_re).max (continuous_abs.comp Complex.continuous_im)
  have h0 := measurable_eval_canonicalFiltration (T := Δ) (zero_le : (0 : ℝ≥0) ≤ Δ)
  have hΔ := measurable_eval_canonicalFiltration (le_refl Δ)
  rw [hset]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · refine measurableSet_forall_le_lt_canonicalFiltration Δ
      (fun t (ω : ContinuousPath ℂ) => max |(ω t - ω 0).re| |(ω t - ω 0).im|)
      (fun t ht => ?_) (fun ω => ?_) _
    · exact hmax.measurable.comp ((measurable_eval_canonicalFiltration ht).sub h0)
    · exact hmax.comp (ω.continuous.sub continuous_const)
  · exact ((continuous_abs.comp (Complex.continuous_re.comp
      (continuous_id.sub continuous_const))).measurable.comp hΔ) measurableSet_Iio
  · exact ((continuous_abs.comp (Complex.continuous_im.comp
      (continuous_id.sub continuous_const))).measurable.comp hΔ) measurableSet_Iio

theorem tubeChain_zero (ε : ℝ) (Δ : ℝ≥0) (y : ℕ → ℂ) : tubeChain ε Δ 0 y = univ := by
  ext ω
  simp [tubeChain]

/-- **Recursive structure of a chain.** A chain of `n + 1` windows is the first window
intersected with the time-`Δ` shift of a chain of `n` windows aimed at the shifted targets. -/
theorem tubeChain_succ (ε : ℝ) (Δ : ℝ≥0) (n : ℕ) (y : ℕ → ℂ) :
    tubeChain ε Δ (n + 1) y =
      tubeStep ε Δ (y 1) ∩ ContinuousPath.shift Δ ⁻¹' tubeChain ε Δ n (fun i => y (i + 1)) := by
  have hshift : ∀ (i : ℕ) (ω : ContinuousPath ℂ), ContinuousPath.shift ((i : ℝ≥0) * Δ)
      (ContinuousPath.shift Δ ω) = ContinuousPath.shift (((i + 1 : ℕ) : ℝ≥0) * Δ) ω := by
    intro i ω
    rw [ContinuousPath.shift_add]
    congr 1
    push_cast
    ring
  ext ω
  simp only [tubeChain, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · simpa using h 0 (Nat.succ_pos n)
    · rw [hshift]
      exact h (i + 1) (Nat.succ_lt_succ hi)
  · rintro ⟨h0, h⟩ i hi
    rcases i with _ | i
    · simpa using h0
    · have := h i (Nat.lt_of_succ_lt_succ hi)
      rwa [hshift] at this

/-- A chain is a Borel set of paths. -/
theorem measurableSet_tubeChain (ε : ℝ) (Δ : ℝ≥0) :
    ∀ (n : ℕ) (y : ℕ → ℂ), MeasurableSet (tubeChain ε Δ n y)
  | 0, y => by
    rw [tubeChain_zero]
    exact MeasurableSet.univ
  | n + 1, y => by
    rw [tubeChain_succ]
    exact ((ContinuousPath.canonicalFiltration (alpha := ℂ)).le Δ _
      (measurableSet_tubeStep ε Δ (y 1))).inter
        (ContinuousPath.measurable_shift_fixed Δ (measurableSet_tubeChain ε Δ n _))

/-- **Chain lower bound.** If consecutive targets differ by at most `ε/16` in both coordinates
and the starting point `x` lies within `ε/16` of `y 0` in both coordinates, then planar Brownian
motion started from `x` follows the chain of `n` windows with probability at least
`oneStepConst ε Δ ^ (2n)`. -/
theorem ofReal_oneStepConst_pow_le_planarBrownianMotion_tubeChain {ε : ℝ} (hε : 0 < ε)
    {Δ : ℝ≥0} (hΔ : 0 < Δ) (n : ℕ) :
    ∀ (x : ℂ) (y : ℕ → ℂ),
      (∀ i, |(y (i + 1) - y i).re| ≤ ε / 16 ∧ |(y (i + 1) - y i).im| ≤ ε / 16) →
      |(x - y 0).re| < ε / 16 → |(x - y 0).im| < ε / 16 →
      ENNReal.ofReal (oneStepConst ε Δ) ^ (2 * n) ≤
        planarBrownianMotion x (tubeChain ε Δ n y) := by
  induction n with
  | zero =>
    intro x y _ _ _
    simp [tubeChain_zero]
  | succ n ih =>
    intro x y hy hre him
    set c := ENNReal.ofReal (oneStepConst ε Δ) with hc
    have key : ∀ u v : ℝ, |u| ≤ ε / 16 → |v| < ε / 16 → |u - v| ≤ ε / 8 := fun u v hu hv => by
      obtain ⟨h1, h2⟩ := abs_le.mp hu
      obtain ⟨h3, h4⟩ := abs_lt.mp hv
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have ha_re : |(y 1 - x).re| ≤ ε / 8 := by
      rw [show (y 1 - x).re = (y 1 - y 0).re - (x - y 0).re by simp only [Complex.sub_re]; ring]
      exact key _ _ (hy 0).1 hre
    have ha_im : |(y 1 - x).im| ≤ ε / 8 := by
      rw [show (y 1 - x).im = (y 1 - y 0).im - (x - y 0).im by simp only [Complex.sub_im]; ring]
      exact key _ _ (hy 0).2 him
    have hstep : c ^ 2 ≤ planarBrownianMotion x (tubeStep ε Δ (y 1)) := by
      refine (ofReal_oneStepConst_sq_le_planarBrownianMotion x hε hΔ ha_re ha_im).trans
        (measure_mono_ae ?_)
      filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω h0 hω
      obtain ⟨hw, hre', him'⟩ := hω
      have hend : ω Δ - y 1 = ω Δ - x - (y 1 - x) := by ring
      refine ⟨fun t ht => ?_, ?_, ?_⟩
      · rw [h0]
        exact hw t ht
      · rw [hend]
        exact hre'
      · rw [hend]
        exact him'
    have hchain := le_planarBrownian_inter_shift_preimage x Δ (measurableSet_tubeStep ε Δ (y 1))
      (measurableSet_tubeChain ε Δ n (fun i => y (i + 1))) (p := c ^ (2 * n))
      (fun ω hω => ih (ω Δ) (fun i => y (i + 1)) (fun i => hy (i + 1)) hω.2.1 hω.2.2)
    rw [tubeChain_succ]
    calc c ^ (2 * (n + 1)) = c ^ (2 * n) * c ^ 2 := by rw [mul_add, mul_one, pow_add]
      _ ≤ c ^ (2 * n) * planarBrownianMotion x (tubeStep ε Δ (y 1)) := by gcongr
      _ ≤ _ := hchain

/-- Every time `t ≤ (M + 1) Δ` lies in one of the `M + 1` windows `[i Δ, i Δ + Δ]`, `i ≤ M`. -/
theorem exists_nat_mul_le_le_add (Δ : ℝ≥0) : ∀ (M : ℕ) (t : ℝ≥0), t ≤ ((M + 1 : ℕ) : ℝ≥0) * Δ →
    ∃ i < M + 1, (i : ℝ≥0) * Δ ≤ t ∧ t ≤ (i : ℝ≥0) * Δ + Δ
  | 0, t, ht => ⟨0, Nat.succ_pos 0, by simp, by simpa using ht⟩
  | M + 1, t, ht => by
    by_cases h : t ≤ ((M + 1 : ℕ) : ℝ≥0) * Δ
    · obtain ⟨i, hi, h1, h2⟩ := exists_nat_mul_le_le_add Δ M t h
      exact ⟨i, Nat.lt_succ_of_lt hi, h1, h2⟩
    · refine ⟨M + 1, Nat.lt_succ_self _, (not_le.mp h).le, ?_⟩
      calc t ≤ ((M + 1 + 1 : ℕ) : ℝ≥0) * Δ := ht
        _ = ((M + 1 : ℕ) : ℝ≥0) * Δ + Δ := by push_cast; ring

/-- **A chain stays in a tube around the curve it follows.** Let the targets be
`y i = g (i Δ)` for a curve `g` whose oscillation over time intervals of length `Δ` is at most
`L`. A path started at `x`, within `ε/16` of `g 0` in both coordinates, that follows the chain of
`N ≥ 1` windows stays at distance less than `κ` from `g` up to time `N Δ`, provided
`√2 · 3ε/4 + √2 · ε/16 + L ≤ κ`. -/
theorem tubeChain_inter_subset_tube {ε : ℝ} {Δ : ℝ≥0} {N : ℕ} (hN : 0 < N)
    {g : ℝ≥0 → ℂ} {L κ : ℝ} (hg : ∀ t u : ℝ≥0, t ≤ u → u ≤ t + Δ → ‖g t - g u‖ ≤ L)
    (hκ : Real.sqrt 2 * (3 * ε / 4) + Real.sqrt 2 * (ε / 16) + L ≤ κ) {x : ℂ}
    (hx_re : |(x - g 0).re| < ε / 16) (hx_im : |(x - g 0).im| < ε / 16) :
    tubeChain ε Δ N (fun i => g ((i : ℝ≥0) * Δ)) ∩ {ω | ω 0 = x} ⊆
      {ω | ∀ t ≤ (N : ℝ≥0) * Δ, ‖ω t - g t‖ < κ} := by
  rintro ω ⟨hω, h0⟩
  simp only [tubeChain, mem_ofPred_eq] at hω h0 ⊢
  intro t ht
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨i, hi, hit, hti⟩ := exists_nat_mul_le_le_add Δ M t ht
  have hsΔ : t - (i : ℝ≥0) * Δ ≤ Δ := tsub_le_iff_left.mpr hti
  have hωt : ContinuousPath.shift ((i : ℝ≥0) * Δ) ω (t - (i : ℝ≥0) * Δ) = ω t := by
    rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le hit]
  have hωi : ContinuousPath.shift ((i : ℝ≥0) * Δ) ω 0 = ω ((i : ℝ≥0) * Δ) := by
    rw [ContinuousPath.shift_apply, add_zero]
  obtain ⟨hre1, him1⟩ := (hω i hi).1 _ hsΔ
  rw [hωt, hωi] at hre1 him1
  have hstart : |(ω ((i : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ)).re| < ε / 16 ∧
      |(ω ((i : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ)).im| < ε / 16 := by
    rcases i with _ | j
    · simpa [h0] using And.intro hx_re hx_im
    · have hj := (hω j (by omega)).2
      have he : (j : ℝ≥0) * Δ + Δ = ((j + 1 : ℕ) : ℝ≥0) * Δ := by push_cast; ring
      simp only [ContinuousPath.shift_apply, he] at hj
      exact hj
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hA : ‖ω t - ω ((i : ℝ≥0) * Δ)‖ < Real.sqrt 2 * (3 * ε / 4) :=
    (Complex.norm_le_sqrt_two_mul_max _).trans_lt (mul_lt_mul_of_pos_left (max_lt hre1 him1) h2)
  have hB : ‖ω ((i : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ)‖ < Real.sqrt 2 * (ε / 16) :=
    (Complex.norm_le_sqrt_two_mul_max _).trans_lt
      (mul_lt_mul_of_pos_left (max_lt hstart.1 hstart.2) h2)
  have hC : ‖g ((i : ℝ≥0) * Δ) - g t‖ ≤ L := hg _ _ hit hti
  calc ‖ω t - g t‖ = ‖(ω t - ω ((i : ℝ≥0) * Δ)) + (ω ((i : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ)) +
        (g ((i : ℝ≥0) * Δ) - g t)‖ := by congr 1; ring
    _ ≤ ‖ω t - ω ((i : ℝ≥0) * Δ)‖ + ‖ω ((i : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ)‖ +
        ‖g ((i : ℝ≥0) * Δ) - g t‖ := norm_add₃_le
    _ < κ := by linarith

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.measurableSet_tubeStep
#print axioms MatedCRT.tubeChain_succ
#print axioms MatedCRT.measurableSet_tubeChain
#print axioms MatedCRT.ofReal_oneStepConst_pow_le_planarBrownianMotion_tubeChain
#print axioms MatedCRT.exists_nat_mul_le_le_add
#print axioms MatedCRT.tubeChain_inter_subset_tube
