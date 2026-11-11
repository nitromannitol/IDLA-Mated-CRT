import MatedCRT.Defs.QuantumCone
import MarkovProcess.Examples.BrownianMotion
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic

/-!
# Ordinary Brownian motion has negative drift

For the standard Brownian motion `brownianMotion 0` of `MarkovProcess` and every `c > 0`, almost surely
`B_t - c t → -∞` as `t → ∞` (Karatzas-Shreve, Chapter 2, Problem 9.3, the Brownian strong law `B_t / t → 0`).
With `c = Q - γ > 0` (`HarmonicBalls.lqgQ`, Duplantier-Sheffield Definition 2.1) this is the input of the `r → 0⁺`
clause of `hlim` in `S2x/ConeScaleRadiusPos.lean`: the radial part is `A_t = B_t + γ t`, and `log r = -t`.

Method (Doob-free): the Gaussian Chernoff bound on each dyadic increment, a union bound over the `8^j` intervals of
level `j`, Borel-Cantelli over the unit intervals `[n, n+1]`, and a deterministic dyadic chaining from the grid to the
continuum. No maximal inequality and no independence beyond the Gaussian laws of `brownianMotion_map_increment`
and `brownianMotion_map_eval` are used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped ENNReal NNReal
open MarkovProcess

namespace MatedCRT.S2x.BrownianDrift

/-- Chernoff bound for the centred Gaussian: `P(θ ≤ s Y) ≤ exp(-θ²/(2v))` for `Y ~ N(0, v)` and `s² = 1`. -/
lemma gaussian_tail_sign {v : ℝ≥0} (hv : 0 < v) (s : ℝ) (hs : s ^ 2 = 1) (θ : ℝ) (hθ : 0 ≤ θ) :
    (gaussianReal 0 v).real {y | θ ≤ s * y} ≤ exp (-θ ^ 2 / (2 * (v : ℝ))) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hv0 : (v : ℝ) ≠ 0 := hv'.ne'
  have ht : 0 ≤ θ / (v : ℝ) := div_nonneg hθ hv'.le
  have hint : Integrable (fun y : ℝ => exp ((θ / (v : ℝ)) * (s * y))) (gaussianReal 0 v) := by
    have e : (fun y : ℝ => exp ((θ / (v : ℝ)) * (s * y))) = fun y => exp (((θ / (v : ℝ)) * s) * y) := by
      funext y
      congr 1
      ring
    rw [e]
    exact integrable_exp_mul_gaussianReal _
  have hmgf : mgf (fun y : ℝ => s * y) (gaussianReal 0 v) (θ / (v : ℝ))
      = exp ((v : ℝ) * ((θ / (v : ℝ)) * s) ^ 2 / 2) := by
    have h1 : mgf (fun y : ℝ => s * y) (gaussianReal 0 v) (θ / (v : ℝ))
        = mgf id (gaussianReal 0 v) ((θ / (v : ℝ)) * s) := by
      unfold mgf
      apply integral_congr_ae
      filter_upwards with ω
      simp only [id]
      congr 1
      ring
    rw [h1, mgf_id_gaussianReal]
    simp only [zero_mul, zero_add]
  have hC := measure_ge_le_exp_mul_mgf (X := fun y : ℝ => s * y) (μ := gaussianReal 0 v)
    (t := θ / (v : ℝ)) θ ht hint
  have hsq : ((θ / (v : ℝ)) * s) ^ 2 = (θ / (v : ℝ)) ^ 2 := by
    rw [mul_pow, hs, mul_one]
  calc (gaussianReal 0 v).real {y | θ ≤ s * y}
      ≤ exp (-(θ / (v : ℝ)) * θ) * mgf (fun y : ℝ => s * y) (gaussianReal 0 v) (θ / (v : ℝ)) := hC
    _ = exp (-(θ / (v : ℝ)) * θ + (v : ℝ) * ((θ / (v : ℝ)) * s) ^ 2 / 2) := by
      rw [hmgf, ← Real.exp_add]
    _ = exp (-θ ^ 2 / (2 * (v : ℝ))) := by
      congr 1
      rw [hsq]
      field_simp
      ring

/-- Two-sided Gaussian tail: `P(θ < |Y|) ≤ 2 exp(-θ²/(2v))` for `Y ~ N(0, v)`. -/
lemma gaussian_abs_tail {v : ℝ≥0} (hv : 0 < v) (θ : ℝ) (hθ : 0 ≤ θ) :
    (gaussianReal 0 v).real {y | θ < |y|} ≤ 2 * exp (-θ ^ 2 / (2 * (v : ℝ))) := by
  have hsub : {y : ℝ | θ < |y|} ⊆ {y | θ ≤ 1 * y} ∪ {y | θ ≤ (-1) * y} := by
    intro y hy
    rcases lt_abs.1 (show θ < |y| from hy) with h | h
    · exact Or.inl (by simp only [mem_ofPred_eq, one_mul]; exact h.le)
    · exact Or.inr (by simp only [mem_ofPred_eq]; linarith)
  have h1 := gaussian_tail_sign hv 1 (by norm_num) θ hθ
  have h2 := gaussian_tail_sign hv (-1) (by norm_num) θ hθ
  calc (gaussianReal 0 v).real {y | θ < |y|}
      ≤ (gaussianReal 0 v).real ({y | θ ≤ 1 * y} ∪ {y | θ ≤ (-1) * y}) := measureReal_mono hsub
    _ ≤ (gaussianReal 0 v).real {y | θ ≤ 1 * y} + (gaussianReal 0 v).real {y | θ ≤ (-1) * y} :=
        measureReal_union_le _ _
    _ ≤ 2 * exp (-θ ^ 2 / (2 * (v : ℝ))) := by linarith

/-- A functional of the Brownian path with Gaussian law `N(0, v)` has two-sided tail `2 exp(-θ²/(2v))`. -/
lemma brownian_tail_of_map {f : ContinuousPath ℝ → ℝ} (hf : Measurable f) {v : ℝ≥0} (hv : 0 < v)
    (hmap : (brownianMotion (0 : ℝ)).map f = gaussianReal 0 v) (θ : ℝ) (hθ : 0 ≤ θ) :
    (brownianMotion (0 : ℝ)).real {w | θ < |f w|} ≤ 2 * exp (-θ ^ 2 / (2 * (v : ℝ))) := by
  have hS : MeasurableSet {y : ℝ | θ < |y|} := measurableSet_lt measurable_const measurable_abs
  calc (brownianMotion (0 : ℝ)).real {w | θ < |f w|}
      = (brownianMotion (0 : ℝ)).real (f ⁻¹' {y : ℝ | θ < |y|}) := rfl
    _ = ((brownianMotion (0 : ℝ)).map f).real {y : ℝ | θ < |y|} :=
        (map_measureReal_apply hf hS).symm
    _ = (gaussianReal 0 v).real {y : ℝ | θ < |y|} := by rw [hmap]
    _ ≤ 2 * exp (-θ ^ 2 / (2 * (v : ℝ))) := gaussian_abs_tail hv θ hθ

/-- Tail of a Brownian increment: `P(θ < |B_b - B_a|) ≤ 2 exp(-θ²/(2(b-a)))` for `a < b`. -/
lemma brownian_increment_tail {a b : ℝ≥0} (hab : a < b) (θ : ℝ) (hθ : 0 ≤ θ) :
    (brownianMotion (0 : ℝ)).real {w | θ < |w b - w a|}
      ≤ 2 * exp (-θ ^ 2 / (2 * ((b : ℝ) - a))) := by
  have hv : 0 < b - a := tsub_pos_of_lt hab
  have hcoe : ((b - a : ℝ≥0) : ℝ) = (b : ℝ) - a := NNReal.coe_sub hab.le
  have hf : Measurable (fun w : ContinuousPath ℝ => w b - w a) :=
    (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) b).sub
      (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) a)
  have h := brownian_tail_of_map hf hv (brownianMotion_map_increment 0 a b hab.le) θ hθ
  rw [hcoe] at h
  exact h

/-- Tail of a Brownian value: `P(θ < |B_t|) ≤ 2 exp(-θ²/(2t))` for `t > 0`. -/
lemma brownian_eval_tail {t : ℝ≥0} (ht : 0 < t) (θ : ℝ) (hθ : 0 ≤ θ) :
    (brownianMotion (0 : ℝ)).real {w | θ < |w t|} ≤ 2 * exp (-θ ^ 2 / (2 * (t : ℝ))) := by
  have hf : Measurable (fun w : ContinuousPath ℝ => w t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t
  exact brownian_tail_of_map hf ht (brownianMotion_map_eval t 0) θ hθ


/-! ## Dyadic chaining (deterministic) -/

/-- Along the level-`j` grid `n + i / 8^j`, a run of `c` consecutive steps starting at `a` moves `W` by at most `c θ`. -/
lemma grid_run_bound (W : ℝ → ℝ) (n : ℝ) (j : ℕ) (θ : ℝ)
    (H : ∀ i : ℕ, i < 8 ^ j → |W (n + ((i : ℝ) + 1) / 8 ^ j) - W (n + (i : ℝ) / 8 ^ j)| ≤ θ) :
    ∀ a c : ℕ, a + c ≤ 8 ^ j →
      |W (n + ((a : ℝ) + c) / 8 ^ j) - W (n + (a : ℝ) / 8 ^ j)| ≤ (c : ℝ) * θ := by
  intro a c
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro hac
    have h1 := ih (by omega)
    have h2 := H (a + c) (by omega)
    have e1 : ((a + c : ℕ) : ℝ) = (a : ℝ) + c := by push_cast; ring
    rw [e1] at h2
    have e2 : (a : ℝ) + ((c + 1 : ℕ) : ℝ) = ((a : ℝ) + c) + 1 := by push_cast; ring
    rw [e2, Nat.cast_succ]
    have e3 : n + (((a : ℝ) + c) + 1) / 8 ^ j = n + (((a : ℝ) + c) + 1) / 8 ^ j := rfl
    calc |W (n + (((a : ℝ) + c) + 1) / 8 ^ j) - W (n + (a : ℝ) / 8 ^ j)|
        ≤ |W (n + (((a : ℝ) + c) + 1) / 8 ^ j) - W (n + ((a : ℝ) + c) / 8 ^ j)|
          + |W (n + ((a : ℝ) + c) / 8 ^ j) - W (n + (a : ℝ) / 8 ^ j)| := abs_sub_le _ _ _
      _ ≤ θ + (c : ℝ) * θ := add_le_add h2 h1
      _ = ((c : ℝ) + 1) * θ := by ring

/-- The dyadic index `⌊8^j (t - n)⌋₊` of `t` at level `j`, relative to the base point `n`. -/
noncomputable def dyadicIndex (n t : ℝ) (j : ℕ) : ℕ := ⌊(8 : ℝ) ^ j * (t - n)⌋₊

/-- The level-`j` dyadic point `n + ⌊8^j (t - n)⌋₊ / 8^j` below `t`. -/
noncomputable def dyadicPoint (n t : ℝ) (j : ℕ) : ℝ := n + (dyadicIndex n t j : ℝ) / 8 ^ j

lemma dyadicIndex_le {n t : ℝ} (ht1 : t ≤ n + 1) (j : ℕ) :
    dyadicIndex n t j ≤ 8 ^ j := by
  unfold dyadicIndex
  have hx : (8 : ℝ) ^ j * (t - n) ≤ ((8 ^ j : ℕ) : ℝ) := by
    push_cast
    have h1 : t - n ≤ 1 := by linarith
    have h2 : (0 : ℝ) ≤ 8 ^ j := by positivity
    nlinarith
  calc ⌊(8 : ℝ) ^ j * (t - n)⌋₊ ≤ ⌊((8 ^ j : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor hx
    _ = 8 ^ j := Nat.floor_natCast _

lemma dyadicIndex_div (n t : ℝ) (k : ℕ) :
    dyadicIndex n t k = dyadicIndex n t (k + 1) / 8 := by
  unfold dyadicIndex
  have e : (8 : ℝ) ^ k * (t - n) = (8 : ℝ) ^ (k + 1) * (t - n) / ((8 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [e, Nat.floor_div_natCast]

/-- Dyadic chaining: if every level-`j` increment of `W` over the grid `n + i / 8^j` (`i < 8^j`) is at most
`θ0 (1/2)^j`, then `|W t - W n| ≤ 8 θ0` for `t ∈ [n, n+1]` (Karatzas-Shreve, Chapter 2, Problem 9.3). -/
lemma chain_bound (W : ℝ → ℝ) (hW : Continuous W) (n θ0 : ℝ) (hθ0 : 0 ≤ θ0)
    (H : ∀ j i : ℕ, i < 8 ^ j →
      |W (n + ((i : ℝ) + 1) / 8 ^ j) - W (n + (i : ℝ) / 8 ^ j)| ≤ θ0 * (1 / 2) ^ j)
    (t : ℝ) (ht0 : n ≤ t) (ht1 : t ≤ n + 1) : |W t - W n| ≤ 8 * θ0 := by
  -- one step of the chain: from level `k` to level `k + 1`
  have hstep : ∀ k : ℕ, |W (dyadicPoint n t (k + 1)) - W (dyadicPoint n t k)|
      ≤ 7 * (θ0 * (1 / 2) ^ (k + 1)) := by
    intro k
    have hcomb : 8 * dyadicIndex n t k + dyadicIndex n t (k + 1) % 8 = dyadicIndex n t (k + 1) := by
      have := dyadicIndex_div n t k
      omega
    have hc7 : dyadicIndex n t (k + 1) % 8 ≤ 7 := by omega
    have hq1 : dyadicPoint n t (k + 1)
        = n + (((8 * dyadicIndex n t k : ℕ) : ℝ) + ((dyadicIndex n t (k + 1) % 8 : ℕ) : ℝ)) / 8 ^ (k + 1) := by
      unfold dyadicPoint
      congr 1
      rw [← Nat.cast_add, hcomb]
    have hq0 : dyadicPoint n t k = n + ((8 * dyadicIndex n t k : ℕ) : ℝ) / 8 ^ (k + 1) := by
      unfold dyadicPoint
      congr 1
      push_cast
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    have hrun := grid_run_bound W n (k + 1) (θ0 * (1 / 2) ^ (k + 1)) (fun i hi => H (k + 1) i hi)
      (8 * dyadicIndex n t k) (dyadicIndex n t (k + 1) % 8) (by
        have := dyadicIndex_le ht1 (k + 1)
        omega)
    rw [hq1, hq0]
    refine le_trans hrun ?_
    have hnn : 0 ≤ θ0 * (1 / 2) ^ (k + 1) := by positivity
    have hc' : ((dyadicIndex n t (k + 1) % 8 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast hc7
    nlinarith
  have hI0 : dyadicIndex n t 0 ≤ 1 := by
    have := dyadicIndex_le ht1 0
    simpa using this
  have hbase : |W (dyadicPoint n t 0) - W n| ≤ θ0 := by
    have hrun := grid_run_bound W n 0 (θ0 * (1 / 2) ^ 0) (fun i hi => H 0 i hi) 0 (dyadicIndex n t 0)
      (by simpa using dyadicIndex_le ht1 0)
    have e : (n + (((0 : ℕ) : ℝ) + ((dyadicIndex n t 0 : ℕ) : ℝ)) / 8 ^ 0) = dyadicPoint n t 0 := by
      unfold dyadicPoint
      simp
    have e' : (n + ((0 : ℕ) : ℝ) / 8 ^ 0) = n := by simp
    rw [e, e'] at hrun
    have hI0' : ((dyadicIndex n t 0 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hI0
    calc |W (dyadicPoint n t 0) - W n| ≤ ((dyadicIndex n t 0 : ℕ) : ℝ) * (θ0 * (1 / 2) ^ 0) := hrun
      _ ≤ 1 * (θ0 * (1 / 2) ^ 0) := mul_le_mul_of_nonneg_right hI0' (by positivity)
      _ = θ0 := by simp
  have hind : ∀ J : ℕ, |W (dyadicPoint n t J) - W n| ≤ 8 * θ0 - 7 * (θ0 * (1 / 2) ^ J) := by
    intro J
    induction J with
    | zero => simp only [pow_zero, mul_one]; linarith
    | succ J ih =>
      have h1 := hstep J
      have h2 := abs_sub_le (W (dyadicPoint n t (J + 1))) (W (dyadicPoint n t J)) (W n)
      have hp : θ0 * (1 / 2) ^ J = 2 * (θ0 * (1 / 2) ^ (J + 1)) := by rw [pow_succ]; ring
      linarith
  have hfin : ∀ J : ℕ, |W (dyadicPoint n t J) - W n| ≤ 8 * θ0 := by
    intro J
    have h1 := hind J
    have h2 : 0 ≤ 7 * (θ0 * (1 / 2) ^ J) := by positivity
    linarith
  have hdist : ∀ J : ℕ, |dyadicPoint n t J - t| ≤ (1 / 8 : ℝ) ^ J := by
    intro J
    have hp : (0 : ℝ) < 8 ^ J := by positivity
    have hx0 : 0 ≤ (8 : ℝ) ^ J * (t - n) := mul_nonneg hp.le (by linarith)
    have h1 : ((dyadicIndex n t J : ℕ) : ℝ) ≤ (8 : ℝ) ^ J * (t - n) := Nat.floor_le hx0
    have h2 : (8 : ℝ) ^ J * (t - n) < ((dyadicIndex n t J : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have A : ((dyadicIndex n t J : ℕ) : ℝ) / 8 ^ J ≤ t - n := by
      rw [div_le_iff₀ hp]
      linarith [mul_comm (t - n) ((8 : ℝ) ^ J)]
    have B : t - n < (((dyadicIndex n t J : ℕ) : ℝ) + 1) / 8 ^ J := by
      rw [lt_div_iff₀ hp]
      linarith [mul_comm (t - n) ((8 : ℝ) ^ J)]
    have C : (((dyadicIndex n t J : ℕ) : ℝ) + 1) / 8 ^ J
        = ((dyadicIndex n t J : ℕ) : ℝ) / 8 ^ J + 1 / 8 ^ J := add_div _ _ _
    rw [one_div_pow, dyadicPoint, abs_le]
    constructor <;> linarith
  have hqt : Tendsto (fun J : ℕ => dyadicPoint n t J) atTop (𝓝 t) := by
    have h0 : Tendsto (fun J : ℕ => (1 / 8 : ℝ) ^ J) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun J => norm_nonneg _) (fun J => by simpa [Real.norm_eq_abs] using hdist J) h0)
  have hWt : Tendsto (fun J : ℕ => |W (dyadicPoint n t J) - W n|) atTop (𝓝 |W t - W n|) :=
    (((hW.tendsto t).comp hqt).sub_const (W n)).abs
  exact le_of_tendsto hWt (Eventually.of_forall fun J => hfin J)

/-! ## Probability: dyadic increments of the Brownian path -/

/-- The Brownian path read on `ℝ` through `toNNReal`, as in `chain_bound`. -/
noncomputable def pathR (w : ContinuousPath ℝ) (s : ℝ) : ℝ := w (Real.toNNReal s)

lemma continuous_pathR (w : ContinuousPath ℝ) : Continuous (pathR w) :=
  w.continuous.comp continuous_real_toNNReal

/-- The level-`j` dyadic increment of `pathR w` over `[n + i/8^j, n + (i+1)/8^j]` exceeds `δ n (1/2)^j / 16`. -/
def levelEvent (δ : ℝ) (n j i : ℕ) : Set (ContinuousPath ℝ) :=
  {w | δ * n / 16 * (1 / 2) ^ j < |pathR w (n + ((i : ℝ) + 1) / 8 ^ j) - pathR w (n + (i : ℝ) / 8 ^ j)|}

/-- A real probability bound turned into an `ℝ≥0∞` bound for a finite measure. -/
lemma le_ofReal_of_measureReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Set Ω} {r : ℝ} (h : μ.real s ≤ r) : μ s ≤ ENNReal.ofReal r := by
  have e : μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
  rw [e]
  exact ENNReal.ofReal_le_ofReal h

/-- Exponent identity: for `θ = δ n (1/2)^j / 16` and the increment variance `1/8^j`,
`θ² / (2/8^j) = (δ²/512) n² 2^j`. -/
lemma exponent_identity (δ : ℝ) (n j : ℕ) :
    -(δ * n / 16 * (1 / 2) ^ j) ^ 2 / (2 * (1 / 8 ^ j)) = -(δ ^ 2 / 512) * (n : ℝ) ^ 2 * 2 ^ j := by
  have h8 : (8 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 3 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hp : (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ j := one_div_pow _ _
  rw [h8, hp]
  have hY : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp
  ring

/-- The level-`j` increment bound: each dyadic increment exceeds `δ n (1/2)^j / 16` with probability
at most `2 exp(-(δ²/512) n² 2^j)` (Gaussian tail of the increment law `N(0, 8^{-j})`). -/
lemma levelEvent_real_le (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) (hn : 1 ≤ n) (j i : ℕ) :
    (brownianMotion (0 : ℝ)).real (levelEvent δ n j i)
      ≤ 2 * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2 * 2 ^ j) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 1 / 8 ^ j := by positivity
  have ha0 : 0 ≤ (n : ℝ) + (i : ℝ) / 8 ^ j := by positivity
  have hb0 : 0 ≤ (n : ℝ) + ((i : ℝ) + 1) / 8 ^ j := by positivity
  have hab : Real.toNNReal ((n : ℝ) + (i : ℝ) / 8 ^ j) < Real.toNNReal ((n : ℝ) + ((i : ℝ) + 1) / 8 ^ j) := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ha0, Real.coe_toNNReal _ hb0]
    have : (n : ℝ) + ((i : ℝ) + 1) / 8 ^ j - ((n : ℝ) + (i : ℝ) / 8 ^ j) = 1 / 8 ^ j := by ring
    linarith
  have hθ : 0 ≤ δ * n / 16 * (1 / 2) ^ j :=
    mul_nonneg (div_nonneg (mul_nonneg hδ (Nat.cast_nonneg n)) (by norm_num)) (pow_nonneg (by norm_num) j)
  have h := brownian_increment_tail hab (δ * n / 16 * (1 / 2) ^ j) hθ
  rw [Real.coe_toNNReal _ hb0, Real.coe_toNNReal _ ha0] at h
  have hd : (n : ℝ) + ((i : ℝ) + 1) / 8 ^ j - ((n : ℝ) + (i : ℝ) / 8 ^ j) = 1 / 8 ^ j := by ring
  rw [hd, exponent_identity δ n j] at h
  exact h

/-- Union of the `8^j` level-`j` events. -/
lemma levelUnion_le (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    (brownianMotion (0 : ℝ)) (⋃ i ∈ Finset.range (8 ^ j), levelEvent δ n j i)
      ≤ ENNReal.ofReal (((8 ^ j : ℕ) : ℝ) * (2 * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2 * 2 ^ j))) := by
  calc (brownianMotion (0 : ℝ)) (⋃ i ∈ Finset.range (8 ^ j), levelEvent δ n j i)
      ≤ ∑ i ∈ Finset.range (8 ^ j), (brownianMotion (0 : ℝ)) (levelEvent δ n j i) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range (8 ^ j), ENNReal.ofReal (2 * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2 * 2 ^ j)) :=
        Finset.sum_le_sum fun i _ => le_ofReal_of_measureReal (levelEvent_real_le δ hδ n hn j i)
    _ = ENNReal.ofReal (((8 ^ j : ℕ) : ℝ) * (2 * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2 * 2 ^ j))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- Exponential splitting: for `m ≥ 1` and `Y ≥ 1`, `exp(-c m Y) ≤ exp(-c m) exp(c) exp(-c Y)`. -/
lemma exp_split_le (c : ℝ) (hc : 0 < c) (m Y : ℝ) (hm : 1 ≤ m) (hY : 1 ≤ Y) :
    exp (-c * m * Y) ≤ exp (-c * m) * exp c * exp (-c * Y) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [mul_nonneg (mul_nonneg hc.le (by linarith : (0 : ℝ) ≤ m - 1)) (by linarith : (0 : ℝ) ≤ Y - 1)]

/-- `Y³ exp(-c Y) ≤ (24/c⁴) (1/Y)` for `Y ≥ 1` (from `exp x ≥ x⁴/24`). -/
lemma pow_three_mul_exp_le (c : ℝ) (hc : 0 < c) (Y : ℝ) (hY : 1 ≤ Y) :
    Y ^ 3 * exp (-c * Y) ≤ 24 / c ^ 4 * (1 / Y) := by
  have hcY : 0 ≤ c * Y := mul_nonneg hc.le (by linarith)
  have h4 := Real.pow_div_factorial_le_exp (c * Y) hcY 4
  have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac] at h4
  have hle : (c * Y) ^ 4 ≤ 24 * exp (c * Y) := by linarith
  have hprod : exp (-c * Y) * exp (c * Y) = 1 := by rw [← Real.exp_add]; simp
  have hmain : exp (-c * Y) * (c * Y) ^ 4 ≤ 24 := by
    have := mul_le_mul_of_nonneg_left hle (Real.exp_nonneg (-c * Y))
    nlinarith
  have hY0 : 0 < Y := by linarith
  have e : 24 / c ^ 4 * (1 / Y) = 24 / (c ^ 4 * Y) := by field_simp
  rw [e, le_div_iff₀ (by positivity)]
  have e2 : Y ^ 3 * exp (-c * Y) * (c ^ 4 * Y) = exp (-c * Y) * (c * Y) ^ 4 := by ring
  linarith [e2, hmain]

/-- The per-level constant: `8^j · 2 exp(-c n² 2^j) ≤ (2 e^c · 24/c⁴) exp(-c n²) (1/2)^j`, with `c = δ²/512`. -/
lemma level_term_le (c : ℝ) (hc : 0 < c) (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    ((8 ^ j : ℕ) : ℝ) * (2 * exp (-c * (n : ℝ) ^ 2 * 2 ^ j))
      ≤ (2 * exp c * (24 / c ^ 4)) * exp (-c * (n : ℝ) ^ 2) * (1 / 2) ^ j := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hY : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hcast : ((8 ^ j : ℕ) : ℝ) = ((2 : ℝ) ^ j) ^ 3 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hp : (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ j := one_div_pow _ _
  rw [hcast, hp]
  have h1 := exp_split_le c hc ((n : ℝ) ^ 2) ((2 : ℝ) ^ j) hm hY
  have h2 := pow_three_mul_exp_le c hc ((2 : ℝ) ^ j) hY
  calc ((2 : ℝ) ^ j) ^ 3 * (2 * exp (-c * (n : ℝ) ^ 2 * 2 ^ j))
      ≤ ((2 : ℝ) ^ j) ^ 3 * (2 * (exp (-c * (n : ℝ) ^ 2) * exp c * exp (-c * 2 ^ j))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by norm_num)) (by positivity)
    _ = (2 * exp c) * exp (-c * (n : ℝ) ^ 2) * (((2 : ℝ) ^ j) ^ 3 * exp (-c * 2 ^ j)) := by ring
    _ ≤ (2 * exp c) * exp (-c * (n : ℝ) ^ 2) * (24 / c ^ 4 * (1 / 2 ^ j)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (2 * exp c * (24 / c ^ 4)) * exp (-c * (n : ℝ) ^ 2) * (1 / 2 ^ j) := by ring

/-- The union of all level-`j` events, over all levels `j`. -/
def levelUnionEvent (δ : ℝ) (n : ℕ) : Set (ContinuousPath ℝ) :=
  ⋃ j : ℕ, ⋃ i ∈ Finset.range (8 ^ j), levelEvent δ n j i

/-- The dyadic oscillation event on `[n, n+1]` has probability `≤ 2 K e^{-c n²}`, `K = 2 e^c · 24/c⁴`, `c = δ²/512`. -/
lemma levelUnionEvent_le (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 1 ≤ n) :
    (brownianMotion (0 : ℝ)) (levelUnionEvent δ n)
      ≤ ENNReal.ofReal (2 * ((2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4))
          * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2))) := by
  have hc : 0 < δ ^ 2 / 512 := by positivity
  have hB0 : 0 ≤ (2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4))
      * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2) := by positivity
  calc (brownianMotion (0 : ℝ)) (levelUnionEvent δ n)
      ≤ ∑' j : ℕ, (brownianMotion (0 : ℝ)) (⋃ i ∈ Finset.range (8 ^ j), levelEvent δ n j i) :=
        measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal ((2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4))
          * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2) * (1 / 2) ^ j) :=
        ENNReal.tsum_le_tsum fun j => (levelUnion_le δ hδ.le n hn j).trans
          (ENNReal.ofReal_le_ofReal (by
            have := level_term_le (δ ^ 2 / 512) hc n hn j
            calc _ ≤ _ := this
              _ = _ := by ring))
    _ = ENNReal.ofReal (∑' j : ℕ, (2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4))
          * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2) * (1 / 2) ^ j) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hB0 (by positivity))
          (summable_geometric_two.mul_left _)).symm
    _ = ENNReal.ofReal (2 * ((2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4))
          * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2))) := by
        congr 1
        rw [tsum_mul_left, tsum_geometric_two]
        ring

/-! ## Borel-Cantelli over the unit intervals `[n, n+1]` -/

/-- The endpoint event `|B_n| > δ n / 2` at integer time `n` (Gaussian `N(0, n)`). -/
def endpointEvent (δ : ℝ) (n : ℕ) : Set (ContinuousPath ℝ) :=
  {w | δ * n / 2 < |pathR w n|}

/-- The bad event on the unit interval `[n, n+1]`: an endpoint or a dyadic oscillation exceeds its threshold. -/
def badEvent (δ : ℝ) (n : ℕ) : Set (ContinuousPath ℝ) :=
  levelUnionEvent δ n ∪ endpointEvent δ n

/-- Exponent constant `min(δ²/512, δ²/8)`. -/
noncomputable def cBound (δ : ℝ) : ℝ := min (δ ^ 2 / 512) (δ ^ 2 / 8)

/-- Prefactor `2K' + 2` with `K' = 2 e^{δ²/512} · 24 / (δ²/512)⁴`. -/
noncomputable def mBound (δ : ℝ) : ℝ := 2 * (2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4)) + 2

lemma cBound_pos {δ : ℝ} (hδ : 0 < δ) : 0 < cBound δ :=
  lt_min (by positivity) (by positivity)

lemma endpointEvent_le (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 1 ≤ n) :
    (brownianMotion (0 : ℝ)) (endpointEvent δ n) ≤ ENNReal.ofReal (2 * exp (-(δ ^ 2 / 8) * (n : ℝ))) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast (show 0 < n by omega)
  have hθ : 0 ≤ δ * n / 2 := by
    have : (0 : ℝ) ≤ n := by positivity
    exact div_nonneg (mul_nonneg hδ.le this) (by norm_num)
  have h := brownian_eval_tail ht (δ * n / 2) hθ
  have hset : endpointEvent δ n = {w : ContinuousPath ℝ | δ * n / 2 < |w (n : ℝ≥0)|} := by
    ext w
    simp [endpointEvent, pathR]
  rw [hset]
  refine le_ofReal_of_measureReal (h.trans ?_)
  rw [NNReal.coe_natCast]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.2
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have e : -(δ * n / 2) ^ 2 / (2 * (n : ℝ)) = -(δ ^ 2 / 8) * (n : ℝ) := by
    field_simp
    ring
  exact le_of_eq e

lemma badEvent_le (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 1 ≤ n) :
    (brownianMotion (0 : ℝ)) (badEvent δ n) ≤ ENNReal.ofReal (mBound δ * exp (-cBound δ * (n : ℝ))) := by
  have hc : 0 < δ ^ 2 / 512 := by positivity
  have hcB : 0 < cBound δ := cBound_pos hδ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hA := levelUnionEvent_le δ hδ n hn
  have hB := endpointEvent_le δ hδ n hn
  have hK' : 0 ≤ 2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4) := by positivity
  have hX : 0 ≤ 2 * ((2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4))
      * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2)) := by positivity
  have hY : 0 ≤ 2 * exp (-(δ ^ 2 / 8) * (n : ℝ)) := by positivity
  have h1 : exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2) ≤ exp (-cBound δ * (n : ℝ)) := by
    apply Real.exp_le_exp.2
    have hcb : cBound δ ≤ δ ^ 2 / 512 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hcb (sq_nonneg (n : ℝ)),
      mul_le_mul_of_nonneg_left (show (n : ℝ) ≤ (n : ℝ) ^ 2 by nlinarith) hcB.le]
  have h2 : exp (-(δ ^ 2 / 8) * (n : ℝ)) ≤ exp (-cBound δ * (n : ℝ)) := by
    apply Real.exp_le_exp.2
    have hcb : cBound δ ≤ δ ^ 2 / 8 := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right hcb hn0]
  have hsum := add_le_add hA hB
  rw [← ENNReal.ofReal_add hX hY] at hsum
  refine (measure_union_le _ _).trans (hsum.trans (ENNReal.ofReal_le_ofReal ?_))
  have hX' : 2 * ((2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4))
        * exp (-(δ ^ 2 / 512) * (n : ℝ) ^ 2))
      ≤ 2 * ((2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4)) * exp (-cBound δ * (n : ℝ))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hK') (by norm_num)
  have hY' : 2 * exp (-(δ ^ 2 / 8) * (n : ℝ)) ≤ 2 * exp (-cBound δ * (n : ℝ)) := by linarith
  unfold mBound
  have e : (2 * (2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4)) + 2) * exp (-cBound δ * (n : ℝ))
      = 2 * ((2 * exp (δ ^ 2 / 512) * (24 / (δ ^ 2 / 512) ^ 4)) * exp (-cBound δ * (n : ℝ)))
        + 2 * exp (-cBound δ * (n : ℝ)) := by ring
  rw [e]
  linarith [hX', hY']

lemma summable_badBound (δ : ℝ) (hδ : 0 < δ) :
    Summable (fun k : ℕ => mBound δ * exp (-cBound δ * ((k + 1 : ℕ) : ℝ))) := by
  have hcB : 0 < cBound δ := cBound_pos hδ
  have hr0 : 0 ≤ exp (-cBound δ) := (Real.exp_pos _).le
  have hr1 : exp (-cBound δ) < 1 := (Real.exp_lt_exp.2 (neg_lt_zero.2 hcB)).trans_eq Real.exp_zero
  have e : (fun k : ℕ => mBound δ * exp (-cBound δ * ((k + 1 : ℕ) : ℝ)))
      = fun k : ℕ => (mBound δ * exp (-cBound δ)) * (exp (-cBound δ)) ^ k := by
    funext k
    rw [show -cBound δ * ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) * (-cBound δ) by ring,
      Real.exp_nat_mul, pow_succ]
    ring
  rw [e]
  exact (summable_geometric_of_lt_one hr0 hr1).mul_left _

/-- Borel-Cantelli: almost surely the bad events on `[n, n+1]` occur for finitely many `n`. -/
lemma ae_eventually_not_bad (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ w ∂(brownianMotion (0 : ℝ)), ∀ᶠ k : ℕ in atTop, w ∉ badEvent δ (k + 1) := by
  refine ae_eventually_notMem ?_
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  calc ∑' k : ℕ, (brownianMotion (0 : ℝ)) (badEvent δ (k + 1))
      ≤ ∑' k : ℕ, ENNReal.ofReal (mBound δ * exp (-cBound δ * ((k + 1 : ℕ) : ℝ))) :=
        ENNReal.tsum_le_tsum fun k => badEvent_le δ hδ (k + 1) (by omega)
    _ = ENNReal.ofReal (∑' k : ℕ, mBound δ * exp (-cBound δ * ((k + 1 : ℕ) : ℝ))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by unfold mBound; positivity)
          (summable_badBound δ hδ)).symm

/-- On the complement of the bad events, the Brownian path is eventually `δ`-sublinear. -/
lemma eventually_abs_le_of_not_bad (δ : ℝ) (hδ : 0 < δ) (w : ContinuousPath ℝ)
    (hw : ∀ᶠ k : ℕ in atTop, w ∉ badEvent δ (k + 1)) :
    ∀ᶠ t : ℝ≥0 in atTop, |w t| ≤ δ * (t : ℝ) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hw
  have key : ∀ n : ℕ, K + 1 ≤ n → ∀ t : ℝ, (n : ℝ) ≤ t → t ≤ n + 1 → |pathR w t| ≤ δ * n := by
    intro n hnK t ht0 ht1
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hw' : w ∉ badEvent δ (k + 1) := hK k (by omega)
    have hup : ∀ j i : ℕ, i < 8 ^ j →
        |pathR w (((k + 1 : ℕ) : ℝ) + ((i : ℝ) + 1) / 8 ^ j) - pathR w (((k + 1 : ℕ) : ℝ) + (i : ℝ) / 8 ^ j)|
          ≤ δ * ((k + 1 : ℕ) : ℝ) / 16 * (1 / 2) ^ j := by
      intro j i hi
      have hnot : w ∉ levelEvent δ (k + 1) j i := fun h =>
        hw' (Or.inl (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, h⟩⟩))
      exact not_lt.1 hnot
    have hend : ¬ (δ * ((k + 1 : ℕ) : ℝ) / 2 < |pathR w ((k + 1 : ℕ) : ℝ)|) := fun h =>
      hw' (Or.inr h)
    have hθ0 : 0 ≤ δ * ((k + 1 : ℕ) : ℝ) / 16 :=
      div_nonneg (mul_nonneg hδ.le (Nat.cast_nonneg _)) (by norm_num)
    have hchain := chain_bound (pathR w) (continuous_pathR w) ((k + 1 : ℕ) : ℝ)
      (δ * ((k + 1 : ℕ) : ℝ) / 16) hθ0 hup t ht0 ht1
    have hend' := not_lt.1 hend
    have htri : |pathR w t| ≤ |pathR w t - pathR w ((k + 1 : ℕ) : ℝ)| + |pathR w ((k + 1 : ℕ) : ℝ)| := by
      have := abs_add_le (pathR w t - pathR w ((k + 1 : ℕ) : ℝ)) (pathR w ((k + 1 : ℕ) : ℝ))
      rwa [sub_add_cancel] at this
    linarith
  refine eventually_atTop.2 ⟨((K + 1 : ℕ) : ℝ≥0), fun t' ht' => ?_⟩
  have hT : ((K + 1 : ℕ) : ℝ) ≤ (t' : ℝ) := by exact_mod_cast ht'
  have ht0 : (0 : ℝ) ≤ (t' : ℝ) := t'.2
  have hnK : K + 1 ≤ ⌊(t' : ℝ)⌋₊ := Nat.le_floor hT
  have hfl : ((⌊(t' : ℝ)⌋₊ : ℕ) : ℝ) ≤ (t' : ℝ) := Nat.floor_le ht0
  have hfl2 : (t' : ℝ) ≤ ((⌊(t' : ℝ)⌋₊ : ℕ) : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have h := key ⌊(t' : ℝ)⌋₊ hnK (t' : ℝ) hfl hfl2
  have hpt : pathR w (t' : ℝ) = w t' := by simp [pathR]
  rw [hpt] at h
  have hδn : δ * ((⌊(t' : ℝ)⌋₊ : ℕ) : ℝ) ≤ δ * (t' : ℝ) := mul_le_mul_of_nonneg_left hfl hδ.le
  linarith

lemma lqgQ_sub_gamma_pos {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : 0 < HarmonicBalls.lqgQ γ - γ := by
  unfold HarmonicBalls.lqgQ
  have e : 2 / γ + γ / 2 - γ = (4 - γ ^ 2) / (2 * γ) := by
    field_simp
    ring
  rw [e]
  exact div_pos (by nlinarith) (by positivity)

/-- **Brownian negative drift** (Karatzas-Shreve, Chapter 2, Problem 9.3). For the standard Brownian motion
from `0` and every `c > 0`, almost surely `B_t - c t → -∞` as `t → ∞`. -/
theorem ae_brownian_sub_linear_tendsto_atBot {c : ℝ} (hc : 0 < c) :
    ∀ᵐ w ∂(brownianMotion (0 : ℝ)), Tendsto (fun t : ℝ≥0 => w t - c * (t : ℝ)) atTop atBot := by
  filter_upwards [ae_eventually_not_bad (c / 2) (half_pos hc)] with w hw
  have hb := eventually_abs_le_of_not_bad (c / 2) (half_pos hc) w hw
  rw [tendsto_atBot]
  intro b
  filter_upwards [hb, eventually_ge_atTop (Real.toNNReal (max 0 (-2 * b / c)))] with t h1 h2
  have h3 : max 0 (-2 * b / c) ≤ (t : ℝ) := Real.toNNReal_le_iff_le_coe.1 h2
  have h4 : -2 * b / c ≤ (t : ℝ) := (le_max_right _ _).trans h3
  have h5 : -2 * b ≤ c * (t : ℝ) := by
    have := (div_le_iff₀ hc).1 h4
    linarith
  have h6 := le_abs_self (w t)
  linarith

/-- **Brownian negative drift at `c = Q - γ`** (`HarmonicBalls.lqgQ`, Duplantier-Sheffield Definition 2.1):
for `0 < γ < 2` the drift `Q - γ` is positive, and `B_t - (Q - γ) t → -∞` almost surely. -/
theorem ae_brownian_lqgQ_drift_tendsto_atBot {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ w ∂(brownianMotion (0 : ℝ)),
      Tendsto (fun t : ℝ≥0 => w t - (HarmonicBalls.lqgQ γ - γ) * (t : ℝ)) atTop atBot :=
  ae_brownian_sub_linear_tendsto_atBot (lqgQ_sub_gamma_pos hγ0 hγ2)

#print axioms ae_brownian_sub_linear_tendsto_atBot
#print axioms ae_brownian_lqgQ_drift_tendsto_atBot

end MatedCRT.S2x.BrownianDrift
