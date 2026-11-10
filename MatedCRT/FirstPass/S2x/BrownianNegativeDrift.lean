import MatedCRT.Defs.QuantumCone
import MarkovProcess.Examples.BrownianMotion
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic

/-!
# Ordinary Brownian motion has negative drift (fp-S2x-brownian-drift, z2)

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

end MatedCRT.S2x.BrownianDrift
