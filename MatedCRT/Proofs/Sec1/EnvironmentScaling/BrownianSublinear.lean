import Mathlib

/-!
# Real-time sublinear growth of Brownian motion (the `hsub` premise)

Component of `notes/env-steps/env-steps.tex:243-250`.  For a Brownian motion `B` on `ℝ≥0` with
measurable coordinates, almost surely `B t / t → 0` as `t → ∞` through the reals, the path being read
at `t.toNNReal`.  The conclusion `ae_tendsto_div_real_of_gaussianBandStep` is exactly the premise
`hsub` of `MatedCRT.Sec1.exists_measurable_referenceConeConditionedPath`
(`CanonicalConeIdentification.lean`).

Route.  The only probabilistic input is the Gaussian maximal estimate for the path on a horizon,
retained as the named Step `GaussianBandStep B P` (env-steps.tex:247-248, "the reflection bound for
the maximum").  Everything else is proved here:

* `measure_bandExceed_le` and `tsum_measure_bandExceed_ne_top`: for a band level `c > 0` the exceptional
  events `bandExceed B c n` (the path leaves `|B s - B 0| < c (n+1)` on `[0, n+1]`) have probabilities
  bounded by `4 exp(-c² (n+1) / 32)`, which is summable in `n`;
* `ae_eventually_not_mem_bandExceed`: Borel–Cantelli (`MeasureTheory.ae_eventually_notMem`);
* `tendsto_div_of_eventually_band`: deterministic interpolation, for `t ≥ 1` and `n = ⌊t⌋₊` one has
  `t ∈ [0, n+1]` and `n + 1 ≤ 2 t`;
* `ae_tendsto_div_real_of_gaussianBandStep`: the assembly over the countably many levels `(k+1)⁻¹`.

No unit-interval interpolation premise and no Gaussian tail are assumed beyond the named Step.  The
exceptional sets are explicit: `bandExceed B c n` and the Borel–Cantelli set they generate.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT.Sec1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Named Step: the Gaussian maximal estimate for the path on a horizon.**  For every horizon
`T` and every width `a > 0`, the probability that `|B s - B 0| ≥ a` for some `s ≤ T` is at most
`4 exp(-a² / (32 T))`.  This is the reflection-type bound for the maximum of
`notes/env-steps/env-steps.tex:247-248`.  Its Lean proof for `ProbabilityTheory.IsBrownianReal B P`
with measurable coordinates is `LatticeProb.measure_exists_abs_sub_ge_le`
(lattice-probability, `LatticeProb/Prob/BrownianMax.lean:247`), which is not importable at the
repository's pin: `LatticeProb.Prob.BrownianTail` fails to build (`BrownianTail.lean:120:41`).  It
is therefore carried as an explicit hypothesis and not claimed. -/
def GaussianBandStep (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (T : ℝ≥0) (a : ℝ), 0 < a →
    P {ω | ∃ s : ℝ≥0, s ≤ T ∧ a ≤ |B s ω - B 0 ω|} ≤
      4 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (32 * (T : ℝ)))))

/-- Deterministic interpolation of band bounds on the naturals.  If for every level `k` the
oscillation `|f s - f 0|` on `[0, n+1]` is below `(k+1)⁻¹ (n+1)` for all large `n`, then
`f t / t → 0` as `t → ∞` in `ℝ`. -/
theorem tendsto_div_of_eventually_band (f : ℝ → ℝ)
    (hf : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ (n : ℝ) + 1 →
      |f s - f 0| < (1 / ((k : ℝ) + 1)) * ((n : ℝ) + 1)) :
    Tendsto (fun t : ℝ => f t / t) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < δ / 4 by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hf k)
  have hεpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hε
  refine Filter.eventually_atTop.mpr ⟨max (max (N : ℝ) 1) (|f 0| / ε), fun t ht => ?_⟩
  show dist (f t / t) 0 < δ
  have hNt : (N : ℝ) ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht1 : 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have hf0 : |f 0| / ε ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := by linarith
  have hnt : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
  have htn : t ≤ ((⌊t⌋₊ : ℕ) : ℝ) + 1 := (Nat.lt_floor_add_one t).le
  have hNn : N ≤ ⌊t⌋₊ := Nat.le_floor hNt
  have hband : |f t - f 0| < ε * (((⌊t⌋₊ : ℕ) : ℝ) + 1) := hN ⌊t⌋₊ hNn t ht0.le htn
  have h1 : ε * (((⌊t⌋₊ : ℕ) : ℝ) + 1) ≤ ε * (2 * t) :=
    mul_le_mul_of_nonneg_left (by linarith) hεpos.le
  have h2 : |f t - f 0| < 2 * ε * t := by linarith [hband, h1]
  have h3 : |f 0| ≤ ε * t := by
    have := (div_le_iff₀ hεpos).mp hf0
    linarith
  have h4 : |f t| < 3 * ε * t := by
    have h2' := abs_lt.mp h2
    have h3' := abs_le.mp h3
    exact abs_lt.mpr ⟨by linarith [h2'.1, h3'.1], by linarith [h2'.2, h3'.2]⟩
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos ht0, div_lt_iff₀ ht0]
  have hε4 : ε < δ / 4 := hk
  have h5 : 0 < (δ - 3 * ε) * t := mul_pos (by linarith) ht0
  nlinarith [h4, h5]

/-- The exceptional event of the band estimate at level `c` and index `n`: for some `s ∈ [0, n+1]`
the path satisfies `c (n+1) ≤ |B s - B 0|`. -/
def bandExceed (B : ℝ≥0 → Ω → ℝ) (c : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃ s : ℝ≥0, s ≤ (n : ℝ≥0) + 1 ∧ c * ((n : ℝ) + 1) ≤ |B s ω - B 0 ω|}

/-- Gaussian bound on the band event: `P (bandExceed B c n) ≤ 4 q^(n+1)` with `q = exp(-c²/32)`,
from the named Step `GaussianBandStep` at horizon `n+1` and width `c (n+1)`. -/
theorem measure_bandExceed_le {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hstep : GaussianBandStep B P) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    P (bandExceed B c n) ≤ 4 * ENNReal.ofReal (Real.exp (-(c ^ 2 / 32)) ^ (n + 1)) := by
  have hpos : 0 < c * ((n : ℝ) + 1) := mul_pos hc (by positivity)
  have h := hstep ((n : ℝ≥0) + 1) (c * ((n : ℝ) + 1)) hpos
  have hexp : Real.exp (-((c * ((n : ℝ) + 1)) ^ 2 / (32 * (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ))))
      = Real.exp (-(c ^ 2 / 32)) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
  rw [← hexp]
  exact h

/-- The band events are summable in `n`: the Gaussian bounds decay geometrically. -/
theorem tsum_measure_bandExceed_ne_top {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hstep : GaussianBandStep B P) {c : ℝ} (hc : 0 < c) :
    ∑' n : ℕ, P (bandExceed B c n) ≠ ⊤ := by
  have hq0 : 0 ≤ Real.exp (-(c ^ 2 / 32)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(c ^ 2 / 32)) < 1 := by
    have h0 : -(c ^ 2 / 32) < 0 := by
      have : 0 < c ^ 2 := pow_pos hc 2
      linarith
    have := Real.exp_lt_exp.mpr h0
    rwa [Real.exp_zero] at this
  have hsumm : Summable (fun n : ℕ => Real.exp (-(c ^ 2 / 32)) ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq1)
  have hle : ∑' n : ℕ, P (bandExceed B c n)
      ≤ 4 * ENNReal.ofReal (∑' n : ℕ, Real.exp (-(c ^ 2 / 32)) ^ (n + 1)) := by
    calc ∑' n : ℕ, P (bandExceed B c n)
        ≤ ∑' n : ℕ, 4 * ENNReal.ofReal (Real.exp (-(c ^ 2 / 32)) ^ (n + 1)) :=
          ENNReal.tsum_le_tsum fun n => measure_bandExceed_le hstep hc n
      _ = 4 * ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(c ^ 2 / 32)) ^ (n + 1)) :=
          ENNReal.tsum_mul_left
      _ = 4 * ENNReal.ofReal (∑' n : ℕ, Real.exp (-(c ^ 2 / 32)) ^ (n + 1)) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hle

/-- Borel–Cantelli step: almost surely, for each level `c > 0`, the path eventually avoids
`bandExceed B c n`. -/
theorem ae_eventually_not_mem_bandExceed {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hstep : GaussianBandStep B P) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ω ∉ bandExceed B c n :=
  ae_eventually_notMem (tsum_measure_bandExceed_ne_top hstep hc)

/-- The band statement at level `(k+1)⁻¹`, almost surely: for all large `n` the path satisfies
`|B s - B 0| < (k+1)⁻¹ (n+1)` for every `s ∈ [0, n+1]`. -/
theorem ae_eventually_band {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hstep : GaussianBandStep B P) (k : ℕ) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ s : ℝ≥0, s ≤ (n : ℝ≥0) + 1 →
      |B s ω - B 0 ω| < (1 / ((k : ℝ) + 1)) * ((n : ℝ) + 1) := by
  have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  filter_upwards [ae_eventually_not_mem_bandExceed hstep hc] with ω hω
  filter_upwards [hω] with n hn
  intro s hs
  by_contra hcon
  exact hn (by simp only [bandExceed, Set.mem_ofPred_eq]; exact ⟨s, hs, not_lt.mp hcon⟩)

/-- **Real-time sublinear growth of Brownian motion, conditional on the named Step.**  Given the
Gaussian maximal estimate `GaussianBandStep B P`, almost surely `B t / t → 0` as `t → ∞` through the
reals.  This is the premise `hsub` of `exists_measurable_referenceConeConditionedPath`. -/
theorem ae_tendsto_div_real_of_gaussianBandStep {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hstep : GaussianBandStep B P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => B t.toNNReal ω / t) atTop (𝓝 0) := by
  filter_upwards [ae_all_iff.mpr (fun k => ae_eventually_band hstep k)] with ω hω
  refine tendsto_div_of_eventually_band (fun t : ℝ => B t.toNNReal ω) (fun k => ?_)
  filter_upwards [hω k] with n hn
  intro s hs0 hsn
  have hle : s.toNNReal ≤ (n : ℝ≥0) + 1 := by
    rw [Real.toNNReal_le_iff_le_coe]
    push_cast
    exact hsn
  simp only [Real.toNNReal_zero]
  exact hn _ hle

end MatedCRT.Sec1
