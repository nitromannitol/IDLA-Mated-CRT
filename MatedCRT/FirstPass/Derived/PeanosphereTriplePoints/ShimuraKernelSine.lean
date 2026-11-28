import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A lower bound for the one-dimensional Dirichlet heat kernel of an interval

The Dirichlet heat kernel `q_s(u, v) = LQGMetric.HeatSq.intervalDirKernel a L s u v` of the interval
`(a, a + L)` has the sine series
`q_s(u, v) = (2 / L) ∑_{k ≥ 1} e^{-π² k² s / (2 L²)} sin(π k (u - a) / L) sin(π k (v - a) / L)`
(`LQGMetric.HeatSq.hasSum_intervalDirKernel_sine`).  When `r = e^{-π² s / (2 L²)} ≤ 1 / 4` the
first mode dominates: together with `|sin (k θ)| ≤ k sin θ` for `θ ∈ [0, π]` this gives a lower
bound by the first mode alone, for `v` in the middle half of the interval.

## Main results

* `intervalDirKernel_ge_firstMode`: `(1 / L) r sin (π (u - a) / L) ≤ q_s(u, v)` for
  `u ∈ [a, a + L]` and `v ∈ [a + L / 4, a + 3 L / 4]`.
* `intervalDirKernel_ge_linear`: `(2 / L²) r (u - a) ≤ q_s(u, v)` for `u ∈ [a, a + L / 2]`.
-/

set_option autoImplicit false

open Real

namespace MatedCRT.PeanosphereTriplePoints

/-- For `sin θ ≥ 0` one has `|sin (n θ)| ≤ n sin θ`. -/
lemma abs_sin_nat_mul_le {θ : ℝ} (h : 0 ≤ Real.sin θ) (n : ℕ) :
    |Real.sin (n * θ)| ≤ n * Real.sin θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : Real.sin (((n + 1 : ℕ) : ℝ) * θ) =
        Real.sin (n * θ) * Real.cos θ + Real.cos (n * θ) * Real.sin θ := by
      rw [← Real.sin_add]; congr 1; push_cast; ring
    rw [e]
    have h1 := abs_cos_le_one θ
    have h2 := abs_cos_le_one ((n : ℝ) * θ)
    calc |Real.sin (n * θ) * Real.cos θ + Real.cos (n * θ) * Real.sin θ|
        ≤ |Real.sin (n * θ) * Real.cos θ| + |Real.cos (n * θ) * Real.sin θ| := abs_add_le _ _
      _ = |Real.sin (n * θ)| * |Real.cos θ| + |Real.cos (n * θ)| * Real.sin θ := by
          rw [abs_mul, abs_mul, abs_of_nonneg h]
      _ ≤ (n * Real.sin θ) * 1 + 1 * Real.sin θ :=
          add_le_add (mul_le_mul ih h1 (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) h))
            (mul_le_mul_of_nonneg_right h2 h)
      _ = ((n + 1 : ℕ) : ℝ) * Real.sin θ := by push_cast; ring

/-- On `[π / 4, 3 π / 4]` the sine is at least `7 / 10`. -/
lemma seven_tenths_le_sin {φ : ℝ} (h1 : π / 4 ≤ φ) (h2 : φ ≤ 3 * π / 4) :
    7 / 10 ≤ Real.sin φ := by
  have hq : (7 : ℝ) / 10 < Real.sin (π / 4) := by
    rw [Real.sin_pi_div_four]
    have : (7 : ℝ) / 5 < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  have hp := Real.pi_pos
  rcases le_total φ (π / 2) with h | h
  · have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h h1
    linarith
  · have e : Real.sin φ = Real.sin (π - φ) := (Real.sin_pi_sub φ).symm
    have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith : π - φ ≤ π / 2)
      (by linarith : π / 4 ≤ π - φ)
    linarith

/-- The summands beyond the first two modes: for `0 ≤ r ≤ 1 / 4`,
`(n + 2) r ^ ((n + 2) ^ 2) ≤ r (1 / 32) ^ (n + 1)`. -/
lemma pow_sq_mul_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 4) (n : ℕ) :
    r ^ ((n + 2) ^ 2) * ((n : ℝ) + 2) ≤ r * (1 / 32 : ℝ) ^ (n + 1) := by
  have hr1 : r ≤ 1 := by linarith
  have e : r ^ ((n + 2) ^ 2) = r * (r ^ 3) ^ (n + 1) * r ^ (n ^ 2 + n) := by
    rw [show (n + 2) ^ 2 = 1 + 3 * (n + 1) + (n ^ 2 + n) by ring, pow_add, pow_add, pow_mul,
      pow_one]
  have h3 : r ^ 3 ≤ 1 / 64 := by
    calc r ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hr0 hr 3
      _ = 1 / 64 := by norm_num
  have h4 : (r ^ 3) ^ (n + 1) ≤ (1 / 64 : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) h3 _
  have h5 : r ^ (n ^ 2 + n) ≤ 1 := pow_le_one₀ hr0 hr1
  have h6 : ((n : ℝ) + 2) ≤ 2 ^ (n + 1) := by
    have : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
    have : n + 2 ≤ 2 ^ (n + 1) := this
    exact_mod_cast this
  have h7 : r ^ ((n + 2) ^ 2) ≤ r * (1 / 64 : ℝ) ^ (n + 1) := by
    rw [e]
    calc r * (r ^ 3) ^ (n + 1) * r ^ (n ^ 2 + n) ≤ r * (1 / 64 : ℝ) ^ (n + 1) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h4 hr0) h5 (by positivity) (by positivity)
      _ = r * (1 / 64 : ℝ) ^ (n + 1) := by ring
  calc r ^ ((n + 2) ^ 2) * ((n : ℝ) + 2)
      ≤ (r * (1 / 64 : ℝ) ^ (n + 1)) * 2 ^ (n + 1) :=
        mul_le_mul h7 h6 (by positivity) (by positivity)
    _ = r * ((1 / 64 : ℝ) ^ (n + 1) * 2 ^ (n + 1)) := by ring
    _ = r * (1 / 32 : ℝ) ^ (n + 1) := by rw [← mul_pow]; norm_num

/-- **The first sine mode dominates the Dirichlet heat kernel of an interval.**  If
`exp (-(π² / (2 L²)) s) ≤ 1 / 4`, `u ∈ [a, a + L]` and `v ∈ [a + L / 4, a + 3 L / 4]`, then
`(1 / L) r sin (π (u - a) / L) ≤ q_s(u, v)` with `r = exp (-(π² / (2 L²)) s)`. -/
theorem intervalDirKernel_ge_firstMode {a L s u v : ℝ} (hL : 0 < L) (hs : 0 < s)
    (hr : Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * s) ≤ 1 / 4)
    (hu : a ≤ u) (hu' : u ≤ a + L) (hv : a + L / 4 ≤ v) (hv' : v ≤ a + 3 * L / 4) :
    1 / L * Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * s) * Real.sin (Real.pi * (u - a) / L) ≤
      LQGMetric.HeatSq.intervalDirKernel a L s u v := by
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * s) := ⟨_, rfl⟩
  rw [← hrdef] at hr ⊢
  have hr0 : 0 < r := by rw [hrdef]; exact Real.exp_pos _
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.pi * (u - a) / L := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = Real.pi * (v - a) / L := ⟨_, rfl⟩
  rw [← hθ]
  have hpi := Real.pi_pos
  have hθ0 : 0 ≤ θ := by rw [hθ]; apply div_nonneg _ hL.le; apply mul_nonneg hpi.le; linarith
  have hθ1 : θ ≤ π := by
    rw [hθ, div_le_iff₀ hL]; nlinarith
  have hsθ : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθ1
  have hφ1 : π / 4 ≤ φ := by
    rw [hφ, le_div_iff₀ hL]; nlinarith
  have hφ2 : φ ≤ 3 * π / 4 := by
    rw [hφ, div_le_iff₀ hL]; nlinarith
  have hsφ := seven_tenths_le_sin hφ1 hφ2
  have hmd : ∀ k : ℕ, LQGMetric.HeatSq.modeDecay L s k = r ^ (k ^ 2) := by
    intro k
    rw [hrdef, ← Real.exp_nat_mul]
    unfold LQGMetric.HeatSq.modeDecay
    congr 1; push_cast; ring
  have hsu : ∀ k : ℕ, LQGMetric.HeatSq.sinMode a L k u = Real.sin (k * θ) := by
    intro k; unfold LQGMetric.HeatSq.sinMode; rw [hθ]; congr 1; ring
  have hsv : ∀ k : ℕ, LQGMetric.HeatSq.sinMode a L k v = Real.sin (k * φ) := by
    intro k; unfold LQGMetric.HeatSq.sinMode; rw [hφ]; congr 1; ring
  have h := LQGMetric.HeatSq.hasSum_intervalDirKernel_sine (a := a) hs hL u v
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℝ, F = fun k : ℕ =>
      2 / L * (r ^ (k ^ 2) * (Real.sin (k * θ) * Real.sin (k * φ))) := ⟨_, rfl⟩
  have hfe : (fun k : ℕ => 2 / L * (LQGMetric.HeatSq.modeDecay L s k *
      (LQGMetric.HeatSq.sinMode a L k u * LQGMetric.HeatSq.sinMode a L k v))) = F := by
    funext k; rw [hFdef]; simp only [hmd, hsu, hsv]
  rw [hfe] at h
  have h2 := (hasSum_nat_add_iff' 2).mpr h
  -- geometric majorant
  have hg : HasSum (fun n : ℕ => (1 / 32 : ℝ) ^ (n + 1)) (1 / 31) := by
    have := (hasSum_geometric_of_lt_one (r := (1 / 32 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 32)
    convert this using 1
    · funext n; ring
    · norm_num
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = 2 / L * r * Real.sin θ := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hG := hg.mul_left (-m)
  have hpt : ∀ n : ℕ, -m * (1 / 32 : ℝ) ^ (n + 1) ≤ F (n + 2) := by
    intro n
    rw [hFdef]
    simp only
    have hp : |Real.sin (((n + 2 : ℕ) : ℝ) * θ) * Real.sin (((n + 2 : ℕ) : ℝ) * φ)| ≤
        ((n : ℝ) + 2) * Real.sin θ := by
      rw [abs_mul]
      calc |Real.sin (((n + 2 : ℕ) : ℝ) * θ)| * |Real.sin (((n + 2 : ℕ) : ℝ) * φ)|
          ≤ (((n + 2 : ℕ) : ℝ) * Real.sin θ) * 1 :=
            mul_le_mul (abs_sin_nat_mul_le hsθ _) (abs_sin_le_one _) (abs_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) hsθ)
        _ = ((n : ℝ) + 2) * Real.sin θ := by push_cast; ring
    have hp1 := (abs_le.mp hp).1
    have hkey := pow_sq_mul_le hr0.le (by linarith) n
    have hA : (0 : ℝ) ≤ 2 / L := by positivity
    have hpow : 0 ≤ r ^ ((n + 2) ^ 2) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hp1 hpow
    have h3 : r ^ ((n + 2) ^ 2) * (((n : ℝ) + 2) * Real.sin θ) ≤
        r * (1 / 32 : ℝ) ^ (n + 1) * Real.sin θ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkey hsθ
    have h4 := mul_le_mul_of_nonneg_left (show -(r * (1 / 32 : ℝ) ^ (n + 1) * Real.sin θ) ≤
      r ^ ((n + 2) ^ 2) * (Real.sin (((n + 2 : ℕ) : ℝ) * θ) *
        Real.sin (((n + 2 : ℕ) : ℝ) * φ)) by linarith) hA
    have e : -m * (1 / 32 : ℝ) ^ (n + 1) =
        2 / L * (-(r * (1 / 32 : ℝ) ^ (n + 1) * Real.sin θ)) := by rw [hm]; ring
    rw [e]; exact h4
  have hle := hasSum_le hpt hG h2
  have hsum2 : ∑ i ∈ Finset.range 2, F i = F 1 := by
    simp [Finset.sum_range_succ, hFdef]
  rw [hsum2] at hle
  have hF1 : F 1 = m * Real.sin φ := by
    rw [hFdef, hm]; simp only [Nat.cast_one, one_mul, one_pow]; ring
  have hmul := mul_le_mul_of_nonneg_left hsφ hm0
  have e1 : 1 / L * r * Real.sin θ = m / 2 := by rw [hm]; ring
  rw [e1]
  linarith

/-- **Linear lower bound for the Dirichlet heat kernel of an interval near its left end.**  Under
the hypotheses of `intervalDirKernel_ge_firstMode`, with `u ≤ a + L / 2`,
`(2 / L²) r (u - a) ≤ q_s(u, v)`, where `r = exp (-(π² / (2 L²)) s)`. -/
theorem intervalDirKernel_ge_linear {a L s u v : ℝ} (hL : 0 < L) (hs : 0 < s)
    (hr : Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * s) ≤ 1 / 4)
    (hu : a ≤ u) (hu' : u ≤ a + L / 2) (hv : a + L / 4 ≤ v) (hv' : v ≤ a + 3 * L / 4) :
    2 / L ^ 2 * Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * s) * (u - a) ≤
      LQGMetric.HeatSq.intervalDirKernel a L s u v := by
  refine le_trans ?_ (intervalDirKernel_ge_firstMode hL hs hr hu (by linarith) hv hv')
  have hpi := Real.pi_pos
  have hr0 := Real.exp_pos (-(Real.pi ^ 2 / (2 * L ^ 2)) * s)
  have hθ0 : 0 ≤ Real.pi * (u - a) / L := by
    apply div_nonneg _ hL.le; apply mul_nonneg hpi.le; linarith
  have hθ1 : Real.pi * (u - a) / L ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hL]; nlinarith
  have hsin := Real.mul_le_sin hθ0 hθ1
  have e : 2 / L ^ 2 * Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * s) * (u - a) =
      1 / L * Real.exp (-(Real.pi ^ 2 / (2 * L ^ 2)) * s) *
        (2 / Real.pi * (Real.pi * (u - a) / L)) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hsin (by positivity)

end MatedCRT.PeanosphereTriplePoints
