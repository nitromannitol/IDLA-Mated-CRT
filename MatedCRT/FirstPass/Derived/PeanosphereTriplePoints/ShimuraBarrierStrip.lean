import MatedCRT.FirstPass.Derived.BrownianTubeChain

/-!
# A uniform lower bound for planar Brownian motion in a vertical strip

For `0 < α ≤ β < H`, a vertical window `(y₁, y₂) ⊂ (0, H)` and a time `T > 0`, planar Brownian
motion started at any point whose real part lies in `[α, β]` keeps its real part in `(0, H)` up to
time `T` and ends with real part in `(y₁, y₂)` with probability at least some `p > 0` that does
not depend on the starting point.

The proof follows the straight segment from the start `x` to the real point `(y₁ + y₂) / 2` inside
a tube chain.  The real parts of the segment lie at distance at least `m` from `0` and `H`, with
`m` depending only on the data, so a chain of windows of width `ε = m / 4` with step `T / N` keeps
the path in the strip and ends it in the target window.  The lower bound on the chain is
`ofReal_oneStepConst_pow_le_planarBrownianMotion_tubeChain`, which does not depend on the start,
and the tube estimate is `tubeChain_inter_subset_tube`.

## Main result

* `exists_pos_le_planarBrownianMotion_reStrip`: the uniform positivity statement.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls MatedCRTHarmonic.Brownian

namespace MatedCRT.PeanosphereTriplePoints

/-- **Uniform positivity of the strip event.** Let `0 < α ≤ β < H`, `0 < y₁ < y₂ < H` and `T > 0`.
There is `p > 0` such that planar Brownian motion started at any `x` with `x.re ∈ [α, β]` has the
real part of its path in `(0, H)` on `[0, T]` and in `(y₁, y₂)` at time `T`, with probability at
least `p`. -/
theorem exists_pos_le_planarBrownianMotion_reStrip {H α β y₁ y₂ : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hβ : β < H) (hy₁ : 0 < y₁) (hy₁₂ : y₁ < y₂) (hy₂ : y₂ < H) {T : ℝ≥0} (hT : 0 < T) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ x : ℂ, x.re ∈ Set.Icc α β →
      p ≤ planarBrownianMotion x
        {ω | (∀ s ≤ T, 0 < (ω s).re ∧ (ω s).re < H) ∧ (ω T).re ∈ Set.Ioo y₁ y₂} := by
  have hH : 0 < H := hα.trans_le (hαβ.trans hβ.le)
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  -- the margin from the boundary
  obtain ⟨m, hm0, hmα, hmy₁, hmβ, hmy₂, hmy⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ α ∧ m ≤ y₁ ∧ m ≤ H - β ∧
      m ≤ H - y₂ ∧ m ≤ (y₂ - y₁) / 2 :=
    ⟨min α (min y₁ (min (H - β) (min (H - y₂) ((y₂ - y₁) / 2)))),
      lt_min hα (lt_min hy₁ (lt_min (by linarith) (lt_min (by linarith) (by linarith)))),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))),
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _)))⟩
  set ε : ℝ := m / 4 with hεdef
  have hε : 0 < ε := by positivity
  -- the number of steps
  obtain ⟨N, hN⟩ := exists_nat_gt (max (16 * H / ε) (512 * (T : ℝ) / ε ^ 2))
  have hN1 : 16 * H / ε < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 512 * (T : ℝ) / ε ^ 2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN2
  have hN0 : 0 < N := by exact_mod_cast hNpos
  set Δ : ℝ≥0 := T / N with hΔdef
  have hΔreal : (Δ : ℝ) = T / N := by simp [hΔdef]
  have hΔpos : 0 < Δ := div_pos hT (by exact_mod_cast hN0)
  have hΔε : (Δ : ℝ) ≤ ε ^ 2 / 512 := by
    rw [hΔreal, div_le_div_iff₀ hNpos (by norm_num)]
    rw [div_lt_iff₀ (by positivity)] at hN2
    nlinarith
  have hNΔ : (N : ℝ≥0) * Δ = T := by
    apply NNReal.eq
    rw [NNReal.coe_mul, hΔreal]
    simp only [NNReal.coe_natCast]
    field_simp
  have hHN : H / N ≤ ε / 16 := by
    rw [div_le_div_iff₀ hNpos (by norm_num)]
    rw [div_lt_iff₀ hε] at hN1
    nlinarith
  refine ⟨ENNReal.ofReal (oneStepConst ε Δ) ^ (2 * N),
    ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (oneStepConst_pos hε hΔpos hΔε)) _, fun x hx => ?_⟩
  obtain ⟨hxα, hxβ⟩ := hx
  set ys : ℝ := (y₁ + y₂) / 2 with hysdef
  -- the straight curve
  set g : ℝ≥0 → ℂ := fun t => x + (((t : ℝ) / T : ℝ) : ℂ) * ((ys - x.re : ℝ) : ℂ) with hgdef
  have hg0 : g 0 = x := by simp [hgdef]
  have hgre : ∀ t : ℝ≥0, (g t).re = x.re + ((t : ℝ) / T) * (ys - x.re) := by
    intro t
    simp [hgdef]
  have hcabs : |ys - x.re| ≤ H := by
    rw [abs_le]
    constructor <;> linarith
  have hg : ∀ t u : ℝ≥0, t ≤ u → u ≤ t + Δ → ‖g t - g u‖ ≤ H / N := by
    intro t u htu hut
    have hdiff : g t - g u = ((((t : ℝ) - u) / T : ℝ) : ℂ) * ((ys - x.re : ℝ) : ℂ) := by
      simp only [hgdef]
      push_cast
      ring
    have htu' : (t : ℝ) ≤ u := by exact_mod_cast htu
    have hut' : (u : ℝ) ≤ t + Δ := by exact_mod_cast hut
    rw [hdiff, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_div, abs_of_nonneg hT'.le, abs_of_nonpos (by linarith)]
    calc (-((t : ℝ) - u)) / T * |ys - x.re| ≤ ((Δ : ℝ) / T) * H := by
          gcongr
          all_goals linarith
      _ = H / N := by
          rw [hΔreal]
          field_simp
  have hχ : ∀ i : ℕ, |((g (((i + 1 : ℕ) : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ))).re| ≤ ε / 16 ∧
      |((g (((i + 1 : ℕ) : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ))).im| ≤ ε / 16 := by
    intro i
    have hnorm : ‖g (((i + 1 : ℕ) : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ)‖ ≤ ε / 16 := by
      rw [norm_sub_rev]
      refine (hg _ _ ?_ ?_).trans hHN
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) (by positivity)
      · apply le_of_eq
        push_cast
        ring
    exact ⟨(Complex.abs_re_le_norm _).trans hnorm, (Complex.abs_im_le_norm _).trans hnorm⟩
  have hchain := ofReal_oneStepConst_pow_le_planarBrownianMotion_tubeChain hε hΔpos N x
    (fun i => g ((i : ℝ≥0) * Δ)) hχ (by simp [hg0, hε]) (by simp [hg0, hε])
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hκ : Real.sqrt 2 * (3 * ε / 4) + Real.sqrt 2 * (ε / 16) + H / N ≤ m := by
    have h1 : Real.sqrt 2 * (3 * ε / 4) ≤ 2 * (3 * ε / 4) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    have h2 : Real.sqrt 2 * (ε / 16) ≤ 2 * (ε / 16) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    linarith
  refine hchain.trans (measure_mono_ae ?_)
  filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω h0 hω
  have htube := tubeChain_inter_subset_tube hN0 (g := g) (L := H / N) (κ := m) hg hκ
    (x := x) (by rw [hg0]; simp [hε]) (by rw [hg0]; simp [hε]) ⟨hω, h0⟩
  rw [hNΔ] at htube
  have hrange : ∀ s : ℝ≥0, s ≤ T → m ≤ (g s).re ∧ (g s).re ≤ H - m := by
    intro s hs
    have hθ0 : (0 : ℝ) ≤ (s : ℝ) / T := by positivity
    have hθ1 : (s : ℝ) / T ≤ 1 := by
      rw [div_le_one hT']
      exact_mod_cast hs
    rw [hgre]
    constructor <;> nlinarith [mul_nonneg hθ0 (show 0 ≤ ys - m by simp only [hysdef]; linarith),
      mul_nonneg (sub_nonneg.mpr hθ1) (show 0 ≤ x.re - m by linarith),
      mul_nonneg hθ0 (show 0 ≤ H - m - ys by simp only [hysdef]; linarith),
      mul_nonneg (sub_nonneg.mpr hθ1) (show 0 ≤ H - m - x.re by linarith)]
  have hre : ∀ s : ℝ≥0, s ≤ T → |(ω s).re - (g s).re| < m := fun s hs => by
    have := htube s hs
    have h2 : (ω s - g s).re = (ω s).re - (g s).re := by simp
    rw [← h2]
    exact (Complex.abs_re_le_norm _).trans_lt this
  refine ⟨fun s hs => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := abs_lt.mp (hre s hs)
    obtain ⟨h3, h4⟩ := hrange s hs
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := abs_lt.mp (hre T le_rfl)
    have hgT : (g T).re = ys := by
      rw [hgre, div_self hT'.ne']
      ring
    rw [hgT] at h1 h2
    constructor <;> simp only [hysdef] at h1 h2 <;> linarith

end MatedCRT.PeanosphereTriplePoints
