import MatedCRT.FirstPass.Derived.BrownianTubeChain
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.WaypointProofTemplate

/-!
# Planar Brownian motion follows the moved polar template

The tube estimate (step A3 of the support-theorem argument) behind the Brownian disconnection
estimate in the proof of the invariance principle of Gwynne-Miller-Sheffield (Lemma 3.14 of
arXiv:1807.07515).

For `‖x‖ = r`, let `g t := movedTemplate 0 r (arg x) (t / r²)` be the polar template of the
cellular embedding, moved to start at `x` and run on the time scale `r²`. Planar Brownian motion
started from `x` stays within `r / 2000` of `g` up to time `r²` with probability at least a
constant `templateTubeConst > 0` that depends neither on `r` nor on `x`.

* `oneStepConst_pow_le_planarBrownianMotion_movedTemplate`: the general form, with `N` windows of
  half-side `3 a r / 4` and duration `r² / N`, for `29 / N ≤ a / 16` and
  `√2 · 3a/4 + √2 · a/16 + 29 / N ≤ κ`; the bound is `oneStepConst a (1 / N) ^ (2N)`, which does
  not depend on `r` by Brownian scaling (`oneStepConst_smul`).
* `templateTubeConst_le_planarBrownianMotion`: the case `N = 8192000000`, `a = 1/4000`,
  `κ = 1/2000`; `templateTubeConst_pos`: the constant is positive.

The template moves at speed at most `29 r` (`waypointProof_movedTemplate_lipschitz`) and starts at
`x` (`waypointProof_movedTemplate_zero`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
open HarmonicBalls MatedCRTHarmonic.Brownian MatedCRTHarmonic.CellularEmbedding

namespace MatedCRT

/-- **Tube along the moved polar template, general form.** For `r > 0`, `‖x‖ = r`, `N ≥ 1`
windows and `a > 0` with `29 / N ≤ a / 16` and `√2 · 3a/4 + √2 · a/16 + 29 / N ≤ κ`, planar
Brownian motion started from `x` stays within `κ r` of `t ↦ movedTemplate 0 r (arg x) (t / r²)`
up to time `r²` with probability at least `oneStepConst a (1 / N) ^ (2N)`. -/
theorem oneStepConst_pow_le_planarBrownianMotion_movedTemplate {r : ℝ≥0} (hr : 0 < r)
    {N : ℕ} (hN : 0 < N) {a κ : ℝ} (ha : 0 < a) (h16 : 29 / (N : ℝ) ≤ a / 16)
    (hκ : Real.sqrt 2 * (3 * a / 4) + Real.sqrt 2 * (a / 16) + 29 / (N : ℝ) ≤ κ)
    {x : ℂ} (hx : ‖x‖ = r) :
    ENNReal.ofReal (oneStepConst a (1 / (N : ℝ≥0))) ^ (2 * N) ≤
      planarBrownianMotion x {ω | ∀ t ≤ r ^ 2,
        ‖ω t - movedTemplate 0 r (Complex.arg x) ((t : ℝ) / (r : ℝ) ^ 2)‖ < κ * r} := by
  have hr' : (0 : ℝ) < r := hr
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ≥0 → ℂ,
      g = fun t : ℝ≥0 => movedTemplate 0 r (Complex.arg x) ((t : ℝ) / (r : ℝ) ^ 2) := ⟨_, rfl⟩
  have hgt : ∀ t, g t = movedTemplate 0 r (Complex.arg x) ((t : ℝ) / (r : ℝ) ^ 2) := by
    intro t
    rw [hgdef]
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ≥0, Δ = r ^ 2 * (1 / (N : ℝ≥0)) := ⟨_, rfl⟩
  have hΔpos : 0 < Δ := by
    rw [hΔ]
    positivity
  have hΔR : (Δ : ℝ) = 1 / N * (r : ℝ) ^ 2 := by
    rw [hΔ]
    push_cast
    ring
  have hNΔ : (N : ℝ≥0) * Δ = r ^ 2 := by
    rw [hΔ, mul_comm, mul_assoc, one_div_mul_cancel hN0, mul_one]
  have hε : 0 < (r : ℝ) * a := mul_pos hr' ha
  have hc : oneStepConst ((r : ℝ) * a) Δ = oneStepConst a (1 / (N : ℝ≥0)) := by
    rw [hΔ]
    exact oneStepConst_smul hr.ne' a _
  -- the template moves by at most `29 r / N` over a window
  have hg : ∀ t u : ℝ≥0, t ≤ u → u ≤ t + Δ → ‖g t - g u‖ ≤ 29 * r / N := by
    intro t u htu hut
    have h1 : (t : ℝ) ≤ u := by exact_mod_cast htu
    have h2 : (u : ℝ) ≤ t + Δ := by exact_mod_cast hut
    have hr2 : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
    have habs : |(t : ℝ) / (r : ℝ) ^ 2 - (u : ℝ) / (r : ℝ) ^ 2| ≤ 1 / N := by
      rw [← sub_div, abs_div, abs_of_pos hr2, div_le_iff₀ hr2, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr h1)]
      linarith
    rw [hgt, hgt]
    calc ‖movedTemplate 0 r (Complex.arg x) ((t : ℝ) / (r : ℝ) ^ 2) -
          movedTemplate 0 r (Complex.arg x) ((u : ℝ) / (r : ℝ) ^ 2)‖
        ≤ 29 * r * |(t : ℝ) / (r : ℝ) ^ 2 - (u : ℝ) / (r : ℝ) ^ 2| :=
          MatedCRTHarmonic.CellFamily.waypointProof_movedTemplate_lipschitz 0 hr'.le _ _ _
      _ ≤ 29 * r * (1 / N) := by gcongr
      _ = 29 * r / N := by ring
  have hstepg : ∀ i : ℕ, ‖g (((i + 1 : ℕ) : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ)‖ ≤
      (r : ℝ) * a / 16 := by
    intro i
    rw [norm_sub_rev]
    refine (hg _ _ (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_succ i)) zero_le)
      (le_of_eq (by push_cast; ring))).trans ?_
    calc 29 * (r : ℝ) / N = r * (29 / N) := by ring
      _ ≤ r * (a / 16) := by gcongr
      _ = r * a / 16 := by ring
  have hy : ∀ i : ℕ, |(g (((i + 1 : ℕ) : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ)).re| ≤ (r : ℝ) * a / 16 ∧
      |(g (((i + 1 : ℕ) : ℝ≥0) * Δ) - g ((i : ℝ≥0) * Δ)).im| ≤ (r : ℝ) * a / 16 := fun i =>
    ⟨(Complex.abs_re_le_norm _).trans (hstepg i), (Complex.abs_im_le_norm _).trans (hstepg i)⟩
  -- the template starts at `x`
  have hg0 : g 0 = x := by
    have h := MatedCRTHarmonic.CellFamily.waypointProof_movedTemplate_zero (z := 0) (y₀ := x)
      (r := r) (by rw [sub_zero]; exact hx)
    rw [sub_zero] at h
    rw [hgt, NNReal.coe_zero, zero_div]
    exact h
  have hy0 : g (((0 : ℕ) : ℝ≥0) * Δ) = x := by
    rw [Nat.cast_zero, zero_mul, hg0]
  have hε16 : (0 : ℝ) < (r : ℝ) * a / 16 := by positivity
  have hx0re : |(x - g (((0 : ℕ) : ℝ≥0) * Δ)).re| < (r : ℝ) * a / 16 := by
    rw [hy0, sub_self, Complex.zero_re, abs_zero]
    exact hε16
  have hx0im : |(x - g (((0 : ℕ) : ℝ≥0) * Δ)).im| < (r : ℝ) * a / 16 := by
    rw [hy0, sub_self, Complex.zero_im, abs_zero]
    exact hε16
  have hx0re' : |(x - g 0).re| < (r : ℝ) * a / 16 := by
    rw [hg0, sub_self, Complex.zero_re, abs_zero]
    exact hε16
  have hx0im' : |(x - g 0).im| < (r : ℝ) * a / 16 := by
    rw [hg0, sub_self, Complex.zero_im, abs_zero]
    exact hε16
  have hlow := ofReal_oneStepConst_pow_le_planarBrownianMotion_tubeChain hε hΔpos N x
    (fun i => g ((i : ℝ≥0) * Δ)) hy hx0re hx0im
  rw [hc] at hlow
  have hκ' : Real.sqrt 2 * (3 * ((r : ℝ) * a) / 4) + Real.sqrt 2 * ((r : ℝ) * a / 16) +
      29 * (r : ℝ) / N ≤ κ * r := by
    calc _ = (r : ℝ) * (Real.sqrt 2 * (3 * a / 4) + Real.sqrt 2 * (a / 16) + 29 / N) := by ring
      _ ≤ (r : ℝ) * κ := by gcongr
      _ = κ * r := by ring
  have hincl := tubeChain_inter_subset_tube (ε := (r : ℝ) * a) (Δ := Δ) hN (g := g)
    (L := 29 * r / N) (κ := κ * r) hg hκ' hx0re' hx0im'
  refine hlow.trans (measure_mono_ae ?_)
  filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω h0 hω
  have hmem := hincl ⟨hω, h0⟩
  simp only [mem_ofPred_eq] at hmem ⊢
  intro t ht
  have h := hmem t (by rw [hNΔ]; exact ht)
  rw [hgt] at h
  exact h

/-- The constant of the tube estimate around the moved polar template:
`oneStepConst (1/4000) (1/N) ^ (2N)` with `N = 8192000000` windows. -/
noncomputable def templateTubeConst : ℝ≥0∞ :=
  ENNReal.ofReal (oneStepConst (1 / 4000) (1 / ((8192000000 : ℕ) : ℝ≥0))) ^ (2 * 8192000000)

/-- The constant of the tube estimate is positive. -/
theorem templateTubeConst_pos : 0 < templateTubeConst := by
  have h : 0 < oneStepConst (1 / 4000) (1 / ((8192000000 : ℕ) : ℝ≥0)) := by
    refine oneStepConst_pos (by norm_num) (by positivity) ?_
    push_cast
    norm_num
  exact pos_iff_ne_zero.mpr (pow_ne_zero _ (ENNReal.ofReal_pos.mpr h).ne')

/-- **Tube along the moved polar template.** For `r > 0` and `‖x‖ = r`, planar Brownian motion
started from `x` stays within `r / 2000` of `t ↦ movedTemplate 0 r (arg x) (t / r²)` up to time
`r²` with probability at least `templateTubeConst`, uniformly in `r` and `x`. -/
theorem templateTubeConst_le_planarBrownianMotion {r : ℝ≥0} (hr : 0 < r) {x : ℂ}
    (hx : ‖x‖ = r) :
    templateTubeConst ≤
      planarBrownianMotion x {ω | ∀ t ≤ r ^ 2,
        ‖ω t - movedTemplate 0 r (Complex.arg x) ((t : ℝ) / (r : ℝ) ^ 2)‖ < r / 2000} := by
  have hs : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h := oneStepConst_pow_le_planarBrownianMotion_movedTemplate hr
    (N := 8192000000) (by norm_num) (a := 1 / 4000) (κ := 1 / 2000) (by norm_num)
    (by push_cast; norm_num) (by push_cast; nlinarith [hs, Real.sqrt_nonneg 2]) hx
  have hset : {ω : ContinuousPath ℂ | ∀ t ≤ r ^ 2,
      ‖ω t - movedTemplate 0 r (Complex.arg x) ((t : ℝ) / (r : ℝ) ^ 2)‖ < 1 / 2000 * r} =
      {ω | ∀ t ≤ r ^ 2,
        ‖ω t - movedTemplate 0 r (Complex.arg x) ((t : ℝ) / (r : ℝ) ^ 2)‖ < r / 2000} := by
    ext ω
    simp only [mem_ofPred_eq, one_div_mul_eq_div]
  rw [hset] at h
  exact h

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.oneStepConst_pow_le_planarBrownianMotion_movedTemplate
#print axioms MatedCRT.templateTubeConst_pos
#print axioms MatedCRT.templateTubeConst_le_planarBrownianMotion
