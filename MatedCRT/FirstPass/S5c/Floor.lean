import MatedCRT.FirstPass.S5c.Scaling
import MatedCRT.FirstPass.S5c.Continuum
import MatedCRT.FirstPass.S5c.Superharmonic
import MatedCRT.FirstPass.S5c.Pole

/-!
# FIRST PASS, Lemma 5.3: uniform positive floor of the surplus on compact subsets (G-5-3 Section 1, eq. (5))

For one realization of the harmonic-ball family: `A_n(x) = w_t(x) + t R_n(x)`, `R_n = -w_{s_n} / s_n`, `s_n = t 2^{-n}`.
Every compact `K ⊆ Λ_t` admits an index `n` and a constant `b > 0` with `b ≤ A_n` on `K` (G-5-3, eq. (5)).
Pointwise: at `x ≠ 0` the value is eventually `w_t + t G > 0` (strict obstacle gap, `Λ_t ⊆ cluster`); at the pole it
blows up (`Pole.lean`). Monotone in `n` by mass scaling (`Scaling.lean`); compact cover (`Pole.lean`).
Realization-level hypotheses are named; the random quantifiers are handled in the wrapper.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Metric Filter Topology
open scoped Real
open _root_.HarmonicBalls

theorem surplus_floor_on_compact {μ : Measure ℂ} {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hsup : FPSuperharmonicOfLaplacianLE) {Λ : ℝ → Set ℂ}
    (hopen : ∀ s : ℝ, 0 < s → IsOpen (cluster μ ρ 0 s))
    (hLap : ∀ s : ℝ, 0 < s → ∃ μp : Measure ℂ, HasLaplacian (leastSupersolution μ ρ 0 s) μp 0 (ball 0 ρ))
    (hcont : ∀ s : ℝ, 0 < s → s ≤ t → ContinuousOn (leastSupersolution μ ρ 0 s) (ball 0 ρ))
    (hΛ : ∀ s : ℝ, 0 < s → s ≤ t → Λ s = interior (closure (cluster μ ρ 0 s)))
    (hmonoΛ : ∀ s u : ℝ, 0 < s → s ≤ u → Λ s ⊆ Λ u)
    (hint : ∀ x ∈ ball (0 : ℂ) ρ, x ≠ 0 → ∃ s₀ : ℝ, 0 < s₀ ∧ x ∉ Λ s₀)
    (hbb : ∀ x ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, 0 ≤ s →
      BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ ρ 0 s))
    (hGc : ContinuousOn (greenFunction (ball 0 ρ) 0) (ball 0 ρ \ {0}))
    (hGlow : ∀ r : ℝ, 0 < r → r < ρ / 2 → ∀ x ∈ sphere (0 : ℂ) r,
      (2 * π)⁻¹ * Real.log (ρ / 2 / r) ≤ greenFunction (ball 0 ρ) 0 x)
    (hΛc : Λ t ⊆ cluster μ ρ 0 t) (hΛball : Λ t ⊆ ball (0 : ℂ) ρ)
    {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty) (hKΛ : K ⊆ Λ t) :
    ∃ n : ℕ, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K,
      b ≤ leastSupersolution μ ρ 0 t x + t * (-(leastSupersolution μ ρ 0 (t * (1 / 2) ^ n) x) /
        (t * (1 / 2) ^ n)) := by
  set s : ℕ → ℝ := fun n => t * (1 / 2 : ℝ) ^ n with hs_def
  have hspos : ∀ n, 0 < s n := fun n => by
    simp only [hs_def]
    positivity
  have hsle : ∀ n : ℕ, s n ≤ t := fun n => by
    simp only [hs_def]
    exact mul_le_of_le_one_right ht.le (pow_le_one₀ (by norm_num) (by norm_num))
  set A : ℕ → ℂ → ℝ := fun n x => leastSupersolution μ ρ 0 t x +
    t * (-(leastSupersolution μ ρ 0 (s n) x) / s n) with hA_def
  -- continuity of `A n` on the open disk
  have hAc : ∀ n, ContinuousOn (A n) (ball (0 : ℂ) ρ) := fun n =>
    (hcont t ht le_rfl).add (continuousOn_const.mul ((hcont (s n) (hspos n) (hsle n)).neg.div_const (s n)))
  -- mass scaling: `w_{s(k+1)} / s(k+1) ≤ w_{s k} / s k`
  have hscale : ∀ x ∈ ball (0 : ℂ) ρ, ∀ k : ℕ,
      leastSupersolution μ ρ 0 (s (k + 1)) x / s (k + 1) ≤ leastSupersolution μ ρ 0 (s k) x / s k := by
    intro x hx k
    have hle : s (k + 1) ≤ s k := by
      simp only [hs_def, pow_succ]
      have : (0 : ℝ) < t * (1 / 2) ^ k := by positivity
      nlinarith
    have h := leastSupersolution_le_scaled (μ := μ) (r := ρ) (z := 0) (hspos (k + 1)) hle x (hbb x hx)
    rw [div_le_div_iff₀ (hspos (k + 1)) (hspos k)]
    have hsk := hspos k
    have h2 := mul_le_mul_of_nonneg_right h hsk.le
    have e : s (k + 1) / s k * leastSupersolution μ ρ 0 (s k) x * s k
        = s (k + 1) * leastSupersolution μ ρ 0 (s k) x := by
      field_simp
    linarith [h2, e]
  -- monotonicity of `A n` in `n`
  have hAstep : ∀ x ∈ ball (0 : ℂ) ρ, ∀ k : ℕ, A k x ≤ A (k + 1) x := by
    intro x hx k
    have h1 := hscale x hx k
    have h2 : -(leastSupersolution μ ρ 0 (s k) x) / s k ≤
        -(leastSupersolution μ ρ 0 (s (k + 1)) x) / s (k + 1) := by
      rw [neg_div, neg_div]
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 ht.le
    simp only [hA_def]
    linarith
  have hAmono : ∀ x ∈ ball (0 : ℂ) ρ, Monotone fun n => A n x := fun x hx =>
    monotone_nat_of_le_succ (fun k => hAstep x hx k)
  -- pointwise eventual positivity on `K`
  have hpos : ∀ x ∈ K, ∃ n, 0 < A n x := by
    intro x hxK
    have hxB : x ∈ ball (0 : ℂ) ρ := hΛball (hKΛ hxK)
    by_cases hx0 : x = 0
    · -- the pole: `R_n(0) → ∞` (`Pole.lean`), with `R_n = -(s_n)⁻¹ w_{s_n}`
      subst hx0
      let R : ℕ → ℂ → ℝ := fun n y => -((s n)⁻¹ * leastSupersolution μ ρ 0 (s n) y)
      have hRsup : ∀ n, IsSuperharmonicOn (ball (0 : ℂ) ρ) (R n) := by
        intro n
        obtain ⟨μp, hμp⟩ := hLap (s n) (hspos n)
        exact isSuperharmonicOn_neg_mul_of_hasLaplacian hsup isOpen_ball (inv_pos.2 (hspos n))
          (hcont (s n) (hspos n) (hsle n)) hμp
      have hRc : ∀ n, ContinuousOn (R n) (ball (0 : ℂ) ρ) := fun n =>
        (continuousOn_const.mul (hcont (s n) (hspos n) (hsle n))).neg
      have hRmono : ∀ y ∈ ball (0 : ℂ) ρ, Monotone fun n => R n y := by
        intro y hy
        refine monotone_nat_of_le_succ (fun k => ?_)
        have h1 := hscale y hy k
        rw [div_eq_inv_mul, div_eq_inv_mul] at h1
        simp only [R]
        linarith
      have hRheq : ∀ y ∈ ball (0 : ℂ) ρ \ {0}, ∀ᶠ n in atTop,
          R n y = greenFunction (ball 0 ρ) 0 y := by
        intro y hy
        obtain ⟨s₀, hs₀, hys₀⟩ := hint y hy.1 hy.2
        filter_upwards [eventually_leastSupersolution_eq_neg_green ht hopen hΛ hmonoΛ hy.1 hy.2 s₀ hs₀ hys₀]
          with n hn
        simp only [R, hs_def]
        rw [hn]
        have := hspos n
        simp only [hs_def] at this
        field_simp
      have hpole := eventually_ge_pole_of_superharmonic hρ (half_pos hρ) (by linarith) hRsup hRc hGc
        (fun y hy => hRmono y hy.1) hRheq hGlow ((|leastSupersolution μ ρ 0 t 0| + 1) / t)
      obtain ⟨n, hn⟩ := hpole.exists
      refine ⟨n, ?_⟩
      have hAR : A n 0 = leastSupersolution μ ρ 0 t 0 + t * R n 0 := by
        simp only [hA_def, R]
        ring
      have hM : t * ((|leastSupersolution μ ρ 0 t 0| + 1) / t) = |leastSupersolution μ ρ 0 t 0| + 1 := by
        field_simp
      have h1 : t * ((|leastSupersolution μ ρ 0 t 0| + 1) / t) ≤ t * R n 0 :=
        mul_le_mul_of_nonneg_left hn ht.le
      have h2 := neg_le_abs (leastSupersolution μ ρ 0 t 0)
      linarith [hAR]
    · -- away from the pole: the surplus is eventually the strictly positive `w_t + t G` (strict obstacle gap)
      obtain ⟨s₀, hs₀, hxs₀⟩ := hint x hxB hx0
      have hgap : x ∈ cluster μ ρ 0 t := hΛc (hKΛ hxK)
      obtain ⟨n, hn⟩ := (eventually_pos_surplus_of_mem_cluster ht hopen hΛ hmonoΛ hxB hx0 hgap s₀ hs₀ hxs₀).exists
      exact ⟨n, hn⟩
  -- compact cover, then the minimum on `K`
  have hKU : K ⊆ ball (0 : ℂ) ρ := fun x hx => hΛball (hKΛ hx)
  obtain ⟨n0, hn0⟩ := exists_forall_pos_on_open isOpen_ball hK hKU A hAc hAmono hpos
  obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne ((hAc n0).mono hKU)
  exact ⟨n0, A n0 x₀, hn0 x₀ hx₀K, fun x hx => hmin hx⟩

end MatedCRT.S5c
