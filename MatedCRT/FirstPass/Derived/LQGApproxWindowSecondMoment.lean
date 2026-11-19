import MatedCRT.FirstPass.Derived.PlanarOccupationSecondMoment
import MatedCRT.FirstPass.Derived.StoppedHeatBoundOfBallBound

/-!
# Second moment of the window occupation integrals of the LQG approximants

Let `ρ_k = ε^{γ²/2} e^{γ h_ε}`, `ε = 2^{-k}`, be the density of the `k`-th dyadic approximant of the
`γ`-LQG measure and `f ≥ 0` a bounded measurable function vanishing outside `B̄(0, n)`.  If the
approximants give every ball `B(c, r)`, `‖c‖ ≤ n + 1`, `0 < r ≤ 1` mass at most `C r^β`, uniformly in
`k`, then the Green potential `y ↦ ∫_{(0,1]} ∫ f ρ_k d(planar Gaussian y, r) dr` is bounded by a
constant `U` independent of `k` and of `‖y‖ ≤ n` (`exists_green_bound_weightedApproxDensity`).  With
the Khas'minskii bound `lintegral_windowOcc_sq_le` this gives
`∫ dz E_z[(∫_{(0,1]} f ρ_k(B_s) ds)²] ≤ 2 U ∫ f ρ_k` (`lintegral_lintegral_windowOcc_sq_le`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.FirstPass.Derived

/-- The density `f · ε^{γ²/2} e^{γ h_ε}` of `f` against the `k`-th dyadic approximant of the
`γ`-LQG measure. -/
noncomputable def weightedApproxDensity (γ : ℝ) (h : ℝ → ℂ → ℝ) (f : ℂ → ℝ) (k : ℕ) (x : ℂ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (f x) * ENNReal.ofReal (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
    Real.exp (γ * h (LatticeProb.LQG.dyadicScale k) x))

theorem measurable_weightedApproxDensity {γ : ℝ} {h : ℝ → ℂ → ℝ} {f : ℂ → ℝ} {k : ℕ}
    (hf : Measurable f) (hm : Measurable (h (LatticeProb.LQG.dyadicScale k))) :
    Measurable (weightedApproxDensity γ h f k) :=
  (ENNReal.measurable_ofReal.comp hf).mul
    (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hm))))

theorem weightedApproxDensity_eq_zero {γ : ℝ} {h : ℝ → ℂ → ℝ} {f : ℂ → ℝ} {k : ℕ} {x : ℂ}
    (hx : f x = 0) : weightedApproxDensity γ h f k x = 0 := by
  simp [weightedApproxDensity, hx]

/-- **Green potential bound for the weighted approximant densities.**  If the dyadic approximants of
the `γ`-LQG measure of `h` give every ball `B(c, r)` with `‖c‖ ≤ n + 1` and `0 < r ≤ 1` mass at most
`C r^β`, uniformly in the level, and `0 ≤ f ≤ K` is measurable and vanishes off `B̄(0, n)`, then
`∫_{(0,1]} ∫ f ρ_k d(planar Gaussian y, r) dr ≤ U` for every level `k` and every `‖y‖ ≤ n`. -/
theorem exists_green_bound_weightedApproxDensity {γ : ℝ} {h : ℝ → ℂ → ℝ}
    (hmeas : ∀ k : ℕ, Measurable (h (LatticeProb.LQG.dyadicScale k)))
    {n β C : ℝ} (hβ : 0 < β) (hC0 : 0 < C)
    (hball : ∀ z : ℂ, ‖z‖ ≤ n + 1 → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
      LatticeProb.LQG.lqgApprox γ h (LatticeProb.LQG.dyadicScale k) (ball z r) ≤
        ENNReal.ofReal (C * r ^ β))
    {f : ℂ → ℝ} (hf : Measurable f) {K : ℝ} (hfK : ∀ x, 0 ≤ f x ∧ f x ≤ K)
    (hfn : ∀ x : ℂ, n < ‖x‖ → f x = 0) :
    ∃ U : ℝ≥0∞, U ≠ ⊤ ∧ ∀ k : ℕ, ∀ y : ℂ, ‖y‖ ≤ n →
      ∫⁻ r in Ioc (0 : ℝ) 1, ∫⁻ x, weightedApproxDensity γ h f k x
        ∂planarGaussian y r.toNNReal ≤ U := by
  obtain ⟨N, hN⟩ :=
    LatticeProb.exists_lintegral_Ioc_lintegral_map_prod_gaussianReal_indicator_le (0 : ℂ) (n + 1)
  have hK0 : 0 ≤ K := (hfK 0).1.trans (hfK 0).2
  refine ⟨ENNReal.ofReal (1024 / 7 / (2 * Real.pi) * max (K * C) (N * (K * C)) /
    (min β 1 / 2) * (1 : ℝ) ^ (min β 1 / 2)), ENNReal.ofReal_ne_top, fun k y hy => ?_⟩
  have hgm := measurable_weightedApproxDensity (γ := γ) (h := h) (k := k) hf (hmeas k)
  have hind : (ball (0 : ℂ) (n + 1)).indicator (weightedApproxDensity γ h f k) =
      weightedApproxDensity γ h f k := by
    refine indicator_eq_self.2 fun x hx => ?_
    by_contra hxb
    refine hx (weightedApproxDensity_eq_zero (hfn x ?_))
    have : n + 1 ≤ ‖x‖ := by simpa [mem_ball_zero_iff] using hxb
    linarith
  have key := hN _ hgm (K * C) β (mul_nonneg hK0 hC0.le) hβ (fun c hc r hr hr1 => ?_) y
    (mem_closedBall_zero_iff.2 (by linarith)) 1 zero_le_one
  · rw [hind] at key
    exact key
  · have h1 := hball c (mem_closedBall_zero_iff.1 hc) r hr hr1 k
    rw [LatticeProb.LQG.lqgApprox, withDensity_apply _ measurableSet_ball] at h1
    calc ∫⁻ x in ball c r, weightedApproxDensity γ h f k x
        ≤ ∫⁻ x in ball c r, ENNReal.ofReal K * ENNReal.ofReal
            (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
              Real.exp (γ * h (LatticeProb.LQG.dyadicScale k) x)) :=
          setLIntegral_mono' measurableSet_ball fun x _ =>
            mul_le_mul' (ENNReal.ofReal_le_ofReal (hfK x).2) le_rfl
      _ = ENNReal.ofReal K * ∫⁻ x in ball c r, ENNReal.ofReal
            (LatticeProb.LQG.dyadicScale k ^ (γ ^ 2 / 2) *
              Real.exp (γ * h (LatticeProb.LQG.dyadicScale k) x)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal (C * r ^ β) := mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (K * C * r ^ β) := by
          rw [← ENNReal.ofReal_mul hK0]
          congr 1
          ring

/-- The window occupation integrals integrate against the starting point `z` to the integral of the
density: `∫ dz E_z ∫_{(0,1]} g(B_s) ds = ∫ g`. -/
theorem lintegral_lintegral_windowOcc_planarLaw {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, ∫⁻ b, windowOcc g b ∂planarLaw z = ∫⁻ x, g x := by
  have hP : ∀ z : ℂ, IsProbabilityMeasure (planarLaw z) := fun z => by
    unfold planarLaw; infer_instance
  have hev := measurable_eval_toNNReal_uncurry hg
  have hswap : ∀ z : ℂ, ∫⁻ b, windowOcc g b ∂planarLaw z =
      ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ b, g (b s.toNNReal) ∂planarLaw z := fun z => by
    unfold windowOcc
    exact lintegral_lintegral_swap (μ := planarLaw z) (ν := volume.restrict (Ioc (0 : ℝ) 1))
      (f := fun (b : ContinuousPath ℂ) (s : ℝ) => g (b s.toNNReal))
      ((hev.comp measurable_swap).aemeasurable)
  simp_rw [hswap]
  have hm : Measurable fun p : (ℂ × ℝ) × ContinuousPath ℂ => g (p.2 p.1.2.toNNReal) :=
    hev.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hmz : Measurable fun q : ℂ × ℝ => ∫⁻ b, g (b q.2.toNNReal) ∂planarLaw q.1 :=
    measurable_lintegral_planarLaw (X := ℂ × ℝ) (p := Prod.fst) measurable_fst hm
  rw [lintegral_lintegral_swap (μ := volume) (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun (z : ℂ) (s : ℝ) => ∫⁻ b, g (b s.toNNReal) ∂planarLaw z) hmz.aemeasurable]
  rw [setLIntegral_congr_fun measurableSet_Ioc
    (fun s _ => lintegral_lintegral_planarLaw_eval s.toNNReal hg)]
  simp

/-- **Second moment bound for the window occupation integrals of the approximants.**  If the Green
potential of `g` is at most `U` on `B̄(0, n)` and `g` vanishes off `B̄(0, n)`, then
`∫ dz E_z[(∫_{(0,1]} g(B_s) ds)²] ≤ 2 U ∫ g`. -/
theorem lintegral_lintegral_windowOcc_sq_le {g : ℂ → ℝ≥0∞} (hg : Measurable g) {n : ℝ}
    (hn : ∀ y : ℂ, n < ‖y‖ → g y = 0) {U : ℝ≥0∞}
    (hU : ∀ y : ℂ, ‖y‖ ≤ n →
      ∫⁻ r in Ioc (0 : ℝ) 1, ∫⁻ x, g x ∂planarGaussian y r.toNNReal ≤ U) :
    ∫⁻ z, ∫⁻ b, windowOcc g b ^ 2 ∂planarLaw z ≤ 2 * (U * ∫⁻ x, g x) := by
  have hmz : Measurable fun z : ℂ => ∫⁻ b, windowOcc g b ∂planarLaw z :=
    measurable_lintegral_planarLaw (X := ℂ) (p := id) measurable_id
      ((measurable_windowOcc hg).comp measurable_snd)
  calc ∫⁻ z, ∫⁻ b, windowOcc g b ^ 2 ∂planarLaw z
      ≤ ∫⁻ z, 2 * (U * ∫⁻ b, windowOcc g b ∂planarLaw z) :=
        lintegral_mono fun z => lintegral_windowOcc_sq_le hg hn hU z
    _ = 2 * (U * ∫⁻ z, ∫⁻ b, windowOcc g b ∂planarLaw z) := by
        rw [lintegral_const_mul _ (hmz.const_mul U), lintegral_const_mul _ hmz]
    _ = 2 * (U * ∫⁻ x, g x) := by rw [lintegral_lintegral_windowOcc_planarLaw hg]

end MatedCRT.FirstPass.Derived
