import MatedCRT.FirstPass.Derived.RevuzUniquenessLocalizer
import MatedCRT.FirstPass.Derived.RevuzWeightedStart

/-!
# Riemann sums for the weighted-start clock integral

Ingredients of the identity `∫ dx g(x) E_x[∫_{(0,r]} h(B_s) dA_s] = lim_N Σ_{k<N} (r/N) ∫ P_{kr/N} g · h dμ_A`, which
shows that the weighted-start expectation of a positive continuous additive functional `A` of planar Brownian
motion is determined by its Revuz measure `μ_A` (the uniqueness half of the Revuz correspondence,
Fukushima–Oshima–Takeda (2011), Theorem 5.1.4; Revuz–Yor (1999), Chapter X, Theorem 2.6).

* Additivity of a set integral over a partition of `(t_0, t_N]` into consecutive windows.
* The heat semigroup `P_s g(y) = E_y[g(B_s)]` inherits a translation modulus from `g`.
* On one window `(t, t + δ]`, the reversed Markov identity gives
  `∫ dx E_x[g(B_0) ∫_{(t,t+δ]} h dA] = ∫ dx E_x[P_t g(B_t) ∫_{(t,t+δ]} h dA]`.
* On one window, the Revuz window formula gives `∫ dx E_x[∫_{(t,t+δ]} P_t g(B_s) h(B_s) dA_s] = δ ∫ P_t g · h dμ_A`.
* Pathwise comparison of `∫ P(ω_s) h(ω_s) dA_s` with `P(y_0) ∫ h(ω_s) dA_s` on a window.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess HarmonicBalls

/-- **Additivity over consecutive windows.** For a nondecreasing sequence `t_0 ≤ t_1 ≤ ⋯`, the set integral over
`(t_0, t_N]` is the sum of the set integrals over the windows `(t_k, t_{k+1}]`, `k < N`. -/
theorem setLIntegral_Ioc_eq_sum_range (ν : Measure ℝ) (f : ℝ → ℝ≥0∞) {t : ℕ → ℝ} (ht : Monotone t) (N : ℕ) :
    ∫⁻ s in Ioc (t 0) (t N), f s ∂ν = ∑ k ∈ Finset.range N, ∫⁻ s in Ioc (t k) (t (k + 1)), f s ∂ν := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, ← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
      Ioc_union_Ioc_eq_Ioc (ht (Nat.zero_le N)) (ht (Nat.le_succ N))]

/-- The heat semigroup applied to a measurable function is measurable in the starting point. -/
theorem measurable_lintegral_planarLaw_eval (s : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun y => ∫⁻ ω, g (ω s) ∂planarLaw y :=
  (Measure.measurable_lintegral (hg.comp (ContinuousPath.measurable_coordinateProcess s))).comp
    measurable_planarLaw

/-- **Translation modulus of the heat semigroup.** If `g(a + v) ≤ g(b + v) + c` for every `v`, then
`E_a[g(B_s)] ≤ E_b[g(B_s)] + c`. -/
theorem lintegral_planarLaw_eval_le_add (s : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) {a b : ℂ} {c : ℝ≥0∞}
    (hc : ∀ v, g (a + v) ≤ g (b + v) + c) :
    ∫⁻ ω, g (ω s) ∂planarLaw a ≤ ∫⁻ ω, g (ω s) ∂planarLaw b + c := by
  have h1 : ∀ x, ∫⁻ ω, g (ω s) ∂planarLaw x =
      ∫⁻ w, g (x + (Real.sqrt s : ℂ) * w) ∂stdPlanarGaussian := fun x => by
    rw [lintegral_planarLaw_eval_eq s hg x, planarGaussian_eq_map_add_sqrt_mul, lintegral_map hg (by fun_prop)]
  rw [h1, h1]
  calc ∫⁻ w, g (a + (Real.sqrt s : ℂ) * w) ∂stdPlanarGaussian
      ≤ ∫⁻ w, (g (b + (Real.sqrt s : ℂ) * w) + c) ∂stdPlanarGaussian := lintegral_mono fun w => hc _
    _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- **Bounded Lipschitz modulus of the heat semigroup.** If `g(x) ≤ g(y) + min (K·|x - y|) C` for all `x, y`, then
the same bound holds for `y ↦ E_y[g(B_s)]`. -/
theorem lintegral_planarLaw_eval_le_add_min (s : ℝ≥0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) {K C : ℝ≥0∞}
    (hgm : ∀ x y, g x ≤ g y + min (K * edist x y) C) (a b : ℂ) :
    ∫⁻ ω, g (ω s) ∂planarLaw a ≤ ∫⁻ ω, g (ω s) ∂planarLaw b + min (K * edist a b) C :=
  lintegral_planarLaw_eval_le_add s hg fun v => by simpa only [edist_add_right] using hgm (a + v) (b + v)

/-- **Weighted start on one window.** For a positive continuous additive functional `A` of planar Brownian motion,
`∫ dx E_x[g(B_0) ∫_{(t,t+δ]} h(B_s) dA_s] = ∫ dx E_x[P_t g(B_t) ∫_{(t,t+δ]} h(B_s) dA_s]`, where
`P_t g(y) = E_y[g(B_t)]`. -/
theorem lintegral_eval_zero_mul_setLIntegral_Ioc_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (t : ℝ≥0) {g h : ℂ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) (δ : ℝ) :
    ∫⁻ x, ∫⁻ ω, g (ω 0) * ∫⁻ s in Ioc (t : ℝ) (t + δ), h (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x =
      ∫⁻ x, ∫⁻ ω, (∫⁻ ω', g (ω' t) ∂planarLaw (ω t)) * ∫⁻ s in Ioc (t : ℝ) (t + δ), h (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x := by
  have e1 : ∀ G : ContinuousPath ℂ → ℝ≥0∞,
      ∫⁻ x, ∫⁻ ω, G ω * ∫⁻ s in Ioc (t : ℝ) (t + δ), h (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x =
      ∫⁻ x, ∫⁻ ω, G ω * clockWindowIntegral A h δ (LatticeProb.pathShift ω t) ∂planarLaw x := fun G =>
    lintegral_congr fun x => lintegral_congr_ae
      ((ae_setLIntegral_Ioc_shift_window_eq hA x t hh δ).mono fun ω hω => by simp only [hω])
  rw [e1 (fun ω => g (ω 0)), e1 (fun ω => ∫⁻ ω', g (ω' t) ∂planarLaw (ω t))]
  exact lintegral_eval_zero_mul_pathShift_eq t hg (measurable_clockWindowIntegral hA.meas hh δ)

/-- **The Riemann-sum term on one window.** For a positive continuous additive functional `A` of planar Brownian
motion and `δ ≥ 0`, `∫ dx E_x[∫_{(t,t+δ]} P_t g(B_s) h(B_s) dA_s] = δ ∫ P_t g · h dμ_A`. -/
theorem lintegral_setLIntegral_Ioc_heat_mul_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (t : ℝ≥0) {g h : ℂ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    ∫⁻ x, ∫⁻ ω, ∫⁻ s in Ioc (t : ℝ) (t + δ), (∫⁻ ω', g (ω' t) ∂planarLaw (ω s.toNNReal)) * h (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x =
      ENNReal.ofReal δ * ∫⁻ y, (∫⁻ ω', g (ω' t) ∂planarLaw y) * h y ∂revuz planarLaw A :=
  lintegral_setLIntegral_Ioc_eq_ofReal_mul_lintegral_revuz hA t
    (g := fun y => (∫⁻ ω', g (ω' t) ∂planarLaw y) * h y) ((measurable_lintegral_planarLaw_eval t hg).mul hh) hδ

/-- **Pathwise comparison on a window.** If `u ≤ v + w` pointwise and `v · h` is measurable, then
`∫_S u h dν ≤ ∫_S v h dν + ∫_S w h dν`. -/
theorem setLIntegral_mul_le_add {ν : Measure ℝ} {S : Set ℝ} {u v w h : ℝ → ℝ≥0∞}
    (hvh : Measurable fun s => v s * h s) (huvw : ∀ s, u s ≤ v s + w s) :
    ∫⁻ s in S, u s * h s ∂ν ≤ ∫⁻ s in S, v s * h s ∂ν + ∫⁻ s in S, w s * h s ∂ν := by
  rw [← lintegral_add_left hvh]
  refine lintegral_mono fun s => ?_
  rw [← add_mul]
  gcongr
  exact huvw s

end MatedCRT
