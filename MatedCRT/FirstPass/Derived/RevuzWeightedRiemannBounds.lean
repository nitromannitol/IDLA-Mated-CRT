import MatedCRT.FirstPass.Derived.RevuzWeightedRiemann

/-!
# Two-sided Riemann-sum bounds for the weighted-start clock integral

Let `A` be a positive continuous additive functional of planar Brownian motion with Revuz measure `μ_A`, and let
`g ≥ 0` satisfy `g(x) ≤ g(y) + min (K|x - y|) C`. Split `(0, Nδ]` into the windows `(kδ, (k+1)δ]`, `k < N`, and write
`P_t g(y) = E_y[g(B_t)]`. With `a = ∫ dx E_x[g(B_0) ∫_{(0,Nδ]} h(B_s) dĀ_s]`, the Riemann sum
`b = Σ_{k<N} δ ∫ P_{kδ} g · h dμ_A`, and the discretization error
`e = ∫ dx E_x[Σ_{k<N} ∫_{(kδ,(k+1)δ]} min (K|B_s - B_{kδ}|) C · h(B_s) dĀ_s]`, we prove `a ≤ b + e` and `b ≤ a + e`.

The proof compares, window by window and path by path, `∫ P_{kδ} g(ω_s) h(ω_s) dĀ_s` with
`P_{kδ} g(ω_{kδ}) ∫ h(ω_s) dĀ_s`; the first has expectation `δ ∫ P_{kδ} g · h dμ_A` by the Revuz window formula and
the second has expectation `∫ dx E_x[g(B_0) ∫_{(kδ,(k+1)δ]} h dĀ]` by the reversed Markov identity
(Fukushima–Oshima–Takeda (2011), proof of Theorem 5.1.4; Revuz–Yor (1999), Chapter X, Theorem 2.6).
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- The Lebesgue–Stieltjes measure of the rational-time regularization `Ā` of the clock `A` along the path `ω`. -/
noncomputable def regClockMeasure (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (ω : ContinuousPath ℂ) : Measure ℝ :=
  (stieltjesOfNNReal fun u => regularize A u ω).measure

/-- Set integrals against the regularized clock measure along the path are measurable in the path. -/
theorem measurable_setLIntegral_regClockMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    {E : Type*} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : ContinuousPath ℂ → ℝ → E) (hγc : ∀ ω, Continuous (γ ω)) (hγm : ∀ s, Measurable fun ω => γ ω s)
    (a b : ℝ) {g : E → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun ω => ∫⁻ s in Ioc a b, g (γ ω s) ∂regClockMeasure A ω :=
  LatticeProb.measurable_setLIntegral_stieltjes_Ioc_comp _ (measurable_stieltjesOfNNReal_regularize hA) γ hγc hγm
    a b hg

/-- For a positive continuous additive functional, almost surely the regularized clock measure along the path is
the Lebesgue–Stieltjes measure of the clock itself. -/
theorem ae_regClockMeasure_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF planarLaw A) (z : ℂ) :
    ∀ᵐ ω ∂planarLaw z, regClockMeasure A ω = (stieltjesOfNNReal fun u => A u ω).measure := by
  filter_upwards [hA.path z] with ω hω
  have hreg : (fun u => regularize A u ω) = fun u => A u ω :=
    funext (regularize_eq_of_continuous_monotone hω.2.1 hω.2.2)
  rw [regClockMeasure, hreg]

/-- Integration against the Lebesgue-started path law is the iterated integral. -/
theorem lintegral_bind_planarLaw {F : ContinuousPath ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F ω ∂(volume : Measure ℂ).bind planarLaw = ∫⁻ x, ∫⁻ ω, F ω ∂planarLaw x :=
  Measure.lintegral_bind measurable_planarLaw.aemeasurable hF.aemeasurable

/-- **Weighted start on one window**, regularized clock: `∫ dx E_x[g(B_0) ∫_{(t,t+δ]} h dĀ] =
∫ dx E_x[P_t g(B_t) ∫_{(t,t+δ]} h dĀ]`. -/
theorem lintegral_eval_zero_mul_regClock_window_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (t : ℝ≥0) {g h : ℂ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) (δ : ℝ) :
    ∫⁻ x, ∫⁻ ω, g (ω 0) * ∫⁻ s in Ioc (t : ℝ) (t + δ), h (ω s.toNNReal) ∂regClockMeasure A ω ∂planarLaw x =
      ∫⁻ x, ∫⁻ ω, (∫⁻ ω', g (ω' t) ∂planarLaw (ω t)) *
        ∫⁻ s in Ioc (t : ℝ) (t + δ), h (ω s.toNNReal) ∂regClockMeasure A ω ∂planarLaw x := by
  have e : ∀ G : ContinuousPath ℂ → ℝ≥0∞,
      ∫⁻ x, ∫⁻ ω, G ω * ∫⁻ s in Ioc (t : ℝ) (t + δ), h (ω s.toNNReal) ∂regClockMeasure A ω ∂planarLaw x =
      ∫⁻ x, ∫⁻ ω, G ω * ∫⁻ s in Ioc (t : ℝ) (t + δ), h (ω s.toNNReal)
        ∂(stieltjesOfNNReal fun u => A u ω).measure ∂planarLaw x := fun G =>
    lintegral_congr fun x => lintegral_congr_ae ((ae_regClockMeasure_eq hA x).mono fun ω hω => by simp only [hω])
  rw [e (fun ω => g (ω 0)), e (fun ω => ∫⁻ ω', g (ω' t) ∂planarLaw (ω t))]
  exact lintegral_eval_zero_mul_setLIntegral_Ioc_eq hA t hg hh δ

/-- **The Riemann-sum term on one window**, regularized clock:
`∫ dx E_x[∫_{(t,t+δ]} P_t g(B_s) h(B_s) dĀ_s] = δ ∫ P_t g · h dμ_A`. -/
theorem lintegral_regClock_window_heat_mul_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (t : ℝ≥0) {g h : ℂ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    ∫⁻ x, ∫⁻ ω, ∫⁻ s in Ioc (t : ℝ) (t + δ), (∫⁻ ω', g (ω' t) ∂planarLaw (ω s.toNNReal)) * h (ω s.toNNReal)
        ∂regClockMeasure A ω ∂planarLaw x =
      ENNReal.ofReal δ * ∫⁻ y, (∫⁻ ω', g (ω' t) ∂planarLaw y) * h y ∂revuz planarLaw A := by
  rw [← lintegral_setLIntegral_Ioc_heat_mul_eq hA t hg hh hδ]
  exact lintegral_congr fun x => lintegral_congr_ae ((ae_regClockMeasure_eq hA x).mono fun ω hω => by simp only [hω])

theorem coe_natCast_succ_mul_nnreal (k : ℕ) (δ : ℝ≥0) :
    ((((k + 1 : ℕ) : ℝ≥0) * δ : ℝ≥0) : ℝ) = (((k : ℝ≥0) * δ : ℝ≥0) : ℝ) + δ := by
  push_cast
  ring

/-- The regularized window integral over `(0, Nδ]` is the sum of the clock integrals over the windows
`(kδ, (k+1)δ]`, `k < N`. -/
theorem clockWindowIntegral_eq_sum_range (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (h : ℂ → ℝ≥0∞) (δ : ℝ≥0) (N : ℕ)
    (ω : ContinuousPath ℂ) :
    clockWindowIntegral A h ((N : ℝ≥0) * δ : ℝ≥0) ω = ∑ k ∈ Finset.range N,
      ∫⁻ s in Ioc (((k : ℝ≥0) * δ : ℝ≥0) : ℝ) (((k : ℝ≥0) * δ : ℝ≥0) + δ), h (ω s.toNNReal)
        ∂regClockMeasure A ω := by
  have ht : Monotone fun k : ℕ => (((k : ℝ≥0) * δ : ℝ≥0) : ℝ) := fun i j hij =>
    NNReal.coe_le_coe.2 (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity))
  have hsum := setLIntegral_Ioc_eq_sum_range (regClockMeasure A ω) (fun s => h (ω s.toNNReal)) ht N
  simp only [Nat.cast_zero, zero_mul, NNReal.coe_zero, coe_natCast_succ_mul_nnreal] at hsum
  exact hsum

/-- The Riemann sum `Σ_{k<N} δ ∫ P_{kδ} g · h dμ`, where `P_t g(y) = E_y[g(B_t)]`. -/
noncomputable def heatRiemannSum (g h : ℂ → ℝ≥0∞) (μ : Measure ℂ) (δ : ℝ≥0) (N : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range N, ENNReal.ofReal δ * ∫⁻ y, (∫⁻ ω', g (ω' ((k : ℝ≥0) * δ)) ∂planarLaw y) * h y ∂μ

/-- The pathwise discretization error `Σ_{k<N} ∫_{(kδ,(k+1)δ]} min (K|ω_s - ω_{kδ}|) C · h(ω_s) dĀ_s`. -/
noncomputable def clockRiemannError (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (h : ℂ → ℝ≥0∞) (K C : ℝ≥0∞) (δ : ℝ≥0)
    (N : ℕ) (ω : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range N, ∫⁻ s in Ioc (((k : ℝ≥0) * δ : ℝ≥0) : ℝ) (((k : ℝ≥0) * δ : ℝ≥0) + δ),
    min (K * edist (ω s.toNNReal) (ω ((k : ℝ≥0) * δ))) C * h (ω s.toNNReal) ∂regClockMeasure A ω

/-- The discretization error is measurable in the path. -/
theorem measurable_clockRiemannError {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) (K C : ℝ≥0∞) (δ : ℝ≥0) (N : ℕ) :
    Measurable (clockRiemannError A h K C δ N) := by
  refine Finset.measurable_sum _ fun k _ => ?_
  have hg : Measurable fun p : ℂ × ℂ => min (K * edist p.1 p.2) C * h p.1 :=
    ((measurable_const.mul continuous_edist.measurable).min measurable_const).mul (hh.comp measurable_fst)
  exact measurable_setLIntegral_regClockMeasure hA (fun ω s => (ω s.toNNReal, ω ((k : ℝ≥0) * δ)))
    (fun ω => (ω.continuous.comp continuous_real_toNNReal).prodMk continuous_const)
    (fun _ => (ContinuousMap.measurable_eval _).prodMk (ContinuousMap.measurable_eval _)) _ _ hg

/-- **Pathwise window comparison.** On each window, `∫ P(ω_s) h(ω_s) dĀ_s` and `P(ω_{kδ}) ∫ h(ω_s) dĀ_s` differ by
at most the discretization error of that window, where `P = P_{kδ} g`. -/
theorem window_heat_comparison {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {g h : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hh : Measurable h) {K C : ℝ≥0∞} (hgm : ∀ x y, g x ≤ g y + min (K * edist x y) C) (t : ℝ≥0) (δ : ℝ)
    (ω : ContinuousPath ℂ) :
    (∫⁻ s in Ioc (t : ℝ) (t + δ), (∫⁻ ω', g (ω' t) ∂planarLaw (ω s.toNNReal)) * h (ω s.toNNReal)
        ∂regClockMeasure A ω ≤
      (∫⁻ ω', g (ω' t) ∂planarLaw (ω t)) * ∫⁻ s in Ioc (t : ℝ) (t + δ), h (ω s.toNNReal) ∂regClockMeasure A ω +
        ∫⁻ s in Ioc (t : ℝ) (t + δ), min (K * edist (ω s.toNNReal) (ω t)) C * h (ω s.toNNReal)
          ∂regClockMeasure A ω) ∧
    ((∫⁻ ω', g (ω' t) ∂planarLaw (ω t)) * ∫⁻ s in Ioc (t : ℝ) (t + δ), h (ω s.toNNReal) ∂regClockMeasure A ω ≤
      ∫⁻ s in Ioc (t : ℝ) (t + δ), (∫⁻ ω', g (ω' t) ∂planarLaw (ω s.toNNReal)) * h (ω s.toNNReal)
          ∂regClockMeasure A ω +
        ∫⁻ s in Ioc (t : ℝ) (t + δ), min (K * edist (ω s.toNNReal) (ω t)) C * h (ω s.toNNReal)
          ∂regClockMeasure A ω) := by
  have hωs : Measurable fun s : ℝ => ω s.toNNReal := (ω.continuous.comp continuous_real_toNNReal).measurable
  have hhs : Measurable fun s : ℝ => h (ω s.toNNReal) := hh.comp hωs
  have hP := measurable_lintegral_planarLaw_eval t hg
  constructor
  · have h1 := setLIntegral_mul_le_add (ν := regClockMeasure A ω) (S := Ioc (t : ℝ) (t + δ))
      (u := fun s => ∫⁻ ω', g (ω' t) ∂planarLaw (ω s.toNNReal)) (v := fun _ => ∫⁻ ω', g (ω' t) ∂planarLaw (ω t))
      (w := fun s => min (K * edist (ω s.toNNReal) (ω t)) C) (h := fun s => h (ω s.toNNReal))
      (measurable_const.mul hhs) (fun s => lintegral_planarLaw_eval_le_add_min t hg hgm _ _)
    beta_reduce at h1
    rw [lintegral_const_mul _ hhs] at h1
    exact h1
  · have h2 := setLIntegral_mul_le_add (ν := regClockMeasure A ω) (S := Ioc (t : ℝ) (t + δ))
      (u := fun _ => ∫⁻ ω', g (ω' t) ∂planarLaw (ω t)) (v := fun s => ∫⁻ ω', g (ω' t) ∂planarLaw (ω s.toNNReal))
      (w := fun s => min (K * edist (ω s.toNNReal) (ω t)) C) (h := fun s => h (ω s.toNNReal))
      ((hP.comp hωs).mul hhs) (fun s => by rw [edist_comm]; exact lintegral_planarLaw_eval_le_add_min t hg hgm _ _)
    beta_reduce at h2
    rw [lintegral_const_mul _ hhs] at h2
    exact h2

/-- **Two-sided Riemann-sum bounds for the weighted-start clock integral.** For a positive continuous additive
functional `A` of planar Brownian motion, measurable `g, h ≥ 0` with `g(x) ≤ g(y) + min (K|x - y|) C`, a mesh `δ`
and `N` windows, the weighted-start expectation `a = ∫ dx E_x[g(B_0) ∫_{(0,Nδ]} h(B_s) dĀ_s]` and the Riemann sum
`b = Σ_{k<N} δ ∫ P_{kδ} g · h dμ_A` satisfy `a ≤ b + e` and `b ≤ a + e`, where `e` is the expected discretization
error under Lebesgue starts. -/
theorem lintegral_eval_zero_mul_clockWindowIntegral_riemann_bounds {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) {g h : ℂ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h) {K C : ℝ≥0∞}
    (hgm : ∀ x y, g x ≤ g y + min (K * edist x y) C) (δ : ℝ≥0) (N : ℕ) :
    ∫⁻ x, ∫⁻ ω, g (ω 0) * clockWindowIntegral A h ((N : ℝ≥0) * δ : ℝ≥0) ω ∂planarLaw x ≤
        heatRiemannSum g h (revuz planarLaw A) δ N +
          ∫⁻ ω, clockRiemannError A h K C δ N ω ∂(volume : Measure ℂ).bind planarLaw ∧
      heatRiemannSum g h (revuz planarLaw A) δ N ≤
        (∫⁻ x, ∫⁻ ω, g (ω 0) * clockWindowIntegral A h ((N : ℝ≥0) * δ : ℝ≥0) ω ∂planarLaw x) +
          ∫⁻ ω, clockRiemannError A h K C δ N ω ∂(volume : Measure ℂ).bind planarLaw := by
  let T : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * δ
  let P : ℕ → ℂ → ℝ≥0∞ := fun k y => ∫⁻ ω', g (ω' (T k)) ∂planarLaw y
  let piece : ℕ → ContinuousPath ℂ → ℝ≥0∞ := fun k ω =>
    ∫⁻ s in Ioc (T k : ℝ) (T k + δ), h (ω s.toNNReal) ∂regClockMeasure A ω
  let J : ℕ → ContinuousPath ℂ → ℝ≥0∞ := fun k ω => P k (ω (T k)) * piece k ω
  let I : ℕ → ContinuousPath ℂ → ℝ≥0∞ := fun k ω =>
    ∫⁻ s in Ioc (T k : ℝ) (T k + δ), P k (ω s.toNNReal) * h (ω s.toNNReal) ∂regClockMeasure A ω
  have hg0 : Measurable fun ω : ContinuousPath ℂ => g (ω 0) := hg.comp (ContinuousMap.measurable_eval _)
  have hPm : ∀ k, Measurable (P k) := fun k => measurable_lintegral_planarLaw_eval (T k) hg
  have hpiece : ∀ k, Measurable (piece k) := fun k =>
    measurable_setLIntegral_regClockMeasure hA.meas (fun ω s => ω s.toNNReal)
      (fun ω => ω.continuous.comp continuous_real_toNNReal) (fun _ => ContinuousMap.measurable_eval _) _ _ hh
  have hgp : ∀ k, Measurable fun ω => g (ω 0) * piece k ω := fun k => hg0.mul (hpiece k)
  have hJm : ∀ k, Measurable (J k) := fun k =>
    ((hPm k).comp (ContinuousMap.measurable_eval _)).mul (hpiece k)
  have hIm : ∀ k, Measurable (I k) := fun k =>
    measurable_setLIntegral_regClockMeasure hA.meas (fun ω s => ω s.toNNReal)
      (fun ω => ω.continuous.comp continuous_real_toNNReal) (fun _ => ContinuousMap.measurable_eval _) _ _
      ((hPm k).mul hh)
  have hJ : ∫⁻ ω, ∑ k ∈ Finset.range N, J k ω ∂(volume : Measure ℂ).bind planarLaw =
      ∫⁻ x, ∫⁻ ω, g (ω 0) * clockWindowIntegral A h ((N : ℝ≥0) * δ : ℝ≥0) ω ∂planarLaw x := by
    rw [lintegral_finsetSum _ fun k _ => hJm k]
    calc ∑ k ∈ Finset.range N, ∫⁻ ω, J k ω ∂(volume : Measure ℂ).bind planarLaw
        = ∑ k ∈ Finset.range N, ∫⁻ ω, g (ω 0) * piece k ω ∂(volume : Measure ℂ).bind planarLaw := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [lintegral_bind_planarLaw (hJm k), lintegral_bind_planarLaw (hgp k)]
          exact (lintegral_eval_zero_mul_regClock_window_eq hA (T k) hg hh δ).symm
      _ = ∫⁻ ω, ∑ k ∈ Finset.range N, g (ω 0) * piece k ω ∂(volume : Measure ℂ).bind planarLaw :=
          (lintegral_finsetSum _ fun k _ => hgp k).symm
      _ = ∫⁻ ω, g (ω 0) * clockWindowIntegral A h ((N : ℝ≥0) * δ : ℝ≥0) ω
            ∂(volume : Measure ℂ).bind planarLaw :=
          lintegral_congr fun ω => by rw [← Finset.mul_sum, clockWindowIntegral_eq_sum_range]
      _ = _ := lintegral_bind_planarLaw (hg0.mul (measurable_clockWindowIntegral hA.meas hh _))
  have hI : ∫⁻ ω, ∑ k ∈ Finset.range N, I k ω ∂(volume : Measure ℂ).bind planarLaw =
      heatRiemannSum g h (revuz planarLaw A) δ N := by
    rw [lintegral_finsetSum _ fun k _ => hIm k, heatRiemannSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [lintegral_bind_planarLaw (hIm k)]
    exact lintegral_regClock_window_heat_mul_eq hA (T k) hg hh δ.coe_nonneg
  have hcmp : ∀ ω, (∑ k ∈ Finset.range N, I k ω ≤
        ∑ k ∈ Finset.range N, J k ω + clockRiemannError A h K C δ N ω) ∧
      (∑ k ∈ Finset.range N, J k ω ≤ ∑ k ∈ Finset.range N, I k ω + clockRiemannError A h K C δ N ω) :=
    fun ω => by
      rw [clockRiemannError, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact ⟨Finset.sum_le_sum fun k _ => (window_heat_comparison hg hh hgm (T k) δ ω).1,
        Finset.sum_le_sum fun k _ => (window_heat_comparison hg hh hgm (T k) δ ω).2⟩
  have hIs : Measurable fun ω => ∑ k ∈ Finset.range N, I k ω := Finset.measurable_sum _ fun k _ => hIm k
  have hJs : Measurable fun ω => ∑ k ∈ Finset.range N, J k ω := Finset.measurable_sum _ fun k _ => hJm k
  constructor
  · rw [← hJ, ← hI, ← lintegral_add_left hIs]
    exact lintegral_mono fun ω => (hcmp ω).2
  · rw [← hJ, ← hI, ← lintegral_add_left hJs]
    exact lintegral_mono fun ω => (hcmp ω).1

end MatedCRT
