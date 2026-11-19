import MatedCRT.FirstPass.Derived.RevuzUniquenessIncrement
import MatedCRT.FirstPass.Derived.RevuzUniquenessTaylorBounds

/-!
# Two clocks with the same Revuz measure have the same window integrals

Let `A`, `A'` be positive continuous additive functionals of planar Brownian motion with the same Revuz measure `μ`,
let `h ≥ 0` be Borel with `∫ h dμ < ∞`, and write `N_r = A^h_r - A'^h_r` for the difference of the window integrals
`A^h_r = ∫_{(0,r]} h(B_s) dĀ_s`. If `E_x[A^h_t]` and `E_x[A'^h_t]` are finite at a rational time `t`, then
`A^h_t = A'^h_t` holds `P_x`-almost surely (`ae_clockWindowIntegral_eq_of_revuz_eq`).

The proof is the Taylor argument of Fukushima–Oshima–Takeda (2011), proof of Theorem 5.1.4 (compare Revuz–Yor
(1999), Chapter IV, Proposition 1.2): expand `φ(N_t)`, `φ(y) = log(1 + y²)`, along the dyadic partition
`t_k = k t / 2ⁿ` of `[0, t]`.

* The first-order terms `φ'(N_{t_k}) (N_{t_{k+1}} - N_{t_k})` have mean zero: `N_{t_k}` agrees almost surely with a
  functional of the canonical filtration at the rational time `t_k`, `|φ'| ≤ 1`, and the increments of `N` are
  centred against bounded functionals of the past.
* Along almost every path both clocks are continuous and nondecreasing, so the second-order remainders tend to zero
  and are dominated by `2 (A^h_t + A'^h_t)`, which is integrable.

Hence `E_x φ(N_t) = 0`; since `φ ≥ 0` vanishes only at `0`, `N_t = 0` almost surely.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- The window integral over the empty window `(0, 0]` vanishes. -/
@[simp] theorem clockWindowIntegral_zero (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (h : ℂ → ℝ≥0∞)
    (ω : ContinuousPath ℂ) : clockWindowIntegral A h 0 ω = 0 := by
  simp [clockWindowIntegral]

/-- Below a window where it is finite, the real window integral is nondecreasing. -/
theorem monotoneOn_clockWindowIntegral_toReal (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (h : ℂ → ℝ≥0∞)
    (ω : ContinuousPath ℂ) {T : ℝ} (hT : clockWindowIntegral A h T ω ≠ ∞) :
    MonotoneOn (fun r => (clockWindowIntegral A h r ω).toReal) (Icc 0 T) := fun _ _ _ hr' hrr =>
  ENNReal.toReal_mono (ne_top_of_le_ne_top hT (clockWindowIntegral_mono A h hr'.2 ω))
    (clockWindowIntegral_mono A h hrr ω)

theorem measurable_logOnePlusSq : Measurable logOnePlusSq := by
  show Measurable fun y : ℝ => Real.log (1 + y ^ 2)
  exact (measurable_const.add (measurable_id.pow_const 2)).log

theorem measurable_logOnePlusSqDeriv : Measurable logOnePlusSqDeriv := by
  show Measurable fun y : ℝ => 2 * y / (1 + y ^ 2)
  exact (measurable_const.mul measurable_id).div (measurable_const.add (measurable_id.pow_const 2))

section path

variable {A A' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {h : ℂ → ℝ≥0∞} {ω : ContinuousPath ℂ} {T : ℝ}

/-- Along a path on which both clocks are continuous and nondecreasing and both window integrals are finite at
`T`, the dyadic Taylor remainders of `φ(N)`, `N = A^h - A'^h`, tend to zero. -/
theorem tendsto_dyadicTaylorRemainder_clockWindowIntegral (hh : Measurable h)
    (hc : Continuous fun t => A t ω) (hm : Monotone fun t => A t ω)
    (hc' : Continuous fun t => A' t ω) (hm' : Monotone fun t => A' t ω) (hT0 : 0 ≤ T)
    (hT : clockWindowIntegral A h T ω ≠ ∞) (hT' : clockWindowIntegral A' h T ω ≠ ∞) :
    Tendsto (dyadicTaylorRemainder
      (fun r => (clockWindowIntegral A h r ω).toReal - (clockWindowIntegral A' h r ω).toReal) T)
      atTop (𝓝 0) :=
  tendsto_dyadicTaylorRemainder (α := fun r => (clockWindowIntegral A h r ω).toReal)
    (β := fun r => (clockWindowIntegral A' h r ω).toReal) (fun _ => rfl) hT0
    (monotoneOn_clockWindowIntegral_toReal A h ω hT) (monotoneOn_clockWindowIntegral_toReal A' h ω hT')
    (continuousOn_clockWindowIntegral_toReal hc hm hh hT)
    (continuousOn_clockWindowIntegral_toReal hc' hm' hh hT')

/-- The dyadic Taylor remainders of `φ(N)`, `N = A^h - A'^h`, are bounded by `2 (A^h_T + A'^h_T)`. -/
theorem abs_dyadicTaylorRemainder_clockWindowIntegral_le (hT0 : 0 ≤ T)
    (hT : clockWindowIntegral A h T ω ≠ ∞) (hT' : clockWindowIntegral A' h T ω ≠ ∞) (n : ℕ) :
    |dyadicTaylorRemainder
      (fun r => (clockWindowIntegral A h r ω).toReal - (clockWindowIntegral A' h r ω).toReal) T n| ≤
      2 * ((clockWindowIntegral A h T ω).toReal + (clockWindowIntegral A' h T ω).toReal) := by
  have := abs_dyadicTaylorRemainder_le_of_forall (α := fun r => (clockWindowIntegral A h r ω).toReal)
    (β := fun r => (clockWindowIntegral A' h r ω).toReal) (fun _ => rfl) hT0
    (monotoneOn_clockWindowIntegral_toReal A h ω hT) (monotoneOn_clockWindowIntegral_toReal A' h ω hT')
    (n := n) zero_le_one (fun _ _ => min_le_right _ _)
  simpa using this

end path

/-- **A first-order Taylor term has mean zero.** For PCAFs `A`, `A'` with the same Revuz measure, rational times
`0 < q ≤ q + d` with `E_x[A^h_{q+d}]`, `E_x[A'^h_{q+d}]` finite, and `N_r = A^h_r - A'^h_r`,
`E_x[φ'(N_q) (N_{q+d} - N_q)] = 0`. -/
theorem integral_logOnePlusSqDeriv_mul_increment_eq_zero {A A' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hA' : IsPCAF planarLaw A') (hμ : revuz planarLaw A = revuz planarLaw A')
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) (hfin : ∫⁻ y, h y ∂revuz planarLaw A ≠ ∞) {x : ℂ} {q : ℚ≥0}
    (hq : q ≠ 0) (d : ℚ≥0)
    (hx : ∫⁻ ω, clockWindowIntegral A h (((q + d : ℚ≥0) : ℝ≥0) : ℝ) ω ∂planarLaw x ≠ ∞)
    (hx' : ∫⁻ ω, clockWindowIntegral A' h (((q + d : ℚ≥0) : ℝ≥0) : ℝ) ω ∂planarLaw x ≠ ∞) :
    ∫ ω, logOnePlusSqDeriv ((clockWindowIntegral A h ((q : ℝ≥0) : ℝ) ω).toReal -
        (clockWindowIntegral A' h ((q : ℝ≥0) : ℝ) ω).toReal) *
      (((clockWindowIntegral A h (((q + d : ℚ≥0) : ℝ≥0) : ℝ) ω).toReal -
          (clockWindowIntegral A' h (((q + d : ℚ≥0) : ℝ≥0) : ℝ) ω).toReal) -
        ((clockWindowIntegral A h ((q : ℝ≥0) : ℝ) ω).toReal -
          (clockWindowIntegral A' h ((q : ℝ≥0) : ℝ) ω).toReal)) ∂planarLaw x = 0 := by
  obtain ⟨Ψ, hΨm, hΨ⟩ := exists_canonicalFiltration_version_clockWindowIntegral_sub hA hA' hh x q
  have hcast : ((q + d : ℚ≥0) : ℝ≥0) = (q : ℝ≥0) + (d : ℝ≥0) := NNRat.cast_add q d
  have hs : (q : ℝ≥0) ≠ 0 := by exact_mod_cast hq
  rw [hcast] at hx hx' ⊢
  have key := integral_mul_clockWindowIntegral_increment_eq_zero hA hA' hμ hh hfin hs (d : ℝ≥0) hx hx'
    (G := fun ω => logOnePlusSqDeriv (Ψ ω)) (measurable_logOnePlusSqDeriv.comp hΨm)
    (fun ω => abs_logOnePlusSqDeriv_le_one _)
  rw [← key]
  refine integral_congr_ae ?_
  filter_upwards [hΨ] with ω hω
  rw [hω]

/-- **Two clocks with the same Revuz measure have the same window integrals.** Let `A`, `A'` be PCAFs of planar
Brownian motion with the same Revuz measure `μ`, and `h ≥ 0` Borel with `∫ h dμ < ∞`. If `E_x[A^h_t]` and
`E_x[A'^h_t]` are finite at the rational time `t`, then `A^h_t = A'^h_t` holds `P_x`-almost surely
(Fukushima–Oshima–Takeda (2011), proof of Theorem 5.1.4). -/
theorem ae_clockWindowIntegral_eq_of_revuz_eq {A A' : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hA' : IsPCAF planarLaw A') (hμ : revuz planarLaw A = revuz planarLaw A')
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) (hfin : ∫⁻ y, h y ∂revuz planarLaw A ≠ ∞) {x : ℂ} (t : ℚ≥0)
    (hx : ∫⁻ ω, clockWindowIntegral A h ((t : ℝ≥0) : ℝ) ω ∂planarLaw x ≠ ∞)
    (hx' : ∫⁻ ω, clockWindowIntegral A' h ((t : ℝ≥0) : ℝ) ω ∂planarLaw x ≠ ∞) :
    ∀ᵐ ω ∂planarLaw x,
      clockWindowIntegral A h ((t : ℝ≥0) : ℝ) ω = clockWindowIntegral A' h ((t : ℝ≥0) : ℝ) ω := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact ae_of_all _ fun ω => by simp
  set T : ℝ := ((t : ℝ≥0) : ℝ) with hTdef
  have hT0 : 0 ≤ T := NNReal.coe_nonneg _
  set μx := planarLaw x with hμx
  set N : ContinuousPath ℂ → ℝ → ℝ := fun ω r =>
    (clockWindowIntegral A h r ω).toReal - (clockWindowIntegral A' h r ω).toReal with hNdef
  have hwm : ∀ r, Measurable (clockWindowIntegral A h r) := measurable_clockWindowIntegral hA.meas hh
  have hwm' : ∀ r, Measurable (clockWindowIntegral A' h r) := measurable_clockWindowIntegral hA'.meas hh
  have hNm : ∀ r, Measurable fun ω => N ω r := fun r =>
    (hwm r).ennreal_toReal.sub (hwm' r).ennreal_toReal
  have hint : ∀ r ≤ T, Integrable (fun ω => (clockWindowIntegral A h r ω).toReal) μx := fun r hr =>
    integrable_toReal_of_lintegral_ne_top (hwm r).aemeasurable
      (ne_top_of_le_ne_top hx (lintegral_mono fun ω => clockWindowIntegral_mono A h hr ω))
  have hint' : ∀ r ≤ T, Integrable (fun ω => (clockWindowIntegral A' h r ω).toReal) μx := fun r hr =>
    integrable_toReal_of_lintegral_ne_top (hwm' r).aemeasurable
      (ne_top_of_le_ne_top hx' (lintegral_mono fun ω => clockWindowIntegral_mono A' h hr ω))
  have hNint : ∀ r ≤ T, Integrable (fun ω => N ω r) μx := fun r hr => (hint r hr).sub (hint' r hr)
  have hN0 : ∀ ω, N ω 0 = 0 := fun ω => by simp [hNdef]
  -- almost every path: continuous nondecreasing clocks, finite window integrals at `T`
  have hgood : ∀ᵐ ω ∂μx, (Continuous fun u => A u ω) ∧ (Monotone fun u => A u ω) ∧
      (Continuous fun u => A' u ω) ∧ (Monotone fun u => A' u ω) ∧
      clockWindowIntegral A h T ω ≠ ∞ ∧ clockWindowIntegral A' h T ω ≠ ∞ := by
    filter_upwards [hA.path x, hA'.path x, ae_lt_top (hwm T) hx, ae_lt_top (hwm' T) hx']
      with ω h1 h2 h3 h4
    exact ⟨h1.2.1, h1.2.2, h2.2.1, h2.2.2, h3.ne, h4.ne⟩
  -- the second-order remainders
  set R : ℕ → ContinuousPath ℂ → ℝ := fun n ω => dyadicTaylorRemainder (N ω) T n with hRdef
  have hRm : ∀ n, Measurable (R n) := fun n => by
    simp only [hRdef, dyadicTaylorRemainder]
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((measurable_logOnePlusSq.comp (hNm _)).sub (measurable_logOnePlusSq.comp (hNm _))).sub
      ((measurable_logOnePlusSqDeriv.comp (hNm _)).mul ((hNm _).sub (hNm _)))
  set bound : ContinuousPath ℂ → ℝ := fun ω =>
    2 * ((clockWindowIntegral A h T ω).toReal + (clockWindowIntegral A' h T ω).toReal) with hbdef
  have hbint : Integrable bound μx := ((hint T le_rfl).add (hint' T le_rfl)).const_mul 2
  have hRbound : ∀ n, ∀ᵐ ω ∂μx, ‖R n ω‖ ≤ bound ω := fun n => by
    filter_upwards [hgood] with ω hω
    rw [Real.norm_eq_abs]
    exact abs_dyadicTaylorRemainder_clockWindowIntegral_le hT0 hω.2.2.2.2.1 hω.2.2.2.2.2 n
  have hRint : ∀ n, Integrable (R n) μx := fun n =>
    Integrable.mono' hbint (hRm n).aestronglyMeasurable (hRbound n)
  have hRlim : ∀ᵐ ω ∂μx, Tendsto (fun n => R n ω) atTop (𝓝 0) := by
    filter_upwards [hgood] with ω hω
    exact tendsto_dyadicTaylorRemainder_clockWindowIntegral hh hω.1 hω.2.1 hω.2.2.1 hω.2.2.2.1 hT0
      hω.2.2.2.2.1 hω.2.2.2.2.2
  have hlimR : Tendsto (fun n => ∫ ω, R n ω ∂μx) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence bound (fun n => (hRm n).aestronglyMeasurable) hbint
      hRbound hRlim
    simpa using this
  -- the first-order terms
  have htint : ∀ n, ∀ k ∈ Finset.range (2 ^ n), Integrable (fun ω =>
      logOnePlusSqDeriv (N ω ((k : ℝ) * T / 2 ^ n)) *
        (N ω (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ω ((k : ℝ) * T / 2 ^ n))) μx := by
    intro n k hk
    have hk1 : k + 1 ≤ 2 ^ n := Finset.mem_range.1 hk
    have hΔ := (hNint _ (dyadic_mem_Icc hT0 hk1).2).sub (hNint _ (dyadic_mem_Icc hT0 (Nat.le_of_succ_le hk1)).2)
    refine Integrable.mono' hΔ.abs
      ((measurable_logOnePlusSqDeriv.comp (hNm _)).mul ((hNm _).sub (hNm _))).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_logOnePlusSqDeriv_le_one _)
  have hterm : ∀ n, ∀ k ∈ Finset.range (2 ^ n),
      ∫ ω, logOnePlusSqDeriv (N ω ((k : ℝ) * T / 2 ^ n)) *
        (N ω (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ω ((k : ℝ) * T / 2 ^ n)) ∂μx = 0 := by
    intro n k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [hN0, logOnePlusSqDeriv_zero]
    have hq : ((k : ℚ≥0) * t / 2 ^ n) ≠ 0 :=
      div_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 hk0.ne') ht) (pow_ne_zero _ two_ne_zero)
    have hc1 : ((((k : ℚ≥0) * t / 2 ^ n : ℚ≥0) : ℝ≥0) : ℝ) = (k : ℝ) * T / 2 ^ n := by
      rw [hTdef]; push_cast; ring
    have hc2 : ((((k : ℚ≥0) * t / 2 ^ n + t / 2 ^ n : ℚ≥0) : ℝ≥0) : ℝ) =
        ((k + 1 : ℕ) : ℝ) * T / 2 ^ n := by
      rw [hTdef]; push_cast; ring
    have hle : ((k + 1 : ℕ) : ℝ) * T / 2 ^ n ≤ T := (dyadic_mem_Icc hT0 (Finset.mem_range.1 hk)).2
    have h1 : ∫⁻ ω, clockWindowIntegral A h
        ((((k : ℚ≥0) * t / 2 ^ n + t / 2 ^ n : ℚ≥0) : ℝ≥0) : ℝ) ω ∂μx ≠ ∞ := by
      rw [hc2]
      exact ne_top_of_le_ne_top hx (lintegral_mono fun ω => clockWindowIntegral_mono A h hle ω)
    have h2 : ∫⁻ ω, clockWindowIntegral A' h
        ((((k : ℚ≥0) * t / 2 ^ n + t / 2 ^ n : ℚ≥0) : ℝ≥0) : ℝ) ω ∂μx ≠ ∞ := by
      rw [hc2]
      exact ne_top_of_le_ne_top hx' (lintegral_mono fun ω => clockWindowIntegral_mono A' h hle ω)
    have key := integral_logOnePlusSqDeriv_mul_increment_eq_zero hA hA' hμ hh hfin (x := x) hq (t / 2 ^ n)
      h1 h2
    rw [hc1, hc2] at key
    exact key
  -- `E_x φ(N_T) = E_x (remainder)` for every `n`
  have hdecomp : ∀ n, Integrable (fun ω => logOnePlusSq (N ω T)) μx ∧
      ∫ ω, logOnePlusSq (N ω T) ∂μx = ∫ ω, R n ω ∂μx := by
    intro n
    have hexp : ∀ ω, logOnePlusSq (N ω T) = (∑ k ∈ Finset.range (2 ^ n),
        logOnePlusSqDeriv (N ω ((k : ℝ) * T / 2 ^ n)) *
          (N ω (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ω ((k : ℝ) * T / 2 ^ n))) + R n ω :=
      fun ω => logOnePlusSq_eq_sum_add_dyadicTaylorRemainder (hN0 ω) T n
    have hsumint := integrable_finsetSum _ (htint n)
    have hfun : (fun ω => logOnePlusSq (N ω T)) = fun ω => (∑ k ∈ Finset.range (2 ^ n),
        logOnePlusSqDeriv (N ω ((k : ℝ) * T / 2 ^ n)) *
          (N ω (((k + 1 : ℕ) : ℝ) * T / 2 ^ n) - N ω ((k : ℝ) * T / 2 ^ n))) + R n ω := funext hexp
    refine ⟨hfun ▸ hsumint.add (hRint n), ?_⟩
    rw [hfun, integral_add hsumint (hRint n), integral_finsetSum _ (htint n),
      Finset.sum_eq_zero (hterm n), zero_add]
  have hφ0 : ∫ ω, logOnePlusSq (N ω T) ∂μx = 0 := by
    have : Tendsto (fun _ : ℕ => ∫ ω, logOnePlusSq (N ω T) ∂μx) atTop (𝓝 0) :=
      hlimR.congr fun n => ((hdecomp n).2).symm
    exact tendsto_const_nhds_iff.1 this
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => logOnePlusSq_nonneg _) (hdecomp 0).1).1 hφ0
  filter_upwards [hae, hgood] with ω h1 h2
  have h3 : N ω T = 0 := eq_zero_of_logOnePlusSq_eq_zero h1
  exact (ENNReal.toReal_eq_toReal_iff' h2.2.2.2.2.1 h2.2.2.2.2.2).1 (sub_eq_zero.1 h3)

end MatedCRT
