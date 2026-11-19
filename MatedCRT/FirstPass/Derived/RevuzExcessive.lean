import MatedCRT.FirstPass.Derived.RevuzExcessiveSpaceTime

/-!
# Excessiveness of the Revuz measure for the time change

Let `A` be a positive continuous additive functional of planar Brownian motion with a good clock and Revuz measure
`μ_A`, with rational-time regularization `Ā`, right inverse `τ̄` of `Ā` and time-changed position `Ȳ_u = B_{τ̄_u}`.
For every level `u` and Borel set `S`,
`∫ μ_A(dy) P_y[B_{τ_u} ∈ S] ≤ μ_A(S)`, that is `μ_A P_u ≤ μ_A` for the transition kernel `P_u` of the time change.

The integrated bound `∫ μ_A(dy) E_y[(N − τ̄_u)⁺ 1_S(Ȳ_u)] ≤ N μ_A(S)` with `N = n + 1`, divided by `n + 1`, gives
`∫ μ_A(dy) E_y[(1 − τ̄_u/(n + 1))⁺ 1_S(Ȳ_u)] ≤ μ_A(S)`; the weights increase to `1_S(Ȳ_u)` as `n → ∞`, and
monotone convergence, first under `P_y` and then under `μ_A`, concludes. This is the excessiveness of the Revuz
measure for the time-changed process (Azéma–Duflo–Revuz (1969), §2; Revuz–Yor (1999), Chapter X, §3).

## Main results

* `truncatedHittingWeight`: the weight `(1 − τ̄_u/(n + 1))⁺ 1_S(Ȳ_u)`, measurable, increasing in `n`, with
  supremum `1_S(Ȳ_u)`;
* `lintegral_revuz_truncatedHittingWeight_le`: its `μ_A`-integrated expectation is at most `μ_A(S)`;
* `lintegral_revuz_planarLaw_clockInverse_mem_le`: `∫ μ_A(dy) P_y[B_{τ_u} ∈ S] ≤ μ_A(S)`;
* `bind_revuz_timeChangeKernel_le`: `μ_A P_u ≤ μ_A`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess _root_.HarmonicBalls

/-- The truncated weight `(1 − τ̄_u/(n + 1))⁺ 1_S(Ȳ_u)` of the time-changed position. -/
noncomputable def truncatedHittingWeight (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u : ℝ≥0) (S : Set ℂ) (n : ℕ)
    (ω' : ContinuousPath ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - (clockInverse (regularize A) u ω' : ℝ) / ((n + 1 : ℕ) : ℝ)) *
    S.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A u ω')

theorem measurable_truncatedHittingWeight {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t))
    (u : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) (n : ℕ) : Measurable (truncatedHittingWeight A u S n) := by
  have hc : Measurable fun ω : ContinuousPath ℂ => clockInverse (regularize A) u ω :=
    (measurable_clockInverse_uncurry (measurable_regularize hA) (regularize_monotone A)).comp
      (measurable_const.prodMk measurable_id)
  exact (ENNReal.measurable_ofReal.comp (measurable_const.sub
    (hc.coe_nnreal_real.div_const _))).mul
    ((measurable_one.indicator hS).comp (measurable_timeChangeRegularized hA u))

/-- `(1 − c/(n + 1))⁺` increases with `n` for `c ≥ 0`. -/
theorem monotone_ofReal_one_sub_div_succ {c : ℝ} (hc : 0 ≤ c) :
    Monotone fun n : ℕ => ENNReal.ofReal (1 - c / ((n + 1 : ℕ) : ℝ)) := by
  intro n m hnm
  dsimp only
  gcongr

/-- `(1 − c/(n + 1))⁺` increases to `1`. -/
theorem iSup_ofReal_one_sub_div_succ {c : ℝ} (hc : 0 ≤ c) :
    ⨆ n : ℕ, ENNReal.ofReal (1 - c / ((n + 1 : ℕ) : ℝ)) = 1 := by
  have h0 : Tendsto (fun n : ℕ => c / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 1)
  have h1 : Tendsto (fun n : ℕ => 1 - c / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h0
  rw [sub_zero] at h1
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 - c / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
    simpa using ENNReal.tendsto_ofReal h1
  exact tendsto_nhds_unique (tendsto_atTop_iSup (monotone_ofReal_one_sub_div_succ hc)) hlim

theorem truncatedHittingWeight_mono (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u : ℝ≥0) (S : Set ℂ)
    (ω' : ContinuousPath ℂ) : Monotone fun n => truncatedHittingWeight A u S n ω' :=
  fun _ _ h => by
    dsimp only [truncatedHittingWeight]
    gcongr ?_ * _
    exact monotone_ofReal_one_sub_div_succ (NNReal.coe_nonneg _) h

/-- The truncated weights increase to `1_S(Ȳ_u)`. -/
theorem iSup_truncatedHittingWeight (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (u : ℝ≥0) (S : Set ℂ)
    (ω' : ContinuousPath ℂ) :
    ⨆ n, truncatedHittingWeight A u S n ω' = S.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A u ω') := by
  simp only [truncatedHittingWeight]
  rw [← ENNReal.iSup_mul, iSup_ofReal_one_sub_div_succ (NNReal.coe_nonneg _), one_mul]

/-- **The `μ_A`-integrated truncated weight is at most `μ_A(S)`.** -/
theorem lintegral_revuz_truncatedHittingWeight_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (u : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S)
    (n : ℕ) :
    ∫⁻ y, ∫⁻ ω', truncatedHittingWeight A u S n ω' ∂planarLaw y ∂revuz planarLaw A ≤ revuz planarLaw A S := by
  have hm0 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
  have hmt : ((n + 1 : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hmr : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.succ_pos n)
  have hpt : ∀ ω', ENNReal.ofReal ((((n + 1 : ℕ) : ℝ≥0) : ℝ) - clockInverse (regularize A) u ω') *
      S.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A u ω') =
        ((n + 1 : ℕ) : ℝ≥0∞) * truncatedHittingWeight A u S n ω' := by
    intro ω'
    rw [truncatedHittingWeight, ← mul_assoc, NNReal.coe_natCast]
    congr 1
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hmr.le]
    congr 1
    rw [mul_sub, mul_one, mul_div_assoc', mul_div_cancel_left₀ _ hmr.ne']
  refine (ENNReal.mul_le_mul_iff_right hm0 hmt).1 ?_
  calc ((n + 1 : ℕ) : ℝ≥0∞) * ∫⁻ y, ∫⁻ ω', truncatedHittingWeight A u S n ω' ∂planarLaw y ∂revuz planarLaw A
      = ∫⁻ y, ∫⁻ ω', ((n + 1 : ℕ) : ℝ≥0∞) * truncatedHittingWeight A u S n ω' ∂planarLaw y
          ∂revuz planarLaw A := by
        rw [← lintegral_const_mul' _ _ hmt]
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul' _ _ hmt]
    _ = ∫⁻ y, ∫⁻ ω', ENNReal.ofReal ((((n + 1 : ℕ) : ℝ≥0) : ℝ) - clockInverse (regularize A) u ω') *
          S.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A u ω') ∂planarLaw y ∂revuz planarLaw A :=
        lintegral_congr fun y => lintegral_congr fun ω' => (hpt ω').symm
    _ ≤ (((n + 1 : ℕ) : ℝ≥0) : ℝ≥0∞) * revuz planarLaw A S :=
        lintegral_revuz_truncatedHitting_le hA hG u ((n + 1 : ℕ) : ℝ≥0) hS
    _ = ((n + 1 : ℕ) : ℝ≥0∞) * revuz planarLaw A S := by rw [ENNReal.coe_natCast]

/-- **Excessiveness, regularized form**: `∫ μ_A(dy) P_y[Ȳ_u ∈ S] ≤ μ_A(S)`. -/
theorem lintegral_revuz_timeChangeRegularized_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (u : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) :
    ∫⁻ y, planarLaw y (timeChangeRegularized A u ⁻¹' S) ∂revuz planarLaw A ≤ revuz planarLaw A S := by
  have hY := measurable_timeChangeRegularized hA.meas u
  have hF : ∀ n, Measurable fun y => ∫⁻ ω', truncatedHittingWeight A u S n ω' ∂planarLaw y := fun n =>
    (measurable_truncatedHittingWeight hA.meas u hS n).lintegral_kernel (κ := planarBrownianMotion)
  calc ∫⁻ y, planarLaw y (timeChangeRegularized A u ⁻¹' S) ∂revuz planarLaw A
      = ∫⁻ y, ⨆ n, ∫⁻ ω', truncatedHittingWeight A u S n ω' ∂planarLaw y ∂revuz planarLaw A := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_iSup (measurable_truncatedHittingWeight hA.meas u hS)
          (fun n m h ω' => truncatedHittingWeight_mono A u S ω' h)]
        simp_rw [iSup_truncatedHittingWeight]
        rw [← lintegral_indicator_one (hY hS)]
        rfl
    _ = ⨆ n, ∫⁻ y, ∫⁻ ω', truncatedHittingWeight A u S n ω' ∂planarLaw y ∂revuz planarLaw A :=
        lintegral_iSup hF fun n m h y => lintegral_mono fun ω' => truncatedHittingWeight_mono A u S ω' h
    _ ≤ revuz planarLaw A S := iSup_le fun n => lintegral_revuz_truncatedHittingWeight_le hA hG u hS n

/-- **Excessiveness of the Revuz measure for the time change**: for a PCAF of planar Brownian motion with a good
clock, every level `u` and Borel set `S`, `∫ μ_A(dy) P_y[B_{τ_u} ∈ S] ≤ μ_A(S)`. -/
theorem lintegral_revuz_planarLaw_clockInverse_mem_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (u : ℝ≥0) {S : Set ℂ} (hS : MeasurableSet S) :
    ∫⁻ y, planarLaw y {ω | ω (clockInverse A u ω) ∈ S} ∂revuz planarLaw A ≤ revuz planarLaw A S :=
  (lintegral_congr fun y => planarLaw_eval_clockInverse_mem hA y u S).trans_le
    (lintegral_revuz_timeChangeRegularized_le hA hG u hS)

/-- **Excessiveness, kernel form**: `μ_A P_u ≤ μ_A` for the transition kernel `P_u` of the time change. -/
theorem bind_revuz_timeChangeKernel_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (u : ℝ≥0) :
    (revuz planarLaw A).bind (timeChangeKernel A u) ≤ revuz planarLaw A := by
  refine Measure.le_iff.2 fun S hS => ?_
  rw [Measure.bind_apply hS (timeChangeKernel A u).measurable.aemeasurable]
  exact (lintegral_congr fun y => timeChangeKernel_apply hA u y hS).trans_le
    (lintegral_revuz_planarLaw_clockInverse_mem_le hA hG u hS)

end MatedCRT
