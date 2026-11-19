import MatedCRT.FirstPass.Derived.RevuzInvariantDefect
import MatedCRT.FirstPass.Derived.RevuzHarrisExpectation
import MatedCRT.FirstPass.Derived.RevuzClockInverseIntegral

/-!
# Invariance of the Revuz measure under the time change

Let `A` be a positive continuous additive functional of planar Brownian motion with a good clock, Revuz measure
`μ = μ_A`, time-change kernels `P_u` and defects `D_h = μ − μ P_h` (`revuzDefect`). For a Borel set `E` with
`μ(E) ≠ 0`, the change of variables `s = τ_r` along a good path and the expectation form of the Harris recurrence
(`lintegral_setLIntegral_Ioi_eq_top`) give `∫_{(0,∞)} P_r(x, E) dr = ∞` for every starting point `x`. On the other
hand, integrating `∑_{k<n} (D_h P_{s+kh})(E) ≤ μ(E)` over `s ∈ (0, h]` gives
`∫ D_h(dx) ∫_{(0,∞)} P_r(x, E) dr ≤ h μ(E)`. Choosing `0 < μ(E) < ∞` (`μ` is `σ`-finite) forces `D_h = 0` for
`h > 0`, that is `μ P_h = μ`; for `h = 0`, `P_0(x, ·)` is the Dirac mass at `x`. This is the passage from excessive
to invariant measures for a recurrent time change (Azéma–Duflo–Revuz (1969), §§2–3; Revuz–Yor (1999), Chapter X,
§3).

## Main results

* `setLIntegral_Ioi_timeChangeKernel_eq_top`: `∫_{(0,∞)} P_r(x, E) dr = ∞` when `μ(E) ≠ 0`;
* `lintegral_setLIntegral_Ioi_timeChangeKernel_revuzDefect_le`: `∫ D_h(dx) ∫_{(0,∞)} P_r(x, E) dr ≤ h μ(E)`;
* `revuzDefect_eq_zero`, `bind_timeChangeKernel_revuz_eq`: `μ P_u = μ` for every level `u`;
* `isInvTC_revuz`, `revuzInvariantInput_derived`: the input `RevuzInvariantInput` holds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess _root_.HarmonicBalls

/-- The Lebesgue integral over a translated interval. -/
theorem setLIntegral_Ioc_comp_add_right (f : ℝ → ℝ≥0∞) (a b c : ℝ) :
    ∫⁻ s in Ioc a b, f (s + c) = ∫⁻ r in Ioc (a + c) (b + c), f r := by
  rw [(measurePreserving_add_right volume c).setLIntegral_comp_emb
    (MeasurableEquiv.addRight c).measurableEmbedding f (Ioc a b)]
  simp only [image_add_const_Ioc]

/-- `∫_{(0,∞)} f = ∑_k ∫_{(0,h]} f(s + kh)` for `h > 0`. -/
theorem setLIntegral_Ioi_eq_tsum_Ioc {h : ℝ} (hh : 0 < h) (f : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi (0 : ℝ), f r = ∑' k : ℕ, ∫⁻ s in Ioc (0 : ℝ) h, f (s + k * h) := by
  have hU : (⋃ n : ℕ, Ioc (0 : ℝ) (n * h)) = Ioi 0 :=
    iUnion_Ioc_eq_Ioi_self_iff.2 fun x _ => by
      obtain ⟨n, hn⟩ := exists_nat_ge (x / h)
      exact ⟨n, by rwa [div_le_iff₀ hh] at hn⟩
  have hmono : Monotone fun n : ℕ => Ioc (0 : ℝ) (n * h) := fun m n hmn =>
    Ioc_subset_Ioc_right (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hmn) hh.le)
  have hn : ∀ n : ℕ, ∫⁻ r in Ioc (0 : ℝ) (n * h), f r =
      ∑ k ∈ Finset.range n, ∫⁻ s in Ioc (0 : ℝ) h, f (s + k * h) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ((n + 1 : ℕ) : ℝ) * h = h + n * h := by push_cast; ring
      rw [Finset.sum_range_succ, ← ih, setLIntegral_Ioc_comp_add_right, zero_add, e,
        ← lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl),
        Ioc_union_Ioc_eq_Ioc (mul_nonneg n.cast_nonneg hh.le) (by linarith)]
  rw [← hU, setLIntegral_iUnion_of_directed _ hmono.directed_le, ENNReal.tsum_eq_iSup_nat]
  exact iSup_congr hn

/-- Along a path where the clock `A · ω` starts at `0`, is continuous, strictly increasing and unbounded, the
integral against `dA_s` over `(0, ∞)` is the integral over `r ∈ (0, ∞)` at the time change `τ_r`. -/
theorem setLIntegral_Ioi_stieltjes_clock_eq_clockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {ω : ContinuousPath ℂ} (h0 : A 0 ω = 0) (hc : Continuous fun t => A t ω)
    (hs : StrictMono fun t => A t ω) (hu : Tendsto (fun t => A t ω) atTop atTop)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ s in Ioi (0 : ℝ), F s ∂(stieltjesOfNNReal fun t => A t ω).measure =
      ∫⁻ r in Ioi (0 : ℝ), F (clockInverse A r.toNNReal ω : ℝ) := by
  have hU1 : (⋃ n : ℕ, Ioc (0 : ℝ) n) = Ioi 0 :=
    iUnion_Ioc_eq_Ioi_self_iff.2 fun x _ => exists_nat_ge x
  have hU2 : (⋃ n : ℕ, Ioc (0 : ℝ) (A n ω)) = Ioi 0 :=
    iUnion_Ioc_eq_Ioi_self_iff.2 fun x _ => by
      obtain ⟨n, hn⟩ :=
        ((hu.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop x.toNNReal).exists
      exact ⟨n, Real.toNNReal_le_iff_le_coe.1 hn⟩
  have hm1 : Monotone fun n : ℕ => Ioc (0 : ℝ) n := fun m n hmn =>
    Ioc_subset_Ioc_right (Nat.cast_le.2 hmn)
  have hm2 : Monotone fun n : ℕ => Ioc (0 : ℝ) (A n ω) := fun m n hmn =>
    Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (hs.monotone (Nat.cast_le.2 hmn)))
  conv_lhs => rw [← hU1]
  conv_rhs => rw [← hU2]
  rw [setLIntegral_iUnion_of_directed _ hm1.directed_le,
    setLIntegral_iUnion_of_directed _ hm2.directed_le]
  refine iSup_congr fun n => ?_
  rw [setLIntegral_stieltjes_clock_Ioc_eq_clockInverse hc hs hu hF]
  simp [h0]

/-- Joint measurability of the regularized time-changed position `(u, ω) ↦ B_{τ_u}(ω)`. -/
theorem measurable_timeChangeRegularized_uncurry {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) :
    Measurable fun p : ℝ≥0 × ContinuousPath ℂ => timeChangeRegularized A p.1 p.2 :=
  measurable_path_eval_uncurry.comp
    ((measurable_clockInverse_uncurry (measurable_regularize hA) (regularize_monotone A)).prodMk
      measurable_snd)

/-- `P_u(x, E) = E_x[1_E(B_{τ_u})]`, with the regularized clock. -/
theorem timeChangeKernel_apply_eq_lintegral {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (u : ℝ≥0) (x : ℂ) {E : Set ℂ} (hE : MeasurableSet E) :
    timeChangeKernel A u x E =
      ∫⁻ ω, E.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A u ω) ∂planarLaw x := by
  calc timeChangeKernel A u x E = ∫⁻ y, E.indicator 1 y ∂timeChangeKernel A u x :=
        (lintegral_indicator_one hE).symm
    _ = _ := by
        rw [timeChangeKernel, Kernel.map_apply _ (measurable_timeChangeRegularized hA u),
          lintegral_map (measurable_one.indicator hE) (measurable_timeChangeRegularized hA u)]
        rfl

/-- Joint measurability of `(r, x) ↦ P_{r⁺}(x, E)`. -/
theorem measurable_timeChangeKernel_apply_uncurry {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) {E : Set ℂ} (hE : MeasurableSet E) :
    Measurable fun p : ℝ × ℂ => timeChangeKernel A p.1.toNNReal p.2 E := by
  simp_rw [timeChangeKernel_apply_eq_lintegral hA _ _ hE]
  exact Measurable.lintegral_kernel_prod_right' (κ := Kernel.prodMkLeft ℝ planarBrownianMotion)
    ((measurable_one.indicator hE).comp ((measurable_timeChangeRegularized_uncurry hA).comp
      ((measurable_real_toNNReal.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)))

/-- Measurability of `a ↦ P_{f(a)⁺}(g(a), E)` for measurable `f` and `g`. -/
theorem measurable_timeChangeKernel_apply_comp {α : Type*} [MeasurableSpace α]
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : ∀ t, Measurable (A t)) {E : Set ℂ} (hE : MeasurableSet E)
    {f : α → ℝ} {g : α → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => timeChangeKernel A (f a).toNNReal (g a) E := by
  simpa only [Function.comp_def] using (measurable_timeChangeKernel_apply_uncurry hA hE).comp (hf.prodMk hg)

/-- **The time-changed occupation of a set of positive Revuz measure is infinite.** For a positive continuous
additive functional `A` of planar Brownian motion with a good clock and a Borel set `E` with `μ_A(E) ≠ 0`, for every
starting point `x`, `∫_{(0,∞)} P_r(x, E) dr = ∞`. -/
theorem setLIntegral_Ioi_timeChangeKernel_eq_top {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {E : Set ℂ} (hE : MeasurableSet E)
    (hμE : revuz planarLaw A E ≠ 0) (x : ℂ) :
    ∫⁻ r in Ioi (0 : ℝ), timeChangeKernel A r.toNNReal x E = ∞ := by
  have : IsProbabilityMeasure (planarLaw x) := by unfold planarLaw; infer_instance
  have hg : Measurable (E.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hE
  have hjoint : Measurable fun p : ℝ × ContinuousPath ℂ =>
      E.indicator (1 : ℂ → ℝ≥0∞) (timeChangeRegularized A p.1.toNNReal p.2) :=
    hg.comp ((measurable_timeChangeRegularized_uncurry hA.meas).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  simp_rw [timeChangeKernel_apply_eq_lintegral hA.meas _ x hE]
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  refine (lintegral_congr_ae ?_).trans
    (lintegral_setLIntegral_Ioi_eq_top hA hg (by rwa [lintegral_indicator_one hE]) x)
  filter_upwards [hA.path x, hG x, ae_eval_clockInverse_eq_timeChangeRegularized hA x] with ω hp hg' hω
  rw [setLIntegral_Ioi_stieltjes_clock_eq_clockInverse hp.1 hp.2.1 hg'.1 hg'.2
    (F := fun s : ℝ => E.indicator (1 : ℂ → ℝ≥0∞) (ω s.toNNReal))
    (hg.comp (ω.continuous.comp continuous_real_toNNReal).measurable)]
  simp only [Real.toNNReal_coe, hω]

/-- Splitting the time-changed occupation, integrated against an `s`-finite measure `ν`, into windows of
length `h > 0`: `∫ ν(dx) ∫_{(0,∞)} P_r(x, E) dr = ∫_{(0,h]} ∑_k (ν P_{s+kh})(E) ds`. -/
theorem lintegral_setLIntegral_Ioi_timeChangeKernel_eq_tsum {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (ν : Measure ℂ) [SFinite ν] {h : ℝ≥0} (hh : 0 < h) {E : Set ℂ}
    (hE : MeasurableSet E) :
    ∫⁻ x, (∫⁻ r in Ioi (0 : ℝ), timeChangeKernel A r.toNNReal x E) ∂ν =
      ∫⁻ s in Ioc (0 : ℝ) h, ∑' k : ℕ, (timeChangeKernel A (s + k * h).toNNReal ∘ₘ ν) E := by
  have hk : ∀ k : ℕ, Measurable fun p : ℝ × ℂ =>
      timeChangeKernel A (p.1 + k * h).toNNReal p.2 E :=
    fun k => measurable_timeChangeKernel_apply_comp hA hE (measurable_fst.add_const _) measurable_snd
  have hk' : ∀ k : ℕ, Measurable fun q : ℂ × ℝ =>
      timeChangeKernel A (q.2 + k * h).toNNReal q.1 E :=
    fun k => measurable_timeChangeKernel_apply_comp hA hE (measurable_snd.add_const _) measurable_fst
  have hmx : ∀ k : ℕ, Measurable fun x : ℂ =>
      ∫⁻ s in Ioc (0 : ℝ) h, timeChangeKernel A (s + k * h).toNNReal x E :=
    fun k => (hk' k).lintegral_prod_right'
  have hms : ∀ k : ℕ, Measurable fun s : ℝ =>
      ∫⁻ x, timeChangeKernel A (s + k * h).toNNReal x E ∂ν :=
    fun k => (hk k).lintegral_prod_right'
  calc ∫⁻ x, (∫⁻ r in Ioi (0 : ℝ), timeChangeKernel A r.toNNReal x E) ∂ν
      = ∫⁻ x, (∑' k : ℕ, ∫⁻ s in Ioc (0 : ℝ) h, timeChangeKernel A (s + k * h).toNNReal x E) ∂ν :=
        lintegral_congr fun x =>
          setLIntegral_Ioi_eq_tsum_Ioc (NNReal.coe_pos.2 hh) fun r => timeChangeKernel A r.toNNReal x E
    _ = ∑' k : ℕ, ∫⁻ x, (∫⁻ s in Ioc (0 : ℝ) h, timeChangeKernel A (s + k * h).toNNReal x E) ∂ν :=
        lintegral_tsum fun k => (hmx k).aemeasurable
    _ = ∑' k : ℕ, ∫⁻ s in Ioc (0 : ℝ) h, ∫⁻ x, timeChangeKernel A (s + k * h).toNNReal x E ∂ν :=
        tsum_congr fun k => lintegral_lintegral_swap (hk' k).aemeasurable
    _ = ∫⁻ s in Ioc (0 : ℝ) h, ∑' k : ℕ, ∫⁻ x, timeChangeKernel A (s + k * h).toNNReal x E ∂ν :=
        (lintegral_tsum fun k => (hms k).aemeasurable).symm
    _ = ∫⁻ s in Ioc (0 : ℝ) h, ∑' k : ℕ, (timeChangeKernel A (s + k * h).toNNReal ∘ₘ ν) E := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun s _ => tsum_congr fun k => ?_
        rw [Measure.bind_apply hE (Kernel.aemeasurable _)]

/-- **The defect against the time-changed occupation**: `∫ D_h(dx) ∫_{(0,∞)} P_r(x, E) dr ≤ h μ_A(E)` for `h > 0`,
by integrating `∑_{k<n} (D_h P_{s+kh})(E) ≤ μ_A(E)` over `s ∈ (0, h]`. -/
theorem lintegral_setLIntegral_Ioi_timeChangeKernel_revuzDefect_le {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {h : ℝ≥0} (hh : 0 < h) {E : Set ℂ}
    (hE : MeasurableSet E) :
    ∫⁻ x, (∫⁻ r in Ioi (0 : ℝ), timeChangeKernel A r.toNNReal x E) ∂revuzDefect A h ≤
      (h : ℝ≥0∞) * revuz planarLaw A E := by
  have : SigmaFinite (revuz planarLaw A) := sigmaFinite_revuz hA hG
  have : SFinite (revuzDefect A h) := by unfold revuzDefect; infer_instance
  rw [lintegral_setLIntegral_Ioi_timeChangeKernel_eq_tsum hA.meas _ hh hE]
  calc ∫⁻ s in Ioc (0 : ℝ) h, ∑' k : ℕ, (timeChangeKernel A (s + k * h).toNNReal ∘ₘ revuzDefect A h) E
      = ∫⁻ s in Ioc (0 : ℝ) h, ∑' k : ℕ,
          (timeChangeKernel A (s.toNNReal + k * h) ∘ₘ revuzDefect A h) E := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => tsum_congr fun k => ?_
        have e : (s + k * h : ℝ).toNNReal = s.toNNReal + k * h := by
          apply NNReal.eq
          rw [Real.coe_toNNReal _ (add_nonneg hs.1.le (by positivity)), NNReal.coe_add,
            Real.coe_toNNReal _ hs.1.le]
          norm_cast
        rw [e]
    _ ≤ ∫⁻ _ in Ioc (0 : ℝ) h, revuz planarLaw A E :=
        lintegral_mono fun s => ENNReal.tsum_le_of_sum_range_le fun n =>
          sum_bind_timeChangeKernel_revuzDefect_le hA hG h s.toNNReal hE n
    _ = (h : ℝ≥0∞) * revuz planarLaw A E := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_coe_nnreal, mul_comm]

/-- **The defect of the Revuz measure vanishes**: `D_h = 0` for `h > 0`. -/
theorem revuzDefect_eq_zero {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) {h : ℝ≥0} (hh : 0 < h) :
    revuzDefect A h = 0 := by
  have : SigmaFinite (revuz planarLaw A) := sigmaFinite_revuz hA hG
  by_cases hμ : revuz planarLaw A = 0
  · rw [revuzDefect, hμ, withDensity_zero_left]
  obtain ⟨n, hn⟩ : ∃ n, revuz planarLaw A (spanningSets (revuz planarLaw A) n) ≠ 0 := by
    by_contra hcon
    apply hμ
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (revuz planarLaw A)]
    exact measure_iUnion_null fun i => not_not.1 (not_exists.1 hcon i)
  have hE := measurableSet_spanningSets (revuz planarLaw A) n
  have hfin := measure_spanningSets_lt_top (revuz planarLaw A) n
  have hle := lintegral_setLIntegral_Ioi_timeChangeKernel_revuzDefect_le hA hG hh hE
  simp_rw [setLIntegral_Ioi_timeChangeKernel_eq_top hA hG hE hn] at hle
  rw [lintegral_const] at hle
  refine Measure.measure_univ_eq_zero.1 ?_
  by_contra hD
  rw [ENNReal.top_mul hD] at hle
  exact lt_irrefl (∞ : ℝ≥0∞) (lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin))

/-- `P_0(x, ·)` is the Dirac mass at `x`. -/
theorem timeChangeKernel_zero_apply {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (x : ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    timeChangeKernel A 0 x S = S.indicator 1 x := by
  have : IsProbabilityMeasure (planarLaw x) := by unfold planarLaw; infer_instance
  have hae : (fun ω : ContinuousPath ℂ => ω (clockInverse A 0 ω)) =ᵐ[planarLaw x] fun _ => x := by
    filter_upwards [hA.path x, hG x, ae_planarLaw_eval_zero x] with ω hp hg hω0
    have hset : {t : ℝ≥0 | (0 : ℝ≥0) < A t ω} = Ioi 0 := by
      ext t
      show (0 : ℝ≥0) < A t ω ↔ 0 < t
      constructor
      · intro ht
        refine pos_iff_ne_zero.2 fun ht0 => ?_
        rw [ht0, hp.1] at ht
        exact lt_irrefl 0 ht
      · intro ht
        simpa [hp.1] using hg.1 ht
    show ω (sInf {t | (0 : ℝ≥0) < A t ω}) = x
    rw [hset, csInf_Ioi, hω0]
  rw [timeChangeKernel_eq_map hA, Measure.map_congr hae, Measure.map_const, measure_univ, one_smul,
    Measure.dirac_apply' _ hS]

/-- **The Revuz measure is invariant for the time change**: `μ_A P_u = μ_A` for every level `u`. -/
theorem bind_timeChangeKernel_revuz_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (u : ℝ≥0) :
    timeChangeKernel A u ∘ₘ revuz planarLaw A = revuz planarLaw A := by
  rcases eq_zero_or_pos u with rfl | hu
  · ext S hS
    rw [Measure.bind_apply hS (Kernel.aemeasurable _)]
    calc ∫⁻ x, timeChangeKernel A 0 x S ∂revuz planarLaw A
        = ∫⁻ x, S.indicator 1 x ∂revuz planarLaw A :=
          lintegral_congr fun x => timeChangeKernel_zero_apply hA hG x hS
      _ = revuz planarLaw A S := lintegral_indicator_one hS
  · have := revuz_eq_bind_add_revuzDefect hA hG u
    rw [revuzDefect_eq_zero hA hG hu, add_zero] at this
    exact this.symm

/-- **The Revuz measure of a PCAF with a good clock is invariant for its time change.** -/
theorem isInvTC_revuz {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) :
    IsInvTC planarLaw A (revuz planarLaw A) :=
  (isInvTC_iff hA _).2 (bind_timeChangeKernel_revuz_eq hA hG)

/-- **`RevuzInvariantInput` holds**: the Revuz measure of a PCAF of planar Brownian motion with a good clock is
`σ`-finite and invariant for its time change. -/
theorem revuzInvariantInput_derived : RevuzInvariantInput :=
  fun _ hA hG => ⟨sigmaFinite_revuz hA hG, isInvTC_revuz hA hG⟩

end MatedCRT
