import MatedCRT.FirstPass.Derived.WholePlaneClockStrictMonoFixedStart
import MatedCRT.FirstPass.Derived.NormalizedGFFCoordinateBridge

/-!
# Strict monotonicity of the fixed-start Liouville clock from the one-start positivity of its increments

Berestycki (2015) shows that the increment `G_{a,b} = lim_k (A_k(b) - A_k(a))` of the Liouville clock of planar Brownian
motion started at the origin over a fixed interval `[a, b]`, `0 < a < b`, is almost surely positive, where
`A_k(t) = ∫_0^t ε_k^{γ²/2} e^{γ h_{ε_k}(B_s)} ds` and `ε_k = 2^{-k}`. This file derives from that one-start event, for
the normalized whole-plane Gaussian free field and the convergence of the dyadic clocks from almost every fixed start,
the strict monotonicity of the limit clock from almost every fixed start, almost surely for the joint law of the field
and the Brownian path: the hypothesis `hfixsm` of `Sec1.hasReferenceEnvironments_of_coupling_wholePlane_fixedStart`.

The one-start event is taken in the form of the whole-plane Gaussian free field of `LatticeProb.Gauss`
(`LatticeProb.Gauss.IsWholePlaneGFF`, field `LatticeProb.Gauss.fieldCircleAverage 0 hcirc`): almost surely in the
field, for all rationals `0 < a < b`, from the origin, almost surely the lower limit of
`ENNReal.ofReal (∫_a^b ε_k^{γ²/2} e^{γ h_{ε_k}(w_v)} dv)` is positive.

The argument:
* a normalized whole-plane GFF `Y'` has a `LatticeProb.Gauss` representation whose circle averages agree almost surely
  with those of `Y'` at each radius and centre (`MatedCRT.exists_normalizedGFF_coordinates`); two versions that are
  continuous on `(0, ∞) × ℂ` and agree almost surely at each point agree almost surely everywhere there
  (`ae_forall_eq_of_continuousOn_of_ae_eq`, through a countable dense set), so the one-start event holds for every
  continuous version `c'` of the circle averages of `Y'`;
* the increment of the clock over `[a, b]` is the clock of the path shifted by `a` at time `b - a`
  (`lqgClockApprox_add_eq_add_shift`), an event of the path after time `a > 0`. From the origin it holds after time
  `a` almost surely, hence from Lebesgue-almost every start (simple Markov property at time `a`, and Lebesgue measure
  is absolutely continuous with respect to the heat kernel at time `a`, `ae_start_of_ae_shift_start`), hence after
  time `a` from every start (`ae_planarBrownianMotion_shift_of_ae_start`);
* where the dyadic clocks are uniformly Cauchy on compact time intervals, positive increments between positive
  rational times make the nondecreasing limit clock strictly increasing
  (`strictMono_limitAfterPositiveTimes_of_pos_increments`);
* the event of positive increments is measurable in the field and the path, so the quenched statement gives the
  statement for the joint law from every start.

## Main statements

* `ae_strictMono_wholePlane_fixedStart_of_oneStart`: the fixed-start strict monotonicity from the one-start event and
  the fixed-start convergence, for one parameter `γ`.
* `wholePlane_fixedStart_strictMono_of_oneStart`: the hypothesis `hfixsm` as typed in
  `Sec1.hasReferenceEnvironments_of_coupling_wholePlane_fixedStart`, from the one-start event for every `γ ∈ (0, 2)`
  and `hfix`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology HarmonicBalls LQGMetric MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.Sec1

/-- At a positive time, Lebesgue measure is absolutely continuous with respect to the planar heat kernel. -/
theorem volume_absolutelyContinuous_planarHeatSemigroup (x : ℂ) {s : ℝ≥0} (hs : s ≠ 0) :
    (volume : Measure ℂ) ≪ planarHeatSemigroup s x := by
  rw [planarHeatSemigroup_apply]
  have h := (gaussianReal_absolutelyContinuous' x.re hs).prod
    (gaussianReal_absolutelyContinuous' x.im hs)
  have hm := h.map Complex.measurableEquivRealProd.symm.measurable
  rw [← Measure.volume_eq_prod ℝ ℝ, Complex.volume_preserving_equiv_real_prod.symm.map_eq] at hm
  exact hm

/-- **From one start to almost every start.** If, from the start `x`, the path shifted by a positive time `s` lies
almost surely in a measurable event `S`, then for Lebesgue-almost every start `y` the path lies almost surely in `S`
(simple Markov property at time `s`; Lebesgue measure is absolutely continuous with respect to the law of `b_s`). -/
theorem ae_start_of_ae_shift_start (x : ℂ) {s : ℝ≥0} (hs : s ≠ 0) {S : Set (ContinuousPath ℂ)}
    (hS : MeasurableSet S) (h : ∀ᵐ b ∂(planarBrownianMotion x), ContinuousPath.shift s b ∈ S) :
    ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ b ∂(planarBrownianMotion y), b ∈ S := by
  have ha : ∀ᵐ b ∂(planarBrownianMotion x).map (ContinuousPath.shift s), b ∈ S :=
    (ae_map_iff (ContinuousPath.measurable_shift_fixed s).aemeasurable hS).2 h
  rw [planarBrownianMotion_eq_continuousProcess] at ha
  have hshift := congrArg (fun K => K x)
    (SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup s)
  rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed s) x] at hshift
  rw [hshift] at ha
  have h2 := ProbabilityTheory.Kernel.ae_ae_of_ae_comp ha
  filter_upwards [(volume_absolutelyContinuous_planarHeatSemigroup x hs).ae_le h2] with y hy
  rw [planarBrownianMotion_eq_continuousProcess]
  exact hy

/-- Two families of functions on `(0, ∞) × ℂ` that are almost surely continuous there and agree almost surely at each
point agree almost surely at every point. -/
theorem ae_forall_eq_of_continuousOn_of_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F G : Ω → ℝ → ℂ → ℝ}
    (hF : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => F ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hG : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => G ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (h : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, F ω r z = G ω r z) :
    ∀ᵐ ω ∂P, ∀ r, 0 < r → ∀ z, F ω r z = G ω r z := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (ℝ × ℂ)
  have hD : ∀ᵐ ω ∂P, ∀ p ∈ D ∩ (Ioi 0 ×ˢ univ), F ω p.1 p.2 = G ω p.1 p.2 :=
    (ae_ball_iff (hDc.mono inter_subset_left)).2 fun p hp => h p.1 hp.2.1 p.2
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := isOpen_Ioi.prod isOpen_univ
  filter_upwards [hF, hG, hD] with ω hFω hGω hDω r hr z
  have heq : EqOn (fun p : ℝ × ℂ => F ω p.1 p.2) (fun p => G ω p.1 p.2) (Ioi 0 ×ˢ univ) :=
    Set.EqOn.of_subset_closure (s := (Ioi 0 ×ˢ univ) ∩ D) (fun p hp => hDω p ⟨hp.2, hp.1⟩) hFω hGω
      inter_subset_left (hDd.open_subset_closure_inter hU)
  exact heq (show (r, z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) from ⟨hr, mem_univ z⟩)

/-- **Strict monotonicity of the limit clock from positive increments.** Let `A k` be continuous nondecreasing
functions on `[0, ∞)` vanishing at `0` and uniformly Cauchy on every `[0, N]`. If, for all rationals `0 < a < b`, the
lower limit of `ENNReal.ofReal (A k b - A k a)` is positive, then the limit `LatticeProb.limitAfterPositiveTimes A` is
strictly increasing. -/
theorem strictMono_limitAfterPositiveTimes_of_pos_increments {A : ℕ → ℝ≥0 → ℝ}
    (hc : ∀ k, Continuous (A k)) (h0 : ∀ k, A k 0 = 0) (hmono : ∀ k, Monotone (A k))
    (hU : ∀ N : ℕ, UniformCauchySeqOn A atTop (Icc 0 (N : ℝ≥0)))
    (hpos : ∀ a b : ℚ, 0 < a → a < b →
      0 < liminf (fun k => ENNReal.ofReal (A k (b : ℝ).toNNReal - A k (a : ℝ).toNNReal)) atTop) :
    StrictMono (LatticeProb.limitAfterPositiveTimes A) := by
  have hlim := MatedCRT.FirstPass.Derived.tendsto_limitAfterPositiveTimes_of_uniformCauchySeqOn hc h0 hU
  have hL : Monotone (LatticeProb.limitAfterPositiveTimes A) := fun s t hst =>
    le_of_tendsto_of_tendsto' (hlim s) (hlim t) fun k => hmono k hst
  have hlt : ∀ a b : ℚ, 0 < a → a < b →
      LatticeProb.limitAfterPositiveTimes A (a : ℝ).toNNReal <
        LatticeProb.limitAfterPositiveTimes A (b : ℝ).toNNReal := by
    intro a b ha hab
    have ht : Tendsto (fun k => ENNReal.ofReal (A k (b : ℝ).toNNReal - A k (a : ℝ).toNNReal)) atTop
        (𝓝 (ENNReal.ofReal (LatticeProb.limitAfterPositiveTimes A (b : ℝ).toNNReal -
          LatticeProb.limitAfterPositiveTimes A (a : ℝ).toNNReal))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((hlim _).sub (hlim _))
    have h := hpos a b ha hab
    rw [ht.liminf_eq] at h
    linarith [ENNReal.ofReal_pos.1 h]
  refine strictMono_of_monotone_of_rat hL fun q₁ q₂ hq => ?_
  obtain ⟨h12, hq₂⟩ := Real.toNNReal_lt_toNNReal_iff'.1 hq
  have h12' : q₁ < q₂ := by exact_mod_cast h12
  have hq₂' : (0 : ℚ) < q₂ := by exact_mod_cast hq₂
  set r : ℚ := (max q₁ 0 + q₂) / 2 with hr
  have hr0 : 0 < r := by
    rw [hr]
    linarith [le_max_right q₁ 0]
  have hr1 : q₁ ≤ r := by
    rw [hr]
    linarith [le_max_left q₁ 0]
  have hr2 : r < q₂ := by
    rw [hr]
    linarith [max_lt h12' hq₂']
  exact (hL (Real.toNNReal_mono (by exact_mod_cast hr1))).trans_lt (hlt r q₂ hr0 hr2)

/-- The increment of the approximating clock over `[a, b]`, `0 ≤ a ≤ b`, is the integral of its density over
`[a, b]`. -/
theorem lqgClockApprox_toNNReal_sub_eq_integral {γ ε : ℝ} {hε : ℝ → ℂ → ℝ} (hcont : Continuous (hε ε))
    (w : ContinuousPath ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    lqgClockApprox γ hε ε w b.toNNReal - lqgClockApprox γ hε ε w a.toNNReal =
      ∫ v in a..b, ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (w v.toNNReal)) := by
  have hd : Continuous fun v : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (w v.toNNReal)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (hcont.comp (w.continuous.comp continuous_real_toNNReal))))
  unfold lqgClockApprox
  rw [Real.coe_toNNReal _ (ha.trans hab), Real.coe_toNNReal _ ha]
  exact intervalIntegral.integral_interval_sub_left (hd.intervalIntegrable _ _) (hd.intervalIntegrable _ _)

/-- **Strict monotonicity of the fixed-start clock from the one-start event.** Let `Y'` be a normalized whole-plane
Gaussian free field with a version `c'` of its circle averages that is continuous on `(0, ∞) × ℂ` and jointly
measurable. Suppose that the one-start event holds for the parameter `γ` for every whole-plane GFF of
`LatticeProb.Gauss` (almost surely in the field, for all rationals `0 < a < b`, from the origin, almost surely the
increment of the dyadic clocks over `[a, b]` has positive lower limit; Berestycki 2015), and that the dyadic clocks of
`c' ∘ Y'` are uniformly Cauchy on compact time intervals from Lebesgue-almost every fixed start, almost surely for the
joint law. Then from Lebesgue-almost every fixed start, almost surely for the joint law, their limit clock is strictly
increasing. -/
theorem ae_strictMono_wholePlane_fixedStart_of_oneStart {γ : ℝ}
    (hone : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
      {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
      ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
        0 < liminf (fun k => ENNReal.ofReal (∫ v in (a : ℝ)..(b : ℝ),
          HarmonicBalls.dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (HarmonicBalls.dyadicScale k)
              (w v.toNNReal)))) atTop)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ}
    (hY : IsNormalizedWPGFF Y' P')
    (hver : ∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmeas : Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2))
    (hfix : ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      UniformCauchySeqOn
        (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
        atTop (Icc 0 T)) :
    ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
      StrictMono (LatticeProb.limitAfterPositiveTimes
        fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t) := by
  have hc : ∀ x k, Continuous (c' x (HarmonicBalls.dyadicScale k)) := fun x k =>
    (hcont x).comp_continuous (continuous_const.prodMk continuous_id)
      fun z => ⟨HarmonicBalls.dyadicScale_pos k, mem_univ z⟩
  have hm : ∀ k, Measurable fun q : Ω' × ℂ =>
      c' (Y' q.1) (HarmonicBalls.dyadicScale k) q.2 := fun k =>
    hmeas.comp (((measurable_const : Measurable fun _ : Ω' × ℂ =>
      (⟨HarmonicBalls.dyadicScale k, HarmonicBalls.dyadicScale_pos k⟩ : Ioi (0 : ℝ))).prodMk
        measurable_snd).prodMk (hY.1.measurable.comp measurable_fst))
  have hA : ∀ k (t : ℝ≥0), Measurable fun p : Ω' × ContinuousPath ℂ =>
      lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t := fun k t =>
    (MatedCRT.LQGClockApproxMeasurable.measurable_lqgClockApprox_field_path_time_of_scale
      (c := fun ω => c' (Y' ω)) γ (hm k)).comp
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  obtain ⟨hC, hcirc, hG, -, hcircEq, -⟩ := MatedCRT.exists_normalizedGFF_coordinates hY
  have hid : ∀ᵐ ω ∂P', ∀ r, 0 < r → ∀ z, hcirc ω r z = c' (Y' ω) r z :=
    ae_forall_eq_of_continuousOn_of_ae_eq (G := fun ω => c' (Y' ω)) hG.ae_continuousOn_circle
      (Eventually.of_forall fun ω => hcont (Y' ω)) fun r hr z => by
        filter_upwards [hcircEq r hr z, hver r hr z] with ω h1 h2
        exact h1.trans h2.symm
  have h0 : ∀ᵐ ω ∂P', ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
      0 < liminf (fun k => ENNReal.ofReal
        (lqgClockApprox γ (c' (Y' ω)) (HarmonicBalls.dyadicScale k) w (b : ℝ).toNNReal -
          lqgClockApprox γ (c' (Y' ω)) (HarmonicBalls.dyadicScale k) w (a : ℝ).toNNReal)) atTop := by
    filter_upwards [hone hG, hid] with ω hω hidω a b ha hab
    have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha.le
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
    have hfun : ∀ k, LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (HarmonicBalls.dyadicScale k) =
        c' (Y' ω) (HarmonicBalls.dyadicScale k) := fun k => funext fun z => by
      simp only [LatticeProb.Gauss.fieldCircleAverage, zero_mul, sub_zero]
      exact hidω _ (HarmonicBalls.dyadicScale_pos k) z
    filter_upwards [hω a b ha hab] with w hw
    refine hw.trans_eq (congrArg (fun f : ℕ → ℝ≥0∞ => liminf f atTop) (funext fun k => ?_))
    rw [hfun k, lqgClockApprox_toNNReal_sub_eq_integral (hc _ k) w ha' hab']
  have hall : ∀ᵐ ω ∂P', ∀ x : ℂ, ∀ᵐ w ∂(planarBrownianMotion x), ∀ a b : ℚ, 0 < a → a < b →
      0 < liminf (fun k => ENNReal.ofReal
        (lqgClockApprox γ (c' (Y' ω)) (HarmonicBalls.dyadicScale k) w (b : ℝ).toNNReal -
          lqgClockApprox γ (c' (Y' ω)) (HarmonicBalls.dyadicScale k) w (a : ℝ).toNNReal)) atTop := by
    filter_upwards [h0] with ω hω x
    refine ae_all_iff.2 fun a => ae_all_iff.2 fun b => ?_
    by_cases hab : 0 < a ∧ a < b
    swap
    · exact Eventually.of_forall fun w h1 h2 => absurd ⟨h1, h2⟩ hab
    obtain ⟨ha, hab⟩ := hab
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
    have ha0 : (a : ℝ).toNNReal ≠ 0 := (Real.toNNReal_pos.2 ha').ne'
    have hd : ∀ k (w : ContinuousPath ℂ),
        lqgClockApprox γ (c' (Y' ω)) (HarmonicBalls.dyadicScale k) w (b : ℝ).toNNReal -
          lqgClockApprox γ (c' (Y' ω)) (HarmonicBalls.dyadicScale k) w (a : ℝ).toNNReal =
        lqgClockApprox γ (c' (Y' ω)) (HarmonicBalls.dyadicScale k)
          (ContinuousPath.shift (a : ℝ).toNNReal w) ((b : ℝ).toNNReal - (a : ℝ).toNNReal) := by
      intro k w
      have hle : (a : ℝ).toNNReal ≤ (b : ℝ).toNNReal := Real.toNNReal_mono hab'
      conv_lhs => rw [show (b : ℝ).toNNReal = (a : ℝ).toNNReal + ((b : ℝ).toNNReal - (a : ℝ).toNNReal) from
        (add_tsub_cancel_of_le hle).symm]
      rw [MatedCRT.FirstPass.Derived.lqgClockApprox_add_eq_add_shift (hc _ k) w]
      ring
    have hE : MeasurableSet {w' : ContinuousPath ℂ | 0 < liminf (fun k => ENNReal.ofReal
        (lqgClockApprox γ (c' (Y' ω)) (HarmonicBalls.dyadicScale k) w'
          ((b : ℝ).toNNReal - (a : ℝ).toNNReal))) atTop} := by
      refine measurableSet_lt measurable_const (Measurable.liminf fun k => ?_)
      exact ((hA k _).comp ((measurable_const : Measurable fun _ : ContinuousPath ℂ => ω).prodMk
        measurable_id)).ennreal_ofReal
    have hsh0 : ∀ᵐ w ∂(planarBrownianMotion 0), ContinuousPath.shift (a : ℝ).toNNReal w ∈
        {w' : ContinuousPath ℂ | 0 < liminf (fun k => ENNReal.ofReal
          (lqgClockApprox γ (c' (Y' ω)) (HarmonicBalls.dyadicScale k) w'
            ((b : ℝ).toNNReal - (a : ℝ).toNNReal))) atTop} := by
      filter_upwards [hω a b ha hab] with w hw
      simpa only [hd] using hw
    filter_upwards [MatedCRT.FirstPass.Derived.ae_planarBrownianMotion_shift_of_ae_start x ha0 hE
      (ae_start_of_ae_shift_start 0 ha0 hE hsh0)] with w hw _ _
    simpa only [hd] using hw
  have hS : MeasurableSet {p : Ω' × ContinuousPath ℂ | ∀ a b : ℚ, 0 < a → a < b →
      0 < liminf (fun k => ENNReal.ofReal
        (lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 (b : ℝ).toNNReal -
          lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 (a : ℝ).toNNReal)) atTop} := by
    refine measurableSet_setOfPred.2 ?_
    refine Measurable.forall fun a => Measurable.forall fun b => Measurable.imp measurable_const
      (Measurable.imp measurable_const ?_)
    exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const
      (Measurable.liminf fun k => ((hA k _).sub (hA k _)).ennreal_ofReal))
  have hjoint : ∀ y : ℂ, ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)), ∀ a b : ℚ, 0 < a → a < b →
      0 < liminf (fun k => ENNReal.ofReal
        (lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 (b : ℝ).toNNReal -
          lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 (a : ℝ).toNNReal)) atTop :=
    fun y => (Measure.ae_prod_iff_ae_ae hS).2 (hall.mono fun ω hω => hω y)
  filter_upwards [ae_all_iff.2 fun N : ℕ => hfix N] with y hy
  filter_upwards [ae_all_iff.2 hy, hjoint y] with p hU hp
  exact strictMono_limitAfterPositiveTimes_of_pos_increments
    (fun k => MatedCRT.LQGClockApproxMeasurable.continuous_lqgClockApprox_field c' γ _ (Y' p.1) (hc _ k) p.2)
    (fun k => by simp [lqgClockApprox])
    (fun k => MatedCRT.FirstPass.Derived.LQGLimitClockShift.monotone_lqgClockApprox
      (HarmonicBalls.dyadicScale_pos k).le (hc _ k) p.2)
    hU hp

/-- **The strict-monotonicity binder of the whole-plane reference environments from the one-start event.** The
hypothesis `hfixsm` of `hasReferenceEnvironments_of_coupling_wholePlane_fixedStart` follows from its hypothesis
`hfix` and the one-start event for every `γ ∈ (0, 2)`: for every whole-plane GFF of `LatticeProb.Gauss`, almost surely
in the field, for all rationals `0 < a < b`, from the origin, almost surely the increment of the dyadic clocks over
`[a, b]` has positive lower limit (Berestycki 2015). -/
theorem wholePlane_fixedStart_strictMono_of_oneStart
    (hone : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
        {hcirc : Ω → ℝ → ℂ → ℝ}, LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
          0 < liminf (fun k => ENNReal.ofReal (∫ v in (a : ℝ)..(b : ℝ),
            HarmonicBalls.dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (HarmonicBalls.dyadicScale k)
                (w v.toNNReal)))) atTop)
    (hfix : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ T : ℝ≥0, ∀ᵐ y ∂(volume : Measure ℂ),
          ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
            UniformCauchySeqOn
              (fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t)
              atTop (Icc 0 T)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
        {Y' : Ω' → DistC} {c' : DistC → ℝ → ℂ → ℝ},
        IsNormalizedWPGFF Y' P' →
        (∀ r, 0 < r → ∀ z, ∀ᵐ ω' ∂P', c' (Y' ω') r z = LQGMetric.circleAvg (Y' ω') r z) →
        (∀ x, ContinuousOn (fun p : ℝ × ℂ => c' x p.1 p.2) (Ioi 0 ×ˢ univ)) →
        Measurable (fun q : (Ioi (0 : ℝ) × ℂ) × DistC => c' q.2 q.1.1 q.1.2) →
        ∀ᵐ y ∂(volume : Measure ℂ), ∀ᵐ p ∂(P'.prod (planarBrownianMotion y)),
          StrictMono (LatticeProb.limitAfterPositiveTimes
            fun k t => lqgClockApprox γ (c' (Y' p.1)) (HarmonicBalls.dyadicScale k) p.2 t) :=
  fun γ hγ0 hγ2 {_} _ {_} _ {_} {_} hY hver hcont hmeas =>
    ae_strictMono_wholePlane_fixedStart_of_oneStart (hone γ hγ0 hγ2) hY hver hcont hmeas
      (hfix γ hγ0 hγ2 hY hver hcont hmeas)

end MatedCRT.Sec1
