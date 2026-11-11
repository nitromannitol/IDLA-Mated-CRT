import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.JointBallVersion
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.FixedTimeReduction

/-!
# Lemma 3.4: a jointly measurable version of the truncated LBM occupations

For a valid environment, a starting point `y`, a ball `B = ball z r` and an environment-measurable family of
continuous functions `f ω`, the truncated path integrals `∫_{(0, min T τ]} f ω (X_t) dt` of the rescaled LBM path
`X = rescaledLBMPath (S.clock ω) S.m₀ b` (with exit time `τ` from `B`) agree, for almost every environment and almost
every Brownian path, with a jointly measurable function of `(ω, b)`.

The jointly measurable version integrates over `t` the product of the exit indicator (computed from the rational
inverse `ratClockInv` of the jointly measurable clock limit, `exists_joint_clock_limit`, and the Brownian exit time,
`ContinuousPath.measurable_exitTime`) and the jointly measurable version `F` of `f` on the ball
(`exists_joint_version_ball`), evaluated at the time-changed Brownian path.
-/

open Classical

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- **Jointly measurable version of the truncated LBM occupations.** For every real `T` there is a measurable
`Ĥ : Ω × ContinuousPath ℂ → ℝ` that equals the truncated path integral almost surely. -/
theorem exists_truncated_joint {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) {z y : ℂ} {r : ℝ} (hr : 0 < r)
    (f : Ω → ℂ → ℝ) (hfm : ∀ x : ℂ, Measurable[S.envSigma] fun ω => f ω x)
    (hfc : ∀ ω, ContinuousOn (f ω) (ball z r)) (T : ℝ) :
    ∃ Ĥ : Ω × ContinuousPath ℂ → ℝ, Measurable Ĥ ∧
      ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
        Ĥ (ω, b) = ∫ t in Ioc (0 : ℝ) (min T (pathExitTime (ball z r)
          (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
          f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal) ∧
        AEStronglyMeasurable (fun t : ℝ => f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal))
          (volume.restrict (Ioc (0 : ℝ) (min T (pathExitTime (ball z r)
            (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal))) := by
  obtain ⟨φ, L, -, hLm, hLid⟩ := exists_joint_clock_limit S hS y
  obtain ⟨F, hFm, hFid⟩ := exists_joint_version_ball hS hr f hfm hfc
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ≥0, c = S.m₀.toNNReal := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hc_def]
    exact Real.toNNReal_pos.2 (hS.m₀_pos hγ hγ2)
  -- measurability of the building blocks
  have hτc : Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ => c * q.2.toNNReal :=
    (continuous_const.mul continuous_id).measurable.comp (measurable_real_toNNReal.comp measurable_snd)
  have hpair : Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ => (q.1, c * q.2.toNNReal) :=
    measurable_fst.prodMk hτc
  have hΦ : Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ => ratClockInv (L q.1) (c * q.2.toNNReal) :=
    Measurable.comp (g := fun x : (Ω × ContinuousPath ℂ) × ℝ≥0 => ratClockInv (L x.1) x.2)
      (f := fun q : (Ω × ContinuousPath ℂ) × ℝ => (q.1, c * q.2.toNNReal))
      (measurable_ratClockInv hLm) hpair
  have hΦn : Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ => (ratClockInv (L q.1) (c * q.2.toNNReal)).toNNReal :=
    hΦ.ennreal_toNNReal
  have hXv : Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ =>
      q.1.2 (ratClockInv (L q.1) (c * q.2.toNNReal)).toNNReal :=
    measurable_path_eval_pair.comp ((measurable_snd.comp measurable_fst).prodMk hΦn)
  have hτ : Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ =>
      pathExitTime (ball z r) (q.1.2 : ℝ≥0 → ℂ) :=
    (ContinuousPath.measurable_exitTime (ball z r) Metric.isOpen_ball).comp
      (measurable_snd.comp measurable_fst)
  have hτn : Measurable fun q : (Ω × ContinuousPath ℂ) × ℝ =>
      (((pathExitTime (ball z r) (q.1.2 : ℝ≥0 → ℂ)).toNNReal : ℝ≥0) : ℝ≥0∞) :=
    hτ.ennreal_toNNReal.coe_nnreal_ennreal
  -- the exit indicator of the truncation
  let Ind : (Ω × ContinuousPath ℂ) × ℝ → ℝ := fun q =>
    if 0 < q.2 ∧ q.2 ≤ T ∧ pathExitTime (ball z r) (q.1.2 : ℝ≥0 → ℂ) ≠ ⊤ ∧
        ratClockInv (L q.1) (c * q.2.toNNReal) ≤
          (((pathExitTime (ball z r) (q.1.2 : ℝ≥0 → ℂ)).toNNReal : ℝ≥0) : ℝ≥0∞)
    then 1 else 0
  have hInd : Measurable Ind := by
    refine Measurable.ite ?_ measurable_const measurable_const
    have hA : MeasurableSet {q : (Ω × ContinuousPath ℂ) × ℝ | 0 < q.2} :=
      measurableSet_lt measurable_const measurable_snd
    have hB : MeasurableSet {q : (Ω × ContinuousPath ℂ) × ℝ | q.2 ≤ T} :=
      measurableSet_le measurable_snd measurable_const
    have hC : MeasurableSet {q : (Ω × ContinuousPath ℂ) × ℝ |
        pathExitTime (ball z r) (q.1.2 : ℝ≥0 → ℂ) ≠ ⊤} :=
      (measurableSet_singleton ⊤).compl.preimage hτ
    have hD : MeasurableSet {q : (Ω × ContinuousPath ℂ) × ℝ |
        ratClockInv (L q.1) (c * q.2.toNNReal) ≤
          (((pathExitTime (ball z r) (q.1.2 : ℝ≥0 → ℂ)).toNNReal : ℝ≥0) : ℝ≥0∞)} :=
      measurableSet_le hΦ hτn
    exact hA.inter (hB.inter (hC.inter hD))
  -- the joint integrand
  let g : (Ω × ContinuousPath ℂ) × ℝ → ℝ := fun q => Ind q * F (q.1.1, q.1.2 (ratClockInv (L q.1)
    (c * q.2.toNNReal)).toNNReal)
  have hg : Measurable g := hInd.mul (hFm.comp ((measurable_fst.comp measurable_fst).prodMk hXv))
  refine ⟨fun p => ∫ t, g (p, t), (hg.stronglyMeasurable.integral_prod_right).measurable, ?_⟩
  filter_upwards [hFid, hLid, hS.isLQGClock] with ω hωF hωL hωQ
  filter_upwards [hωL, (hωQ y).2] with b hbL hbT
  have hCc : Continuous (S.clock ω b) := hbT.continuous
  have hC0 : S.clock ω b 0 = 0 := hbT.map_zero
  have hCmono : StrictMono (S.clock ω b) := hbT.strictMono
  have hCunb : ∀ M : ℝ, ∃ s : ℝ≥0, M < S.clock ω b s := fun M =>
    (hbT.tendsto_atTop.eventually_gt_atTop M).exists
  -- the rational inverse is the clock inverse
  have hR : ∀ s : ℝ≥0, ratClockInv (L (ω, b)) (c * s) =
      ((clockInverse (S.clock ω b) (c * s) : ℝ≥0) : ℝ≥0∞) := fun s =>
    ratClockInv_eq_clockInverse hCc hCunb hbL (c * s)
  have hX : ∀ t : ℝ, b (ratClockInv (L (ω, b)) (c * t.toNNReal)).toNNReal =
      rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal := by
    intro t
    rw [hR, ENNReal.toNNReal_coe, hc_def]
    rfl
  have hτfun : (fun s : ℝ≥0 => b (clockInverse (S.clock ω b) (c * s))) =
      rescaledLBMPath (S.clock ω) S.m₀ b := by
    rw [hc_def]
    rfl
  have hcond : ∀ t : ℝ, (ratClockInv (L (ω, b)) (c * t.toNNReal) ≤
      (((pathExitTime (ball z r) (b : ℝ≥0 → ℂ)).toNNReal : ℝ≥0) : ℝ≥0∞)) ↔
      (clockInverse (S.clock ω b) (c * t.toNNReal) ≤ (pathExitTime (ball z r) (b : ℝ≥0 → ℂ)).toNNReal) := by
    intro t
    rw [hR, ENNReal.coe_le_coe]
  -- the exit indicator is the truncation indicator
  have hIndQ : ∀ t : ℝ, Ind ((ω, b), t) = 1 ↔
      (0 < t ∧ t ≤ T ∧ pathExitTime (ball z r) (b : ℝ≥0 → ℂ) ≠ ⊤ ∧
        ratClockInv (L (ω, b)) (c * t.toNNReal) ≤
          (((pathExitTime (ball z r) (b : ℝ≥0 → ℂ)).toNNReal : ℝ≥0) : ℝ≥0∞)) := by
    intro t
    simp only [Ind]
    split_ifs with h
    · exact iff_of_true rfl h
    · exact iff_of_false (by norm_num) (fun hq => h hq)
  have hIndT : ∀ t : ℝ, Ind ((ω, b), t) = 1 ↔
      (0 < t ∧ t ≤ T ∧ t ≤ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal) := by
    intro t
    by_cases ht : 0 < t
    · have hle := le_toReal_exitTime_comp (B := ball z r) (C := S.clock ω b) Metric.isOpen_ball b hCc hCmono hC0
        hCunb hc
        (t := t.toNNReal) (Real.toNNReal_pos.2 ht)
      rw [Real.coe_toNNReal _ ht.le, hτfun] at hle
      rw [hIndQ t]
      constructor
      · rintro ⟨-, h1, h2, h3⟩
        exact ⟨ht, h1, hle.2 ⟨h2, (hcond t).1 h3⟩⟩
      · rintro ⟨-, h1, h2⟩
        obtain ⟨h3, h4⟩ := hle.1 h2
        exact ⟨ht, h1, h3, (hcond t).2 h4⟩
    · constructor
      · intro h
        exact absurd ((hIndQ t).1 h).1 ht
      · rintro ⟨h0, -, -⟩
        exact absurd h0 ht
  have hIndVal : ∀ q : (Ω × ContinuousPath ℂ) × ℝ, Ind q = 0 ∨ Ind q = 1 := by
    intro q
    simp only [Ind]
    split_ifs <;> simp
  -- the joint integrand agrees with the truncated integrand off the exit point
  have hpt : ∀ t : ℝ, t ≠ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal →
      g ((ω, b), t) = (Ioc (0 : ℝ) (min T (pathExitTime (ball z r)
          (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal)).indicator
        (fun t : ℝ => f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) t := by
    intro t htne
    by_cases hmem : t ∈ Ioc (0 : ℝ) (min T (pathExitTime (ball z r)
        (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal)
    · obtain ⟨ht0, htm⟩ := hmem
      have htT : t ≤ T := le_trans htm (min_le_left _ _)
      have htτ : t ≤ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal :=
        le_trans htm (min_le_right _ _)
      have htlt : t < (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal :=
        lt_of_le_of_ne htτ htne
      have hI : Ind ((ω, b), t) = 1 := (hIndT t).2 ⟨ht0, htT, htτ⟩
      have hball : rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal ∈ ball z r :=
        path_mem_ball_of_lt_truncation (T := t + 1) ht0 (lt_min (lt_add_one t) htlt)
      simp only [g]
      rw [hI, one_mul, hX t, hωF _ hball, Set.indicator_of_mem (Set.mem_Ioc.2 ⟨ht0, htm⟩)]
    · have hI : Ind ((ω, b), t) = 0 := by
        rcases hIndVal ((ω, b), t) with h | h
        · exact h
        · exact absurd ((hIndT t).1 h) (fun h' => hmem ⟨h'.1, le_min h'.2.1 h'.2.2⟩)
      simp only [g]
      rw [hI, zero_mul, Set.indicator_of_notMem hmem]
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (pathExitTime (ball z r)
      (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal := by
    filter_upwards [(Set.countable_singleton _).ae_notMem (volume : Measure ℝ)] with t ht
    exact fun h => ht (Set.mem_singleton_iff.2 h)
  -- the integrals agree since the single exit point is a null set
  have hint : ∫ t, g ((ω, b), t) = ∫ t in Ioc (0 : ℝ) (min T (pathExitTime (ball z r)
      (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
        f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal) := by
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [hae] with t ht
    exact hpt t ht
  have hmeas : AEStronglyMeasurable (fun t : ℝ => f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal))
      (volume.restrict (Ioc (0 : ℝ) (min T (pathExitTime (ball z r)
        (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal))) := by
    have hgt : Measurable fun t : ℝ => g ((ω, b), t) :=
      hg.comp (measurable_const.prodMk measurable_id)
    refine hgt.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioc] with t ht hmt
    exact (hpt t ht).trans (Set.indicator_of_mem hmt _)
  exact ⟨hint, hmeas⟩

end MatedCRT
