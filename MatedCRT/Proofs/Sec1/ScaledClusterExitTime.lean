import MatedCRT.Proofs.Sec1.HarmonicBallScaling
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Main

/-!
# eq:btb-converge-to-inf: `b T^b → ∞` in probability (line 3330)

`scaledClusterExitTimeStep_of_steps` proves `ScaledClusterExitTimeStep` along the printed argument, "`T^b =d T`
(Lemma 2.6) and `T > 0` a.s.", from
* Lemma 2.5 (`ConeScaleInvarianceUpToFixedTimeStmt`): the joint law of the circle average process and the family
  process stopped at the exit of `B_{1/2}` is invariant under the rescaling, with the uniqueness of the rescaled
  stopped family;
* `ConeFamilyAEMeasurableStep` (Theorem 2.3): these family processes are random variables;
* `ConeHarmonicBallStrictGrowthStep` (Theorem 2.3): `cl Λ_s ⊆ Λ_t` for `s < t`, which gives `Λ_s → {0}` as `s → 0`
  (`exists_pos_subset_ball`), hence `T > 0`.

The event `{b T^b ≤ t}` is not measurable as stated (the family is a random variable only through its family
process). It is contained, a.s., in the event `{F^b ∈ E_{t/b}}` of the stopped rescaled family process `F^b`, where
`E_x` says that for no rational `q > x` the set `F(q, ·)` contains `0` and only points of norm `< ρ/4` of a fixed
countable dense set `D` (`mem_E_of_scaledExitTime_le`). By Lemma 2.5, `P[F^b ∈ E_x] = P[F ∈ E_x]` for the unscaled
family process `F`, and `P[F ∈ E_x] → P[F ∈ E_0] = 0` as `x → 0`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace Sec1

variable {μ : Measure ℂ} {Λ : ℝ → Set ℂ}

/-! ## Deterministic facts about the families of Theorem 2.3 -/

/-- **Small harmonic balls are small**: with strict growth, `Λ_s ⊆ B_r` for some `s > 0` (the sets
`cl Λ_s \ B_r`, `s ∈ (0, 1)`, are compact, decreasing, with empty intersection since `⋂ Λ_t = {0}`). -/
theorem exists_pos_subset_ball (hΛ : SatisfiesHarmonicBallConditions μ Λ 0) (hstr : IsStrictlyGrowingOn Λ 1)
    {r : ℝ} (hr : 0 < r) : ∃ s, 0 < s ∧ Λ s ⊆ ball 0 r := by
  by_contra hcon
  have hne : Nonempty (Ioo (0 : ℝ) 1) := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  let K : Ioo (0 : ℝ) 1 → Set ℂ := fun s => closure (Λ s) \ ball 0 r
  have hdir : Directed (fun x1 x2 => x1 ⊇ x2) K := by
    intro s1 s2
    have hm : (0 : ℝ) < min (s1 : ℝ) s2 := lt_min s1.2.1 s2.2.1
    refine ⟨⟨min (s1 : ℝ) s2, hm, lt_of_le_of_lt (min_le_left _ _) s1.2.2⟩, ?_, ?_⟩
    · exact sdiff_subset_sdiff_left (closure_mono (hΛ.monotoneOn hm s1.2.1 (min_le_left _ _)))
    · exact sdiff_subset_sdiff_left (closure_mono (hΛ.monotoneOn hm s2.2.1 (min_le_right _ _)))
  have hKne : ∀ s, (K s).Nonempty := by
    intro s
    have h1 : ¬ Λ s ⊆ ball 0 r := fun h => hcon ⟨s, s.2.1, h⟩
    rw [not_subset] at h1
    obtain ⟨x, hx, hxb⟩ := h1
    exact ⟨x, subset_closure hx, hxb⟩
  have hKc : ∀ s, IsCompact (K s) := fun s => ((hΛ.isBounded s s.2.1).isCompact_closure).diff isOpen_ball
  have hKcl : ∀ s, IsClosed (K s) := fun s => isClosed_closure.sdiff isOpen_ball
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K hdir hKne hKc hKcl
  rw [mem_iInter] at hx
  have hx0 : x ∈ ⋂ t ∈ Ioi (0 : ℝ), Λ t := by
    rw [mem_iInter₂]
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rcases lt_or_ge t 1 with ht1 | ht1
    · exact hstr (t / 2) t (half_pos ht') (half_lt_self ht') ht1 (hx ⟨t / 2, half_pos ht', by linarith⟩).1
    · have h12 : x ∈ Λ (1 / 2) :=
        hstr (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (hx ⟨1 / 4, by norm_num, by norm_num⟩).1
      exact hΛ.monotoneOn (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num) ht (by linarith) h12
  rw [hΛ.iInter_eq, mem_singleton_iff] at hx0
  apply (hx ⟨1 / 2, by norm_num, by norm_num⟩).2
  rw [hx0]
  exact mem_ball_self hr

/-- **The exit time of `B_{ρ/3}`** (`clusterExitTime Λ ρ`): if `μ(B_{ρ/3}) < ∞` and `Λ_s ⊆ B_{ρ/3}` for some `s > 0`,
then the set of times `t` with `Λ_t ⊆ B_{ρ/3}` is bounded, its supremum `τ` is positive, `Λ_t ⊆ B_{ρ/3}` for
`t < τ`, and `Λ_t ⊄ B_r` for some `t < τ`, for each `r < ρ/3` (Hausdorff continuity at `τ`). -/
theorem clusterExitTime_spec (hΛ : SatisfiesHarmonicBallConditions μ Λ 0) {ρ : ℝ}
    (hfin : μ (ball 0 (ρ / 3)) ≠ ⊤) (hsmall : ∃ s, 0 < s ∧ Λ s ⊆ ball 0 (ρ / 3)) :
    BddAbove {t | 0 < t ∧ Λ t ⊆ ball 0 (ρ / 3)} ∧ 0 < clusterExitTime Λ ρ ∧
      (∀ t ∈ Ioo 0 (clusterExitTime Λ ρ), Λ t ⊆ ball 0 (ρ / 3)) ∧
      ∀ r < ρ / 3, ∃ t ∈ Ioo 0 (clusterExitTime Λ ρ), ¬ Λ t ⊆ ball 0 r := by
  set S := {t | 0 < t ∧ Λ t ⊆ ball 0 (ρ / 3)} with hS
  have hbdd : BddAbove S := by
    refine ⟨(μ (ball 0 (ρ / 3))).toReal, fun t ht => ?_⟩
    have h1 : μ (Λ t) ≤ μ (ball 0 (ρ / 3)) := measure_mono ht.2
    rw [hΛ.measure_eq t ht.1] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
  have hT : clusterExitTime Λ ρ = sSup S := rfl
  obtain ⟨s, hs, hsub⟩ := hsmall
  have hpos : 0 < sSup S := lt_of_lt_of_le hs (le_csSup hbdd ⟨hs, hsub⟩)
  rw [hT]
  refine ⟨hbdd, hpos, fun t ht => ?_, fun r hr => ?_⟩
  · obtain ⟨t', ht', htt'⟩ := exists_lt_of_lt_csSup (s := S) ⟨s, hs, hsub⟩ ht.2
    exact (hΛ.monotoneOn ht.1 ht'.1 htt'.le).trans ht'.2
  · by_contra hcon
    have hall : ∀ t ∈ Ioo 0 (sSup S), Λ t ⊆ ball 0 r := fun t ht => by
      by_contra h
      exact hcon ⟨t, ht, h⟩
    set τ := sSup S with hτ_def
    have hε : (0 : ℝ≥0∞) < ENNReal.ofReal ((ρ / 3 - r) / 2) := ENNReal.ofReal_pos.2 (by linarith)
    have hev := hΛ.hausdorffContinuousOn τ hpos _ hε
    rw [nhdsWithin_eq_nhds.2 (Ioi_mem_nhds hpos), Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hδΛ⟩ := hev
    have hs1 : max (τ / 2) (τ - δ / 2) ∈ Ioo 0 τ :=
      ⟨lt_max_of_lt_left (half_pos hpos), max_lt (half_lt_self hpos) (by linarith)⟩
    have hd1 : dist (max (τ / 2) (τ - δ / 2)) τ < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor
      · linarith [hs1.2]
      · linarith [le_max_right (τ / 2) (τ - δ / 2)]
    have hd2 : dist (τ + δ / 2) τ < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith
    have h1 := hδΛ hd1
    have h2 := hδΛ hd2
    have hsub2 : Λ (τ + δ / 2) ⊆ ball 0 (ρ / 3) := by
      intro y hy
      have h3 : infEDist y (Λ (max (τ / 2) (τ - δ / 2))) < ENNReal.ofReal (ρ / 3 - r) := by
        calc infEDist y (Λ (max (τ / 2) (τ - δ / 2)))
            ≤ hausdorffEDist (Λ (τ + δ / 2)) (Λ (max (τ / 2) (τ - δ / 2))) :=
              infEDist_le_hausdorffEDist_of_mem hy
          _ ≤ hausdorffEDist (Λ (τ + δ / 2)) (Λ τ) + hausdorffEDist (Λ τ) (Λ (max (τ / 2) (τ - δ / 2))) :=
              hausdorffEDist_triangle
          _ < ENNReal.ofReal ((ρ / 3 - r) / 2) + ENNReal.ofReal ((ρ / 3 - r) / 2) :=
              ENNReal.add_lt_add h2 (by rw [hausdorffEDist_comm]; exact h1)
          _ = ENNReal.ofReal (ρ / 3 - r) := by
              rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
              congr 1
              ring
      obtain ⟨z, hz, hyz⟩ := infEDist_lt_iff.1 h3
      have hz' := hall _ hs1 hz
      rw [edist_lt_ofReal, dist_eq_norm] at hyz
      rw [mem_ball, dist_zero_right] at hz' ⊢
      linarith [norm_sub_norm_le y z]
    have := le_csSup hbdd ⟨by linarith, hsub2⟩
    linarith

/-- An open set whose points in a dense set `D` have norm `< c` lies in `cl B_c`. -/
theorem subset_closedBall_of_dense {D U : Set ℂ} (hD : Dense D) (hU : IsOpen U) {c : ℝ}
    (h : ∀ d ∈ D, d ∈ U → ‖d‖ < c) : U ⊆ closedBall 0 c := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  by_contra hxc
  rw [not_le] at hxc
  obtain ⟨d, hdD, hdU, hdc⟩ :=
    hD.exists_mem_open (hU.inter (isOpen_lt continuous_const continuous_norm)) ⟨x, hx, hxc⟩
  exact lt_asymm (h d hdD hdU) hdc

/-- With `R = 0` the rescaled family is everything, so a stopped rescaled family has `R > 0`. -/
theorem pos_of_isStoppedAtHalfBall_rescaledFamily {Λb : ℝ → Set ℂ} {R b Tb : ℝ} (hb : 0 < b) (hR : 0 ≤ R)
    (hTb : 0 < Tb) (hfam : IsConeHarmonicBallFamilyOn μ Λb (b * Tb))
    (hstop : IsStoppedAtHalfBall (rescaledFamily Λb R b) Tb) : 0 < R := by
  rcases hR.lt_or_eq with h | h
  · exact h
  · exfalso
    subst h
    have hmem : (0 : ℂ) ∈ Λb (b * (Tb / 2)) :=
      hfam.2.1.mem _ ⟨mul_pos hb (half_pos hTb), mul_lt_mul_of_pos_left (half_lt_self hTb) hb⟩
    have h1 : (1 : ℂ) ∈ rescaledFamily Λb 0 b (Tb / 2) := by
      show ((0 : ℝ) : ℂ) * 1 ∈ Λb (b * (Tb / 2))
      simpa using hmem
    have h2 := hstop.1 (Tb / 2) ⟨half_pos hTb, half_lt_self hTb⟩ h1
    rw [mem_ball, dist_zero_right, norm_one] at h2
    norm_num at h2

/-- Rescaled families which agree on `(0, bT)` have the same family process on `(0, T)`. -/
theorem familyProcess_rescaledFamily_congr {Λ' Λb : ℝ → Set ℂ} {R b T : ℝ} (hb : 0 < b)
    (hEq : EqOn Λ' Λb (Ioo 0 (b * T))) :
    familyProcess (rescaledFamily Λb R b) T = familyProcess (rescaledFamily Λ' R b) T := by
  funext p
  have key : p.1 ∈ Ioo 0 T → Λ' (b * p.1) = Λb (b * p.1) := fun hp =>
    hEq ⟨mul_pos hb hp.1, mul_lt_mul_of_pos_left hp.2 hb⟩
  apply propext
  constructor
  · rintro ⟨hp, hx⟩
    refine ⟨hp, ?_⟩
    show (R : ℂ) * p.2 ∈ Λ' (b * p.1)
    rw [key hp]
    exact hx
  · rintro ⟨hp, hx⟩
    refine ⟨hp, ?_⟩
    show (R : ℂ) * p.2 ∈ Λb (b * p.1)
    rw [← key hp]
    exact hx

/-- **The bad event of the rescaled family** (deterministic): if `b T^b ≤ t` with `T^b` the exit time of `B_{ρ/3}` by
`R⁻¹ Λ_{b ·}`, then the stopped rescaled family process of Lemma 2.5 lies in `E_{t/b}`. -/
theorem mem_E_of_scaledExitTime_le {Λb : ℝ → Set ℂ} {R b Tb ρ t : ℝ} {D : Set ℂ} (hDd : Dense D) (hb : 0 < b)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hfam : IsConeHarmonicBallFamily μ Λ) (hlf : IsLocallyFiniteMeasure μ)
    (hstr : IsStrictlyGrowingOn Λ 1) (hR0 : 0 ≤ R) (hTb : 0 < Tb) (hfamb : IsConeHarmonicBallFamilyOn μ Λb (b * Tb))
    (hstopb : IsStoppedAtHalfBall (rescaledFamily Λb R b) Tb)
    (huniq : ∀ (T' : ℝ) (Λ' : ℝ → Set ℂ), 0 < T' → IsConeHarmonicBallFamilyOn μ Λ' (b * T') →
      IsStoppedAtHalfBall (rescaledFamily Λ' R b) T' → T' = Tb ∧ EqOn Λ' Λb (Ioo 0 (b * Tb)))
    (hbad : b * clusterExitTime (rescaledFamily Λ R b) ρ ≤ t) :
    ∀ q : ℚ, t / b < q → ¬ (familyProcess (rescaledFamily Λb R b) Tb ((q : ℝ), 0) ∧
      ∀ d : D, familyProcess (rescaledFamily Λb R b) Tb ((q : ℝ), (d : ℂ)) → ‖(d : ℂ)‖ < ρ / 4) := by
  have hR := pos_of_isStoppedAtHalfBall_rescaledFamily hb hR0 hTb hfamb hstopb
  have hfam' := harmonicBallFamilyScalingStep μ Λ R b hR hb hfam
  have h32 : (3 / 2 : ℝ) / 3 = 1 / 2 := by norm_num
  -- the rescaled family is small at small times, and `μ'(B_{1/2}) < ∞`
  have hsmall : ∃ s, 0 < s ∧ rescaledFamily Λ R b s ⊆ ball 0 ((3 / 2) / 3) := by
    obtain ⟨s0, hs0, hsub⟩ := exists_pos_subset_ball hfam.2.1 hstr (half_pos hR)
    refine ⟨s0 / b, div_pos hs0 hb, fun x hx => ?_⟩
    have hx' : (R : ℂ) * x ∈ Λ s0 := by
      have : b * (s0 / b) = s0 := mul_div_cancel₀ s0 hb.ne'
      have hx2 : (R : ℂ) * x ∈ Λ (b * (s0 / b)) := hx
      rwa [this] at hx2
    have h1 := hsub hx'
    rw [mem_ball, dist_zero_right, norm_dilation hR] at h1
    rw [h32, mem_ball, dist_zero_right]
    nlinarith
  have hpre : (fun x : ℂ => (R : ℂ) * x) ⁻¹' ball 0 (R / 2) = ball 0 ((3 / 2) / 3) := by
    ext x
    rw [mem_preimage, mem_ball, mem_ball, dist_zero_right, dist_zero_right, norm_dilation hR, h32]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hfin : rescaledMeasure μ R b (ball 0 ((3 / 2) / 3)) ≠ ⊤ := by
    rw [← hpre, rescaledMeasure_preimage μ hR.ne' b]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  obtain ⟨hbdd, hpos, hin, hout⟩ := clusterExitTime_spec hfam'.2.1 hfin hsmall
  rw [h32] at hin hout hbdd
  -- uniqueness in Lemma 2.5: the stopped family of Lemma 2.5 is `Λ` on `(0, b Tb)`
  obtain ⟨hTT, hEq⟩ := huniq _ Λ hpos (isConeHarmonicBallFamilyOn_of_global hfam (mul_pos hb hpos)) ⟨hin, hout⟩
  rw [familyProcess_rescaledFamily_congr hb hEq]
  rintro q hq ⟨h0, hD⟩
  have hq0 : 0 < (q : ℝ) := h0.1.1
  have hopen : IsOpen (rescaledFamily Λ R b q) := (hfam'.1 q hq0).1
  have hcl : rescaledFamily Λ R b q ⊆ closedBall 0 (ρ / 4) :=
    subset_closedBall_of_dense hDd hopen fun d hdD hdU => hD ⟨d, hdD⟩ ⟨h0.1, hdU⟩
  have hball : rescaledFamily Λ R b q ⊆ ball 0 (ρ / 3) :=
    hcl.trans (closedBall_subset_ball (by linarith))
  have hsubset : {t | 0 < t ∧ rescaledFamily Λ R b t ⊆ ball 0 (ρ / 3)} ⊆
      {t | 0 < t ∧ rescaledFamily Λ R b t ⊆ ball 0 (1 / 2)} :=
    fun s hs => ⟨hs.1, hs.2.trans (ball_subset_ball (by linarith))⟩
  have hbdd' : BddAbove {t | 0 < t ∧ rescaledFamily Λ R b t ⊆ ball 0 (ρ / 3)} := BddAbove.mono hsubset hbdd
  have hle : (q : ℝ) ≤ clusterExitTime (rescaledFamily Λ R b) ρ := le_csSup hbdd' ⟨hq0, hball⟩
  have : (q : ℝ) ≤ t / b := by
    rw [le_div_iff₀ hb]
    nlinarith
  linarith

/-- At small rational times the unscaled family process satisfies the condition of `E`. -/
theorem exists_rat_familyProcess (hfam : IsConeHarmonicBallFamily μ Λ) (hstr : IsStrictlyGrowingOn Λ 1)
    {T0 ρ : ℝ} (hT0 : 0 < T0) (hρ : 0 < ρ) (D : Set ℂ) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ familyProcess Λ T0 ((q : ℝ), 0) ∧
      ∀ d : D, familyProcess Λ T0 ((q : ℝ), (d : ℂ)) → ‖(d : ℂ)‖ < ρ / 4 := by
  obtain ⟨s, hs, hsub⟩ := exists_pos_subset_ball hfam.2.1 hstr (by linarith : 0 < ρ / 4)
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (lt_min hs hT0)
  have hqT : (q : ℝ) < T0 := lt_of_lt_of_le hq1 (min_le_right _ _)
  refine ⟨q, hq0, ⟨⟨hq0, hqT⟩, hfam.2.1.mem q hq0⟩, fun d hd => ?_⟩
  have h1 := hsub (hfam.2.1.monotoneOn hq0 hs (lt_of_lt_of_le hq1 (min_le_left _ _)).le hd.2)
  rwa [mem_ball, dist_zero_right] at h1

end Sec1

/-- **eq:btb-converge-to-inf** (`ScaledClusterExitTimeStep`) from Lemma 2.5, the measurability of the cone harmonic
ball families and their strict growth (Theorem 2.3). -/
theorem scaledClusterExitTimeStep_of_steps (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hmeas : ConeFamilyAEMeasurableStep) (hgrow : ConeHarmonicBallStrictGrowthStep) :
    ScaledClusterExitTimeStep := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ P hC hcirc μ hfield Λ hΛ t ht
  have hP : IsProbabilityMeasure P := hfield.1
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hDcount : Countable D := hDc.to_subtype
  -- the measurable events `E x` of family processes
  let E : ℝ → Set (ℝ × ℂ → Prop) := fun x => {F | ∀ q : ℚ, x < q → ¬ (F ((q : ℝ), 0) ∧
    ∀ d : D, F ((q : ℝ), (d : ℂ)) → ‖(d : ℂ)‖ < ρ / 4)}
  have hE : ∀ x, MeasurableSet (E x) := fun x =>
    measurableSet_setOfPred.2 (Measurable.forall fun q => measurable_const.imp
      ((measurable_pi_apply _).and (Measurable.forall fun d => (measurable_pi_apply _).imp measurable_const)).not)
  have hEmono : ∀ x y, x ≤ y → E x ⊆ E y := fun x y hxy F hF q hq => hF q (lt_of_le_of_lt hxy hq)
  -- a.s. properties of the family and of the measure
  have hlqg : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := hfield.2.2
  have hgood : ∀ᵐ ω ∂P, IsConeHarmonicBallFamily (μ ω) (Λ ω) ∧ IsLocallyFiniteMeasure (μ ω) ∧
      IsStrictlyGrowingOn (Λ ω) 1 := by
    filter_upwards [hΛ, hlqg, hgrow γ hγ hγ2 Ω P hC hcirc μ hfield] with ω h1 h2 h3
    exact ⟨h1, h2.isLocallyFiniteMeasure, h3 1 _ (Sec1.isConeHarmonicBallFamilyOn_of_global h1 one_pos)⟩
  -- the family stopped at the exit of `B_{1/2}`
  let T0 : Ω → ℝ := fun ω => clusterExitTime (Λ ω) (3 / 2)
  have h32 : (3 / 2 : ℝ) / 3 = 1 / 2 := by norm_num
  have hT0 : ∀ᵐ ω ∂P, 0 < T0 ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T0 ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T0 ω) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hfam, hlf, hstr⟩ := hω
    have hsmall := Sec1.exists_pos_subset_ball hfam.2.1 hstr (by norm_num : (0 : ℝ) < (3 / 2) / 3)
    obtain ⟨-, hpos, hin, hout⟩ := Sec1.clusterExitTime_spec hfam.2.1 measure_ball_lt_top.ne hsmall
    rw [h32] at hin hout
    exact ⟨hpos, Sec1.isConeHarmonicBallFamilyOn_of_global hfam hpos, hin, hout⟩
  have hpair := (hmeas γ hγ hγ2 Ω P hC hcirc μ hfield).1 T0 Λ hT0
  have hfp : AEMeasurable (fun ω => familyProcess (Λ ω) (T0 ω)) P := measurable_snd.comp_aemeasurable hpair
  -- `P[b T^b ≤ t] ≤ P[F ∈ E_{t/b}]` by Lemma 2.5
  have hbound : ∀ b : ℝ, 0 < b →
      P {ω | b * clusterExitTime (rescaledFamily (Λ ω) (coneScaleRadius γ (hcirc ω) b) b) ρ ≤ t} ≤
        P ((fun ω => familyProcess (Λ ω) (T0 ω)) ⁻¹' E (t / b)) := by
    intro b hb
    obtain ⟨Tb, Λb, hTb, hlawb⟩ := h25 γ hγ hγ2 Ω P hC hcirc μ hfield T0 Λ hT0 b hb
    have hpairb := (hmeas γ hγ hγ2 Ω P hC hcirc μ hfield).2 b hb Tb Λb
      (hTb.mono fun ω h => ⟨h.1, h.2.1, h.2.2.1⟩)
    have hEb : MeasurableSet ((univ : Set (Ioi (0 : ℝ) × ℂ → ℝ)) ×ˢ E (t / b)) := MeasurableSet.univ.prod (hE _)
    have key := (Measure.map_apply_of_aemeasurable hpairb hEb).symm.trans
      ((congrArg (fun m : Measure ((Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop)) =>
        m ((univ : Set (Ioi (0 : ℝ) × ℂ → ℝ)) ×ˢ E (t / b))) hlawb).symm.trans
        (Measure.map_apply_of_aemeasurable hpair hEb))
    have hsnd : ∀ (f : Ω → (Ioi (0 : ℝ) × ℂ → ℝ)) (g : Ω → (ℝ × ℂ → Prop)),
        P ((fun ω => (f ω, g ω)) ⁻¹' ((univ : Set (Ioi (0 : ℝ) × ℂ → ℝ)) ×ˢ E (t / b))) = P (g ⁻¹' E (t / b)) := by
      intro f g
      congr 1
      ext ω
      exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
    refine le_trans (measure_mono_ae ?_) ((hsnd _ _).symm.trans (key.trans (hsnd _ _))).le
    filter_upwards [hTb, hgood] with ω hω hg
    obtain ⟨hTbpos, hfamb, hstopb, huniq⟩ := hω
    obtain ⟨hfam, hlf, hstr⟩ := hg
    exact fun hbad => Sec1.mem_E_of_scaledExitTime_le hDd hb hρ hρ1 hfam hlf hstr
      (Sec1.coneScaleRadius_nonneg _ _ _) hTbpos hfamb hstopb huniq hbad
  -- `P[F ∈ E_{1/(n+1)}] → 0`
  let s : ℕ → Set Ω := fun n => (fun ω => familyProcess (Λ ω) (T0 ω)) ⁻¹' E (1 / ((n : ℝ) + 1))
  have hs_tend : Tendsto (fun n => P (s n)) atTop (𝓝 0) := by
    have hanti : Antitone s := by
      intro n m hnm
      refine preimage_mono (hEmono _ _ ?_)
      have : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h := tendsto_measure_iInter_atTop (μ := P) (fun n => hfp.nullMeasurableSet_preimage (hE _)) hanti
      ⟨0, measure_ne_top _ _⟩
    have h0 : P (⋂ n, s n) = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [hgood, hT0] with ω hg hT hmem
      obtain ⟨hfam, -, hstr⟩ := hg
      obtain ⟨q, hq0, hq1, hq2⟩ := Sec1.exists_rat_familyProcess hfam hstr hT.1 hρ D
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hq0
      exact (mem_iInter.1 hmem n) q hn ⟨hq1, hq2⟩
    rw [h0] at h
    exact h
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1 hs_tend e he).exists_forall_of_atTop
  rw [eventually_atTop]
  refine ⟨t * ((N : ℝ) + 1) + 1, fun b hb => ?_⟩
  have hb0 : 0 < b := by
    have : 0 ≤ t * ((N : ℝ) + 1) := by positivity
    linarith
  refine (hbound b hb0).trans (le_trans (measure_mono (preimage_mono (hEmono _ _ ?_))) (hN N le_rfl))
  rw [div_le_div_iff₀ hb0 (by positivity), one_mul]
  linarith

end MatedCRT
