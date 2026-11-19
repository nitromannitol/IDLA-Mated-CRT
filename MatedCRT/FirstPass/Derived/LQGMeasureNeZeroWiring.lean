import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfConeInputsDerived
import MatedCRT.FirstPass.Derived.AnnealedMedianLimitIdentified
import MatedCRT.FirstPass.Derived.ExitCdfMedianPos
import MatedCRT.FirstPass.Derived.LevyProkhorovWeakFiniteMeasure
import MatedCRT.Proofs.LBM.BrownianExitBall
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.TimeChange
import LatticeProb.Prob.PairingSymmetricAllTimes

/-!
# Nondegeneracy of the LQG measure and of the exit-time median of Liouville Brownian motion

Two nondegeneracy facts about a valid environment, in the almost sure form and in the form "almost everywhere for
the law of the data" used by the identification of subsequential limits of the walk laws (BG20, §7.3).

* `ae_μ_ne_zero_of_isValid`: the `γ`-LQG measure `μ_h` is almost surely nonzero. The curve `η` is parametrized by
  `μ_h`-area (§1.1 of the paper, `IsValid.isAreaParametrized`), so `μ_h(η([0,1])) = 1`.
* `measurableSet_ne_zero_of_continuous_cutoffWeightedMeasure`: if `d ↦ 6 ψ μX d` is Lévy–Prokhorov continuous for
  every nonnegative continuous compactly supported cutoff `ψ`, then `{d | μX d ≠ 0}` is Borel: it is the union over
  `n` of the open sets where the cutoff measure for a cutoff equal to `1` on `B̄_n(0)` has positive mass.
* `ae_map_ne_zero_of_isValid`, `ae_map_pairJ_ne_zero_of_isValid`: hence `μX d ≠ 0` for almost every `d` under the
  law of the data whenever `μX (D ω) = μ_h` almost surely.
* `ae_lbmPathLawField_exitTime_eq_zero_and_top`: almost surely, under the law
  `lbmPathLawField γ (pairJ ⊤ (H ω)) 0` of the rescaled Liouville Brownian motion from `0`, the exit time from
  `B_{1/2}` is almost surely positive and finite. The law field integrates bounded Lipschitz path functionals as
  the quenched law of `t ↦ B_{φ⁻¹(m₀ t)}` (`hLBM_lbmPathLawField`, with the continuity input
  `lbmLawContinuity_of_isValid`), which transfers the probabilities of the exit events `{τ ≤ s}`, written through
  the truncated running maximum (`ae_measure_rescaledLBMPath_mem_eq`); for the Liouville Brownian motion the exit
  time is positive (`ae_lbmExitTime_pos`) and finite (`ae_rescaledLBMExitTime_any_ball_lt_top`, `m₀ > 0`).
* `ae_medianOf_exitCdf_lbmPathLawField_ne_zero`: hence, for almost every `d` under the law of the data
  `(pairJ ⊤ H, E)`, the median of the exit time from `B_{1/2}` under `lbmPathLawField γ d.1 0` is nonzero
  (`medianOf_exitCdf_pos`).
-/

open MeasureTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

attribute [local instance] LatticeProb.dUnifMetricSpace

namespace MatedCRT.FirstPass.Derived

/-! ### The LQG measure is nonzero -/

/-- **The LQG measure of a valid environment is almost surely nonzero.** The curve `η` is parametrized by
`μ_h`-area (§1.1 of the paper, `IsValid.isAreaParametrized`), so `μ_h(η([0,1])) = 1`. -/
theorem ae_μ_ne_zero_of_isValid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, S.μ ω ≠ 0 := by
  filter_upwards [hS.isAreaParametrized] with ω hω hμ
  have h1 : (S.μ ω) (S.η ω '' Icc 0 1) = 1 := by
    rw [hω.2.2.2 0 1 zero_lt_one]
    simp
  rw [hμ] at h1
  simp at h1

/-- **Borel measurability of the nondegeneracy set.** If `d ↦ 6 ψ μX d` is Lévy–Prokhorov continuous for every
nonnegative continuous compactly supported cutoff `ψ`, then `{d | μX d ≠ 0}` is a Borel set. -/
theorem measurableSet_ne_zero_of_continuous_cutoffWeightedMeasure {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μX : X → Measure ℂ) [∀ d, IsLocallyFiniteMeasure (μX d)]
    (hπ : ∀ (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ), (∀ z, 0 ≤ ψ z) →
      Continuous fun d => LevyProkhorov.ofMeasure (cutoffWeightedMeasure (μX d) hψ hψc 6)) :
    MeasurableSet {d | μX d ≠ 0} := by
  have hex : ∀ n : ℕ, ∃ ψ : C(ℂ, ℝ), EqOn ψ 1 (closedBall (0 : ℂ) (n : ℝ)) ∧ HasCompactSupport ψ ∧
      ∀ z, ψ z ∈ Icc (0 : ℝ) 1 := fun n => by
    obtain ⟨ψ, hψ1, -, hψc, hψI⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_closedBall (0 : ℂ) (n : ℝ)) isClosed_empty (disjoint_empty _)
    exact ⟨ψ, hψ1, hψc, hψI⟩
  choose ψ hψ1 hψc hψI using hex
  have hmass : ∀ n d, ((cutoffWeightedMeasure (μX d) (ψ n).continuous (hψc n) 6).mass : ℝ≥0∞) =
      ∫⁻ z, ENNReal.ofReal (6 * ψ n z) ∂(μX d) := fun n d => by
    rw [FiniteMeasure.ennreal_mass, coe_cutoffWeightedMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  have hset : {d | μX d ≠ 0} = ⋃ n : ℕ,
      (fun d => (cutoffWeightedMeasure (μX d) (ψ n).continuous (hψc n) 6).mass) ⁻¹' {0}ᶜ := by
    ext d
    simp only [mem_ofPred_eq, mem_iUnion, mem_preimage, mem_compl_iff, mem_singleton_iff]
    constructor
    · intro hd
      by_contra hall
      refine hd (Measure.measure_univ_eq_zero.1 ?_)
      rw [← iUnion_closedBall_nat (0 : ℂ)]
      refine measure_iUnion_null fun n => ?_
      have h0 : ∫⁻ z, ENNReal.ofReal (6 * ψ n z) ∂(μX d) = 0 := by
        rw [← hmass n d, not_not.1 (not_exists.1 hall n), ENNReal.coe_zero]
      have hle : μX d (closedBall 0 n) ≤ ∫⁻ z, ENNReal.ofReal (6 * ψ n z) ∂(μX d) := by
        rw [← lintegral_indicator_one measurableSet_closedBall]
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ closedBall (0 : ℂ) n
        · rw [indicator_of_mem hz, Pi.one_apply, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by rw [hψ1 n hz, Pi.one_apply]; norm_num)
        · rw [indicator_of_notMem hz]
          exact bot_le
      exact nonpos_iff_eq_zero.1 (hle.trans h0.le)
    · rintro ⟨n, hn⟩ hd
      apply hn
      have h : ((cutoffWeightedMeasure (μX d) (ψ n).continuous (hψc n) 6).mass : ℝ≥0∞) = 0 := by
        rw [hmass n d, hd, lintegral_zero_measure]
      exact ENNReal.coe_eq_zero.1 h
  rw [hset]
  exact MeasurableSet.iUnion fun n => (FiniteMeasure.continuous_mass.comp
    (continuous_levyProkhorov_toFiniteMeasure.comp
      (hπ (ψ n) (ψ n).continuous (hψc n) fun z => (hψI n z).1))).measurable
    (measurableSet_singleton 0).compl

/-- **The LQG coordinate of the data is nonzero for almost every value of the data.** If the coordinate `μX (D ω)` of
measurable data `D` is almost surely the LQG measure `μ_h` and `{x | μX x ≠ 0}` is measurable, then `μX x ≠ 0` for
almost every `x` under the law of `D`. -/
theorem ae_map_ne_zero_of_isValid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {X : Type*} [MeasurableSpace X] {D : Ω → X}
    (hD : AEMeasurable D S.P) {μX : X → Measure ℂ} (hμX : MeasurableSet {x | μX x ≠ 0})
    (hDμ : ∀ᵐ ω ∂S.P, μX (D ω) = S.μ ω) :
    ∀ᵐ x ∂(S.P.map D), μX x ≠ 0 :=
  (ae_map_iff hD hμX).2 <| by
    filter_upwards [hDμ, ae_μ_ne_zero_of_isValid hS] with ω h1 h2
    rw [h1]
    exact h2

/-- **The LQG coordinate is nonzero for almost every value of the data `(pairJ ⊤ H, E)`.** Let `H` be a measurable
version of the field and `E` measurable data whose coordinate `μX (E ω)` is almost surely the LQG measure `μ_h`,
with `d ↦ 6 ψ μX d` Lévy–Prokhorov continuous for every cutoff `ψ`. Then `μX d.2 ≠ 0` for almost every `d` under the
law of `(pairJ ⊤ H, E)`. -/
theorem ae_map_pairJ_ne_zero_of_isValid {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M] {E : Ω → M}
    (hE : Measurable E) (μX : M → Measure ℂ) [∀ d, IsLocallyFiniteMeasure (μX d)]
    (hπ : ∀ (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ), (∀ z, 0 ≤ ψ z) →
      Continuous fun d => LevyProkhorov.ofMeasure (cutoffWeightedMeasure (μX d) hψ hψc 6))
    (hEμ : ∀ᵐ ω ∂S.P, μX (E ω) = S.μ ω) :
    ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)), μX d.2 ≠ 0 :=
  ae_map_ne_zero_of_isValid hS (((LQGMetric.measurable_pairJ ⊤).comp hH).prodMk hE).aemeasurable
    (μX := fun d => μX d.2)
    (measurable_snd (measurableSet_ne_zero_of_continuous_cutoffWeightedMeasure μX hπ)) hEμ

/-! ### The exit time of the rescaled Liouville Brownian motion is positive and finite -/

/-- **Quenched nondegeneracy of the exit time of the rescaled Liouville Brownian motion.** For a valid environment
at `0 < γ < 2` and a measurable version `H` of its field, almost surely, under the law
`lbmPathLawField γ (pairJ ⊤ (H ω)) 0` of the rescaled Liouville Brownian motion started at `0`, the exit time from
`B_{1/2}` is almost surely positive and almost surely finite. -/
theorem ae_lbmPathLawField_exitTime_eq_zero_and_top {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P,
      (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) 0 : Measure (ContinuousPath ℂ))
          {g | MarkovProcess.ContinuousPath.exitTime (ball (0 : ℂ) (1 / 2)) g = 0} = 0 ∧
        (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) 0 : Measure (ContinuousPath ℂ))
          {g | MarkovProcess.ContinuousPath.exitTime (ball (0 : ℂ) (1 / 2)) g = ⊤} = 0 := by
  have hm : 0 < S.m₀ := hS.m₀_pos hγ hγ2
  have hΛ := hLBM_lbmPathLawField lbmLawContinuity_of_isValid γ hγ hγ2 Ω S hS H hH hrep 0
  have hfam : ∀ s : ℝ≥0, ∀ᵐ ω ∂S.P,
      planarBrownianMotion 0 {b | 1 / 2 ≤ truncRunningMax s (rescaledLBMPath (S.clock ω) S.m₀ b)} =
        (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) 0 : Measure (ContinuousPath ℂ))
          {g | 1 / 2 ≤ truncRunningMax s ⇑g} := fun s =>
    ae_measure_rescaledLBMPath_mem_eq (D := fun ω => LQGMetric.pairJ ⊤ (H ω)) (Λ := lbmPathLawField γ) hΛ
      (F := fun k f => halfCutoff k (truncRunningMax s f))
      (fun k => isBoundedLipschitzPathFunctional_halfCutoff_comp (Φ := truncRunningMax s)
        (abs_truncRunningMax_sub_le s) k)
      (fun f => tendsto_halfCutoff_indicator (truncRunningMax s) f)
  have hmono : ∀ {s t : ℝ≥0}, s ≤ t → ∀ f, truncRunningMax s f ≤ truncRunningMax t f := by
    intro s t hst f
    have : Nonempty (Icc (0 : ℝ≥0) s) := ⟨⟨0, le_rfl, bot_le⟩⟩
    exact ciSup_le fun u => le_truncRunningMax f (u.2.2.trans hst)
  filter_upwards [hfam 0, ae_all_iff.2 fun n : ℕ => hfam n, hS.isLQGClock,
    hS.ae_lbmExitTime_pos (by norm_num : (0 : ℝ) < 1 / 2),
    hS.ae_rescaledLBMExitTime_any_ball_lt_top hm 0 0 (1 / 2)] with ω h0 hn hclk hpos hfin
  refine ⟨?_, ?_⟩
  · refine measure_mono_null (t := {g : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax 0 ⇑g}) ?_ ?_
    · intro g hg
      have hg' : MarkovProcess.ContinuousPath.exitTime (ball (0 : ℂ) (1 / 2)) g = 0 := hg
      refine (pathExitTime_ball_le_iff g.continuous 0).1 ?_
      show MarkovProcess.ContinuousPath.exitTime (ball (0 : ℂ) (1 / 2)) g ≤ ((0 : ℝ≥0) : ℝ≥0∞)
      rw [hg']
      exact bot_le
    · rw [← h0]
      refine measure_mono_null ?_ (ae_iff.1 ((hclk 0).2.and hpos))
      intro b hb
      show ¬ _
      rintro ⟨hb1, hb2⟩
      have h := (half_le_truncRunningMax_rescaledLBMPath_iff hm hb1 0).1 hb
      rw [NNReal.coe_zero, mul_zero, ENNReal.ofReal_zero] at h
      exact absurd h (not_le.2 hb2)
  · have hmonoA : Monotone fun n : ℕ =>
        {g : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) ⇑g} :=
      fun m n hmn g (hg : 1 / 2 ≤ truncRunningMax (m : ℝ≥0) ⇑g) => hg.trans (hmono (Nat.cast_le.2 hmn) _)
    have hmonoB : Monotone fun n : ℕ =>
        {b : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) (rescaledLBMPath (S.clock ω) S.m₀ b)} :=
      fun m n hmn b (hb : 1 / 2 ≤ truncRunningMax (m : ℝ≥0) (rescaledLBMPath (S.clock ω) S.m₀ b)) =>
        hb.trans (hmono (Nat.cast_le.2 hmn) _)
    have hae : ∀ᵐ b ∂planarBrownianMotion 0, b ∈ ⋃ n : ℕ,
        {b : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) (rescaledLBMPath (S.clock ω) S.m₀ b)} := by
      filter_upwards [(hclk 0).2, hfin] with b hb hb'
      obtain ⟨n, hn'⟩ := ENNReal.exists_nat_gt hb'.ne
      refine mem_iUnion.2 ⟨n, ?_⟩
      refine (pathExitTime_ball_le_iff (continuous_rescaledLBMPath (m := S.m₀) hb) (n : ℝ≥0)).1 ?_
      rw [ENNReal.coe_natCast]
      exact hn'.le
    have hBM1 : planarBrownianMotion 0 (⋃ n : ℕ,
        {b : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) (rescaledLBMPath (S.clock ω) S.m₀ b)}) = 1 := by
      have hc : planarBrownianMotion 0 (⋃ n : ℕ,
          {b : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) (rescaledLBMPath (S.clock ω) S.m₀ b)})ᶜ = 0 := by
        rw [Set.compl_def]
        exact ae_iff.1 hae
      rw [measure_congr (ae_eq_univ.2 hc), measure_univ]
    have hΛ1 : (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) 0 : Measure (ContinuousPath ℂ))
        (⋃ n : ℕ, {g : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) ⇑g}) = 1 := by
      calc (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) 0 : Measure (ContinuousPath ℂ))
            (⋃ n : ℕ, {g : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) ⇑g})
          = ⨆ n : ℕ, (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) 0 : Measure (ContinuousPath ℂ))
              {g : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) ⇑g} := hmonoA.measure_iUnion
        _ = ⨆ n : ℕ, planarBrownianMotion 0
              {b : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) (rescaledLBMPath (S.clock ω) S.m₀ b)} :=
            iSup_congr fun n => (hn n).symm
        _ = planarBrownianMotion 0 (⋃ n : ℕ,
              {b : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) (rescaledLBMPath (S.clock ω) S.m₀ b)}) :=
            hmonoB.measure_iUnion.symm
        _ = 1 := hBM1
    have hmeas : MeasurableSet (⋃ n : ℕ, {g : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax (n : ℝ≥0) ⇑g}) :=
      MeasurableSet.iUnion fun n => measurableSet_le measurable_const (continuous_truncRunningMax _).measurable
    refine measure_mono_null ?_ ((prob_compl_eq_zero_iff hmeas).2 hΛ1)
    intro g hg hmem
    obtain ⟨n, hn'⟩ := mem_iUnion.1 hmem
    have h := (pathExitTime_ball_le_iff g.continuous (n : ℝ≥0)).2 hn'
    have hg' : pathExitTime (ball (0 : ℂ) (1 / 2)) ⇑g = ⊤ := hg
    rw [hg'] at h
    exact ENNReal.coe_ne_top (top_le_iff.1 h)

/-- **The exit-time median of the rescaled Liouville Brownian motion is nonzero for almost every value of the
data.** For a valid environment at `0 < γ < 2`, a measurable version `H` of its field and measurable data `E`, for
almost every `d` under the law of `(pairJ ⊤ H, E)` the median of the exit time from `B_{1/2}` under the law
`lbmPathLawField γ d.1 0` of the rescaled Liouville Brownian motion from `0` is nonzero. -/
theorem ae_medianOf_exitCdf_lbmPathLawField_ne_zero {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {M : Type*} [MeasurableSpace M] {E : Ω → M} (hE : Measurable E) :
    ∀ᵐ d ∂(S.P.map fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω)),
      medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2))
        (lbmPathLawField γ d.1 0 : Measure (ContinuousPath ℂ))) ≠ 0 := by
  have hκP : Measurable fun x : LQGMetric.CoordJ → ℝ =>
      (lbmPathLawField γ x 0 : ProbabilityMeasure (ContinuousPath ℂ)) :=
    (continuous_eval_const (0 : ℂ)).measurable.comp (measurable_lbmPathLawField γ)
  have hκ : Measurable fun x : LQGMetric.CoordJ → ℝ =>
      (lbmPathLawField γ x 0 : Measure (ContinuousPath ℂ)) :=
    measurable_subtype_coe.comp hκP
  have hT0 : MeasurableSet {g : ContinuousPath ℂ |
      MarkovProcess.ContinuousPath.exitTime (ball (0 : ℂ) (1 / 2)) g = 0} :=
    (MarkovProcess.ContinuousPath.measurable_exitTime _ isOpen_ball) (measurableSet_singleton 0)
  have hTT : MeasurableSet {g : ContinuousPath ℂ |
      MarkovProcess.ContinuousPath.exitTime (ball (0 : ℂ) (1 / 2)) g = ⊤} :=
    (MarkovProcess.ContinuousPath.measurable_exitTime _ isOpen_ball) (measurableSet_singleton ⊤)
  have hQ : MeasurableSet {d : (LQGMetric.CoordJ → ℝ) × M |
      (lbmPathLawField γ d.1 0 : Measure (ContinuousPath ℂ))
          {g | MarkovProcess.ContinuousPath.exitTime (ball (0 : ℂ) (1 / 2)) g = 0} = 0 ∧
        (lbmPathLawField γ d.1 0 : Measure (ContinuousPath ℂ))
          {g | MarkovProcess.ContinuousPath.exitTime (ball (0 : ℂ) (1 / 2)) g = ⊤} = 0} :=
    ((((Measure.measurable_coe hT0).comp hκ).comp measurable_fst) (measurableSet_singleton 0)).inter
      ((((Measure.measurable_coe hTT).comp hκ).comp measurable_fst) (measurableSet_singleton 0))
  have hD : Measurable fun ω => (LQGMetric.pairJ ⊤ (H ω), E ω) :=
    ((LQGMetric.measurable_pairJ ⊤).comp hH).prodMk hE
  have hae := (ae_map_iff hD.aemeasurable hQ).2
    (ae_lbmPathLawField_exitTime_eq_zero_and_top hγ hγ2 hS hH hrep)
  filter_upwards [hae] with d hd
  exact (medianOf_exitCdf_pos (ball (0 : ℂ) (1 / 2)) isOpen_ball
    (lbmPathLawField γ d.1 0 : Measure (ContinuousPath ℂ)) hd.1 hd.2).ne'

end MatedCRT.FirstPass.Derived
