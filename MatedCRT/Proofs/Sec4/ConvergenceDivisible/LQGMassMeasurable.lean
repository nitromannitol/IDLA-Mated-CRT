import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LQGMeasureMeasurable
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.UrysohnsLemma
import HarmonicBalls.Proofs.Sec3.Basic

/-! # Measurability of LQG mass on compact sets -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls HasOuterApproxClosed Function
open scoped ENNReal NNReal

/-- A compact set has measurable LQG mass. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_compact_mass
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {K : Set ℂ} (hK : IsCompact K) :
    AEMeasurable (fun ω => (S.μ ω K).toReal) S.P := by
  classical
  obtain ⟨χ, hχK, _, hχc, hχrange⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let F : ℕ → ℂ → ℝ := fun n x => χ x * (hK.isClosed.apprSeq n x : ℝ)
  have hFcont (n : ℕ) : Continuous (F n) :=
    χ.continuous.mul (continuous_subtype_val.comp (hK.isClosed.apprSeq n).continuous)
  have hFc (n : ℕ) : HasCompactSupport (F n) := hχc.mul_right
  apply aemeasurable_of_tendsto_metrizable_ae atTop (f := fun n ω => ∫ x, F n x ∂(S.μ ω))
  · exact fun n => hS.aemeasurable_lqg_integral (F n) (hFcont n) (hFc n)
  · filter_upwards [hS.isLQGMeasure] with ω hω
    let _ := hω.isLocallyFiniteMeasure
    have hint : Integrable χ (S.μ ω) := χ.continuous.integrable_of_hasCompactSupport hχc
    have hdom (n : ℕ) : ∀ᵐ x ∂(S.μ ω), ‖F n x‖ ≤ χ x := by
      filter_upwards [] with x
      have hn : (0 : ℝ) ≤ (hK.isClosed.apprSeq n x : ℝ) := by positivity
      have hle : (hK.isClosed.apprSeq n x : ℝ) ≤ 1 := by
        exact_mod_cast apprSeq_apply_le_one hK.isClosed n x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχrange x).1 hn)]
      exact mul_le_of_le_one_right (hχrange x).1 hle
    have hlim : ∀ᵐ x ∂(S.μ ω), Tendsto (fun n => F n x) atTop
        (𝓝 (K.indicator (fun _ => (1 : ℝ)) x)) := by
      filter_upwards [] with x
      have ha := (tendsto_pi_nhds.mp (tendsto_apprSeq hK.isClosed)) x
      have ha' := continuous_subtype_val.continuousAt.tendsto.comp ha
      change Tendsto (fun n => ((hK.isClosed.apprSeq n x : ℝ≥0) : ℝ)) atTop
        (𝓝 ((K.indicator (fun _ => (1 : ℝ≥0)) x : ℝ≥0) : ℝ)) at ha'
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx, NNReal.coe_one] at ha'
        simpa only [F, hχK hx, Pi.one_apply, one_mul, indicator_of_mem hx] using ha'
      · simp only [indicator_of_notMem hx, NNReal.coe_zero] at ha'
        simpa only [F, indicator_of_notMem hx, mul_zero] using
          (tendsto_const_nhds (x := χ x)).mul ha'
    have ht := tendsto_integral_of_dominated_convergence χ
      (fun n => (hFcont n).aestronglyMeasurable) hint hdom hlim
    change Tendsto _ _ (𝓝 (∫ a, K.indicator (1 : ℂ → ℝ) a ∂(S.μ ω))) at ht
    rw [integral_indicator_one hK.isClosed.measurableSet, measureReal_def] at ht
    exact ht

/-- A compact set has measurable extended nonnegative LQG mass. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_compact_mass_ennreal
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {K : Set ℂ} (hK : IsCompact K) :
    AEMeasurable (fun ω => S.μ ω K) S.P := by
  apply (hS.aemeasurable_lqg_compact_mass hK).ennreal_ofReal.congr
  filter_upwards [hS.isLQGMeasure] with ω hω
  let _ := hω.isLocallyFiniteMeasure
  exact ENNReal.ofReal_toReal hK.measure_ne_top

/-- Every closed set has measurable extended nonnegative LQG mass. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_closed_mass
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {F : Set ℂ} (hF : IsClosed F) :
    AEMeasurable (fun ω => S.μ ω F) S.P := by
  let K : ℕ → Set ℂ := fun n => F ∩ closedBall 0 n
  have hK (n : ℕ) : IsCompact (K n) :=
    (isCompact_closedBall (0 : ℂ) n).inter_left hF
  have hmono : Monotone K := fun _ _ h => inter_subset_inter_right F
    (closedBall_subset_closedBall (by exact_mod_cast h))
  have hunion : (⋃ n, K n) = F := by
    simp only [K, ← inter_iUnion, iUnion_closedBall_nat, inter_univ]
  have hm : AEMeasurable (fun ω => ⨆ n, S.μ ω (K n)) S.P :=
    AEMeasurable.iSup fun n => hS.aemeasurable_lqg_compact_mass_ennreal (hK n)
  convert hm using 1
  funext ω
  rw [← hmono.measure_iUnion, hunion]

/-- The LQG mass of a Borel set intersected with a compact set is measurable. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_mass_inter_compact
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {K : Set ℂ} (hK : IsCompact K) (A : Set ℂ) (hA : MeasurableSet A) :
    AEMeasurable (fun ω => S.μ ω (A ∩ K)) S.P := by
  classical
  induction A, hA using MeasurableSpace.induction_on_inter
      ((BorelSpace.measurable_eq (α := ℂ)).trans borel_eq_generateFrom_isClosed)
      isPiSystem_isClosed with
  | empty => simp
  | basic A hA =>
    exact hS.aemeasurable_lqg_compact_mass_ennreal (hK.inter_left hA)
  | compl A hA ih =>
    apply (hS.aemeasurable_lqg_compact_mass_ennreal hK).sub ih |>.congr
    filter_upwards [hS.isLQGMeasure] with ω hω
    let _ := hω.isLocallyFiniteMeasure
    have hfin : S.μ ω (A ∩ K) ≠ ∞ := ne_top_of_le_ne_top hK.measure_ne_top
      (measure_mono inter_subset_right)
    have heq : K \ (A ∩ K) = Aᶜ ∩ K := by ext x; simp [and_comm]
    rw [← heq, measure_sdiff inter_subset_right (hA.inter hK.isClosed.measurableSet).nullMeasurableSet hfin]
    rfl
  | iUnion f hfd hfm ih =>
    have hdis : Pairwise (Disjoint on fun n => f n ∩ K) := by
      intro i j hij
      exact (hfd hij).mono inter_subset_left inter_subset_left
    have hm : AEMeasurable (fun ω => ∑' n : ℕ, S.μ ω (f n ∩ K)) S.P :=
      AEMeasurable.tsum ih
    simpa only [iUnion_inter, measure_iUnion hdis (fun n => (hfm n).inter hK.isClosed.measurableSet)] using hm

/-- Every Borel set has measurable extended nonnegative LQG mass. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_mass
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (A : Set ℂ) (hA : MeasurableSet A) :
    AEMeasurable (fun ω => S.μ ω A) S.P := by
  let K : ℕ → Set ℂ := fun n => A ∩ closedBall 0 n
  have hmono : Monotone K := fun _ _ h => inter_subset_inter_right A
    (closedBall_subset_closedBall (by exact_mod_cast h))
  have hunion : (⋃ n, K n) = A := by
    simp only [K, ← inter_iUnion, iUnion_closedBall_nat, inter_univ]
  have hm : AEMeasurable (fun ω => ⨆ n, S.μ ω (K n)) S.P :=
    AEMeasurable.iSup fun n => hS.aemeasurable_lqg_mass_inter_compact
      (isCompact_closedBall 0 n) A hA
  convert hm using 1
  funext ω
  rw [← hmono.measure_iUnion, hunion]

/-- The integral of a nonnegative measurable function against the LQG
measure is a measurable extended nonnegative random variable. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_lintegral
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ x, f x ∂(S.μ ω)) S.P := by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine AEMeasurable.iSup fun n => Finset.aemeasurable_fun_sum _ fun i _ => ?_
  exact (hS.aemeasurable_lqg_mass _ ((SimpleFunc.eapprox f n).measurableSet_preimage _)).const_mul i

/-- The integral of a nonnegative measurable function against the LQG
measure is an almost-everywhere measurable real random variable. -/
theorem MatedCRTEnv.IsValid.aemeasurable_lqg_integral_nonneg
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (f : ℂ → ℝ) (hf : Measurable f) (hpos : 0 ≤ f) :
    AEMeasurable (fun ω => ∫ x, f x ∂(S.μ ω)) S.P := by
  apply (hS.aemeasurable_lqg_lintegral (fun x => ENNReal.ofReal (f x))
    hf.ennreal_ofReal).ennreal_toReal.congr
  exact Filter.Eventually.of_forall fun ω =>
    (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos)
      hf.aestronglyMeasurable).symm

/-- The Green potential of the LQG measure is measurable at every spatial
point. -/
theorem MatedCRTEnv.IsValid.aemeasurable_greenPotentialBall
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (R : ℝ) (x : ℂ) :
    AEMeasurable (fun ω => greenPotentialBall (S.μ ω) R x) S.P := by
  let f : ℂ → ℝ := (ball (0 : ℂ) R).indicator
    (fun y => greenFunction (ball (0 : ℂ) R) y x)
  have hf : Measurable f :=
    ((measurable_greenFunction_ball_uncurry R).comp
      (measurable_id.prodMk measurable_const)).indicator measurableSet_ball
  have hpos : 0 ≤ f := by
    intro y
    by_cases hy : y ∈ ball (0 : ℂ) R
    · simpa [f, hy] using greenFunction_nonneg (isBounded_ball (x := (0 : ℂ)) (r := R)) y x
    · simp [f, hy]
  convert hS.aemeasurable_lqg_integral_nonneg f hf hpos using 1
  funext ω
  simp [greenPotentialBall, f, integral_indicator measurableSet_ball]

/-- Almost sure continuity on a closed ball gives a jointly measurable Green
potential version agreeing simultaneously at every point of the ball. -/
theorem MatedCRTEnv.IsValid.exists_jointlyMeasurable_greenPotentialBall
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ᵐ ω ∂S.P, ContinuousOn (greenPotentialBall (S.μ ω) R) (closedBall 0 R)) :
    ∃ g : Ω × ℂ → ℝ, Measurable g ∧ ∀ᵐ ω ∂S.P,
      ∀ x ∈ closedBall (0 : ℂ) R, g (ω, x) = greenPotentialBall (S.μ ω) R x := by
  obtain ⟨g, hg, hga⟩ := exists_jointlyMeasurable_on_event S.P
    (closedBall (0 : ℂ) R) isClosed_closedBall.measurableSet 0
    (by simpa using hR) univ MeasurableSet.univ
    (fun ω => greenPotentialBall (S.μ ω) R)
    (hS.aemeasurable_greenPotentialBall R) (by simpa using hc)
  exact ⟨g, hg, by simpa using hga⟩

/-- Under almost sure volume growth, measurability of the shifted least
supersolution implies measurability of the original least supersolution. -/
theorem MatedCRTEnv.IsValid.aemeasurable_leastSupersolution_of_shifted
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (R t : ℝ) (z x : ℂ) (hR : 0 < R) (ht : 0 < t)
    (hz : z ∈ ball (0 : ℂ) R) (hx : x ∈ closedBall (0 : ℂ) R)
    (hV : ∀ᵐ ω ∂S.P, ∃ βminus βplus, VolumeGrowth (S.μ ω) R βminus βplus)
    (hshift : AEMeasurable (fun ω => shiftedLeastSupersolution (S.μ ω) R z t x) S.P) :
    AEMeasurable (fun ω => leastSupersolution (S.μ ω) R z t x) S.P := by
  apply (hshift.sub (hS.aemeasurable_greenPotentialBall R x)).congr
  filter_upwards [hV, hS.isLQGMeasure] with ω ⟨βminus, βplus, hgrowth⟩ hω
  exact ((obstacleCompatibilityShiftStep_holds (S.μ ω) hω.isLocallyFiniteMeasure
    R βminus βplus hR hgrowth z hz t ht).2.1 x hx).symm

end MatedCRT
