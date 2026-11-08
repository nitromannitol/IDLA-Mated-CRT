import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.TruncatedJointAE

/-!
# Lemma 3.4 (item 3 and E-c2-9 H2): the environment-dependent truncated path integrals are measurable

`lbmTruncatedOccupationMeasurableStep_holds` proves `LBMTruncatedOccupationMeasurableStep 𝒮` (Final.lean) and
`truncatedFixedTimeIntegrableStep_holds` proves `TruncatedFixedTimeIntegrableStep 𝒮` (FixedTimeReduction.lean), from the
jointly measurable version `exists_truncated_joint` of the truncated path integrals.
-/

open Classical

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- A Hölder continuous function on a set is continuous there. -/
lemma continuousOn_of_isHolder {f : ℂ → ℝ} {s : Set ℂ} (h : IsHolderContinuousOn f s) : ContinuousOn f s := by
  obtain ⟨C, χ, hχ, -, hH⟩ := h
  exact hH.continuousOn hχ

/-- **Item 3 (proved):** the truncated LBM occupations are measurable in the environment and the truncated path
integrals are strongly measurable in the Brownian variable. -/
theorem lbmTruncatedOccupationMeasurableStep_holds (𝒮 : SpaceFillingSLEModel) :
    LBMTruncatedOccupationMeasurableStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr _ _ f hfm _ hfc
  choose Ĥ hĤm hĤae using fun n : ℕ =>
    exists_truncated_joint hS hγ hγ2 hr f hfm (fun ω => continuousOn_of_isHolder (hfc ω)) (n : ℝ)
  have hA : ∀ n : ℕ, ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y, Ĥ n (ω, b) =
      ∫ t in Ioc (0 : ℝ) (min (n : ℝ) (pathExitTime (ball z r)
        (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal),
        f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal) :=
    fun n => (hĤae n).mono fun ω h => h.mono fun b hb => hb.1
  have hA' := ae_all_iff.2 hA
  refine ⟨?_, ?_⟩
  · filter_upwards [hA'] with ω hω
    intro n
    have hm : Measurable fun b : ContinuousPath ℂ => Ĥ n (ω, b) :=
      (hĤm n).comp measurable_prodMk_left
    exact hm.stronglyMeasurable.aestronglyMeasurable.congr
      (by filter_upwards [hω n] with b hb; exact hb)
  · intro n
    have hm : Measurable fun ω => ∫ b, Ĥ n (ω, b) ∂planarBrownianMotion y :=
      (StronglyMeasurable.integral_prod_right (f := fun (ω : Ω) (b : ContinuousPath ℂ) => Ĥ n (ω, b))
        (hĤm n).stronglyMeasurable).measurable
    refine hm.aemeasurable.congr ?_
    filter_upwards [hA'] with ω hω
    exact integral_congr_ae (hω n)

/-- **E-c2-9 H2 (proved):** for environment-dependent Hölder test functions, the truncated path functionals are almost
surely strongly measurable in the Brownian variable and integrable in time. -/
theorem truncatedFixedTimeIntegrableStep_holds (𝒮 : SpaceFillingSLEModel) :
    TruncatedFixedTimeIntegrableStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr _ _ f hfm hfb hfc T hT
  obtain ⟨Ĥ, hĤm, hĤae⟩ :=
    exists_truncated_joint hS hγ hγ2 hr f hfm (fun ω => continuousOn_of_isHolder (hfc ω)) T
  filter_upwards [hĤae] with ω hω
  obtain ⟨M, hM⟩ := hfb ω
  unfold TruncatedPathIntegrable
  refine ⟨?_, ?_⟩
  · have hm : Measurable fun b : ContinuousPath ℂ => Ĥ (ω, b) :=
      hĤm.comp measurable_prodMk_left
    exact hm.stronglyMeasurable.aestronglyMeasurable.congr
      (by filter_upwards [hω] with b hb; exact hb.1)
  · filter_upwards [hω] with b hb
    obtain ⟨-, hmeas⟩ := hb
    have hae : ∀ᵐ t ∂(volume : Measure ℝ),
        t ≠ (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal := by
      filter_upwards [(Set.countable_singleton _).ae_notMem (volume : Measure ℝ)] with t ht
      exact fun h => ht (Set.mem_singleton_iff.2 h)
    have hfin : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (min T
        (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    refine Integrable.mono' (integrable_const M) hmeas ?_
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioc] with t ht hmt
    obtain ⟨ht0, htm⟩ := hmt
    have htlt : t < (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal :=
      lt_of_le_of_ne (le_trans htm (min_le_right _ _)) ht
    have hball := path_mem_ball_of_lt_truncation (T := t + 1) ht0 (lt_min (lt_add_one t) htlt)
    show ‖f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)‖ ≤ M
    rw [Real.norm_eq_abs]
    exact hM _ hball

end MatedCRT
