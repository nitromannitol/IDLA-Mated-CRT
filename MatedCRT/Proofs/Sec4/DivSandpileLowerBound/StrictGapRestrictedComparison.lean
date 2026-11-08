import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapLaplacian
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapFixedTime
import HarmonicBalls.Proofs.Sec5.DominatedShiftCompatibility

/-! Comparison and fixed-time reduction for disc-restricted measures. -/

namespace MatedCRT

open Set MeasureTheory Metric _root_.HarmonicBalls

/-- The regularized cluster comparison transfers to the measure restricted to
its disc, using only regularity and frontier nullity of the original measure. -/
theorem restricted_cluster_comparison
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {ρ βm βp : ℝ}
    (hρ : 0 < ρ) (hV : VolumeGrowth μ ρ βm βp) {z : ℂ} (hz : z ∈ ball 0 ρ)
    (hnull : ∀ s : ℝ, 0 < s → closure (cluster μ ρ z s) ⊆ ball 0 ρ →
      μ (frontier (cluster μ ρ z s)) = 0)
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hcompact : closure (cluster (μ.restrict (ball 0 ρ)) ρ z t) ⊆ ball 0 ρ) :
    interior (closure (cluster (μ.restrict (ball 0 ρ)) ρ z s)) ⊆
      cluster (μ.restrict (ball 0 ρ)) ρ z t := by
  rw [← cluster_eq_restrict_ball μ ρ t z] at hcompact ⊢
  rw [← cluster_eq_restrict_ball μ ρ s z]
  exact regularized_cluster_subset_later_cluster hμ hρ hV hz hnull hs hst hcompact

/-- Fixed-time regularization defects are null when compact cluster frontiers
are null, the shifted restricted measure laws are absolutely continuous, and
the defect event satisfies the stated measurability hypotheses. -/
theorem ae_no_regularization_defect_of_regular_measure_and_restricted_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) {ρ t γ : ℝ} {z : ℂ} (hρ : 0 < ρ) (ht : 0 < t)
    (hγ : γ ≠ 0) (hz : z ∈ ball 0 ρ)
    (hregular : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      VolumeGrowth (μ ω) ρ βm βp ∧
      ∀ s : ℝ, 0 < s → closure (cluster (μ ω) ρ z s) ⊆ ball 0 ρ →
        μ ω (frontier (cluster (μ ω) ρ z s)) = 0)
    (hB : MeasurableSet (confinedRegularizationDefect ρ t z))
    (hY : ∀ c : ℝ, AEMeasurable (fun ω =>
      ENNReal.ofReal (Real.exp (γ * c)) • (μ ω).restrict (ball 0 ρ)) P)
    (hjoint : MeasurableSet {p : Ω × ℝ |
      ENNReal.ofReal (Real.exp (γ * p.2)) • (μ p.1).restrict (ball 0 ρ) ∈
        confinedRegularizationDefect ρ t z})
    (hlaw : ∀ c : ℝ,
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) •
        (μ ω).restrict (ball 0 ρ)) P ≪
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
        (μ ω).restrict (ball 0 ρ)) P) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) ρ z t) ⊆ ball 0 ρ →
      interior (closure (cluster (μ ω) ρ z t)) = cluster (μ ω) ρ z t := by
  have hopen : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      IsOpen (cluster ((μ ω).restrict (ball 0 ρ)) ρ z s) := by
    filter_upwards [hregular] with ω ⟨βm, βp, hμ, hV, _⟩
    intro s hs
    rw [← cluster_eq_restrict_ball (μ ω) ρ s z]
    exact (cluster_open_laplacian_of_general greenFunctionBall
      obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ hρ hV hz hs).1
  have hcompare : ∀ᵐ ω ∂P, ∀ s u : ℝ, 0 < s → s < u →
      closure (cluster ((μ ω).restrict (ball 0 ρ)) ρ z u) ⊆ ball 0 ρ →
      interior (closure (cluster ((μ ω).restrict (ball 0 ρ)) ρ z s)) ⊆
        cluster ((μ ω).restrict (ball 0 ρ)) ρ z u := by
    filter_upwards [hregular] with ω ⟨βm, βp, hμ, hV, hnull⟩
    intro s u hs hsu hc
    exact restricted_cluster_comparison hμ hρ hV hz hnull hs hsu hc
  have hresult := ae_no_regularization_defect_of_shifted_measure_law P
    (fun ω => (μ ω).restrict (ball 0 ρ)) ht hγ hopen hcompare hB hY hjoint hlaw
  filter_upwards [hresult] with ω hω hc
  rw [← cluster_eq_restrict_ball (μ ω) ρ t z] at hω
  exact hω hc

/-- Scalar multiplication and restriction are jointly measurable for the
usual evaluation sigma algebra on measures. -/
theorem measurable_restricted_smul_measure (B : Set ℂ) (hB : MeasurableSet B) :
    Measurable (fun p : ENNReal × Measure ℂ => p.1 • p.2.restrict B) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs]
  exact measurable_fst.mul ((Measure.measurable_coe (hs.inter hB)).comp measurable_snd)

/-- The restricted exponential mass-shift family is jointly measurable when
the random measure is measurable. -/
theorem measurable_restricted_exponential_mass_shift
    {Ω : Type*} [MeasurableSpace Ω] {μ : Ω → Measure ℂ} (hμ : Measurable μ)
    (ρ γ : ℝ) : Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (γ * p.2)) • (μ p.1).restrict (ball 0 ρ)) := by
  let F : Ω × ℝ → ENNReal × Measure ℂ :=
    fun p => (ENNReal.ofReal (Real.exp (γ * p.2)), μ p.1)
  have hF : Measurable F :=
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_snd))).prodMk
      (hμ.comp measurable_fst)
  exact (measurable_restricted_smul_measure (ball 0 ρ) measurableSet_ball).comp hF

/-- For a measurable random measure, measurability of the defect set alone
implies the joint and section measurability needed by the Tonelli reduction. -/
theorem ae_no_regularization_defect_of_measurable_measure_and_restricted_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμm : Measurable μ) {ρ t γ : ℝ} {z : ℂ}
    (hρ : 0 < ρ) (ht : 0 < t) (hγ : γ ≠ 0) (hz : z ∈ ball 0 ρ)
    (hregular : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      VolumeGrowth (μ ω) ρ βm βp ∧
      ∀ s : ℝ, 0 < s → closure (cluster (μ ω) ρ z s) ⊆ ball 0 ρ →
        μ ω (frontier (cluster (μ ω) ρ z s)) = 0)
    (hB : MeasurableSet (confinedRegularizationDefect ρ t z))
    (hlaw : ∀ c : ℝ,
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) •
        (μ ω).restrict (ball 0 ρ)) P ≪
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
        (μ ω).restrict (ball 0 ρ)) P) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) ρ z t) ⊆ ball 0 ρ →
      interior (closure (cluster (μ ω) ρ z t)) = cluster (μ ω) ρ z t := by
  have hshift := measurable_restricted_exponential_mass_shift hμm ρ γ
  apply ae_no_regularization_defect_of_regular_measure_and_restricted_law
    P μ hρ ht hγ hz hregular hB _ (hshift hB) hlaw
  intro c
  exact (hshift.comp (measurable_id.prodMk measurable_const)).aemeasurable

/-- The fixed-time reduction also applies to almost-everywhere measurable
random measures, by passing to a measurable representative. -/
theorem ae_no_regularization_defect_of_ae_measurable_measure_and_restricted_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμm : AEMeasurable μ P) {ρ t γ : ℝ} {z : ℂ}
    (hρ : 0 < ρ) (ht : 0 < t) (hγ : γ ≠ 0) (hz : z ∈ ball 0 ρ)
    (hregular : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      VolumeGrowth (μ ω) ρ βm βp ∧
      ∀ s : ℝ, 0 < s → closure (cluster (μ ω) ρ z s) ⊆ ball 0 ρ →
        μ ω (frontier (cluster (μ ω) ρ z s)) = 0)
    (hB : MeasurableSet (confinedRegularizationDefect ρ t z))
    (hlaw : ∀ c : ℝ,
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) •
        (μ ω).restrict (ball 0 ρ)) P ≪
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
        (μ ω).restrict (ball 0 ρ)) P) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) ρ z t) ⊆ ball 0 ρ →
      interior (closure (cluster (μ ω) ρ z t)) = cluster (μ ω) ρ z t := by
  let ν := hμm.mk μ
  have hνm : Measurable ν := hμm.measurable_mk
  have heq : μ =ᵐ[P] ν := hμm.ae_eq_mk
  have hregν : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (ν ω) ∧
      VolumeGrowth (ν ω) ρ βm βp ∧
      ∀ s : ℝ, 0 < s → closure (cluster (ν ω) ρ z s) ⊆ ball 0 ρ →
        ν ω (frontier (cluster (ν ω) ρ z s)) = 0 := by
    filter_upwards [hregular, heq] with ω hω hν
    simpa only [hν] using hω
  have hmap (c : ℝ) :
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
          (μ ω).restrict (ball 0 ρ)) P =
        Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
          (ν ω).restrict (ball 0 ρ)) P := by
    apply Measure.map_congr
    filter_upwards [heq] with ω hω
    rw [hω]
  have hlawν : ∀ c : ℝ,
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) •
        (ν ω).restrict (ball 0 ρ)) P ≪
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
        (ν ω).restrict (ball 0 ρ)) P := by
    intro c
    rw [← hmap 0, ← hmap c]
    exact hlaw c
  have hresult := ae_no_regularization_defect_of_measurable_measure_and_restricted_law
    P ν hνm hρ ht hγ hz hregν hB hlawν
  filter_upwards [hresult, heq] with ω hω hν
  simpa only [hν] using hω

end MatedCRT
