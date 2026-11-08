import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapRestrictedComparison

/-! A measurable representative for the fixed-time regularization defect. -/

namespace MatedCRT

open Set MeasureTheory Metric _root_.HarmonicBalls

/-- A measurable set representing the defect along almost every shifted
sample suffices for the fixed-time Tonelli argument. -/
theorem ae_no_regularization_defect_of_measurable_representative
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμm : Measurable μ) {ρ t γ : ℝ} {z : ℂ}
    (hρ : 0 < ρ) (ht : 0 < t) (hγ : γ ≠ 0) (hz : z ∈ ball 0 ρ)
    (hregular : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      VolumeGrowth (μ ω) ρ βm βp ∧
      ∀ s : ℝ, 0 < s → closure (cluster (μ ω) ρ z s) ⊆ ball 0 ρ →
        μ ω (frontier (cluster (μ ω) ρ z s)) = 0)
    (E : Set (Measure ℂ)) (hE : MeasurableSet E)
    (hrep : ∀ᵐ ω ∂P, ∀ c : ℝ,
      (ENNReal.ofReal (Real.exp (γ * c)) • (μ ω).restrict (ball 0 ρ) ∈ E) ↔
      (ENNReal.ofReal (Real.exp (γ * c)) • μ ω ∈
        confinedRegularizationDefect ρ t z))
    (hlaw : ∀ c : ℝ,
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * 0)) •
        (μ ω).restrict (ball 0 ρ)) P ≪
      Measure.map (fun ω => ENNReal.ofReal (Real.exp (γ * c)) •
        (μ ω).restrict (ball 0 ρ)) P) :
    ∀ᵐ ω ∂P, closure (cluster (μ ω) ρ z t) ⊆ ball 0 ρ →
      interior (closure (cluster (μ ω) ρ z t)) = cluster (μ ω) ρ z t := by
  have hopen : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → IsOpen (cluster (μ ω) ρ z s) := by
    filter_upwards [hregular] with ω ⟨βm, βp, hμ, hV, _⟩
    intro s hs
    exact (cluster_open_laplacian_of_general greenFunctionBall
      obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ hρ hV hz hs).1
  have hcompare : ∀ᵐ ω ∂P, ∀ s u : ℝ, 0 < s → s < u →
      closure (cluster (μ ω) ρ z u) ⊆ ball 0 ρ →
      interior (closure (cluster (μ ω) ρ z s)) ⊆ cluster (μ ω) ρ z u := by
    filter_upwards [hregular] with ω ⟨βm, βp, hμ, hV, hnull⟩
    intro s u hs hsu hc
    exact regularized_cluster_subset_later_cluster hμ hρ hV hz hnull hs hsu hc
  have hcount : ∀ᵐ ω ∂P, {c : ℝ |
      ENNReal.ofReal (Real.exp (γ * c)) • (μ ω).restrict (ball 0 ρ) ∈ E}.Countable := by
    filter_upwards [hopen, hcompare, hrep] with ω ho hc hr
    apply (countable_regularization_defect_shifts_of_comparison ht hγ ho hc).mono
    intro c h
    exact (hr c).mp h
  have hshift := measurable_restricted_exponential_mass_shift hμm ρ γ
  have hY : ∀ c : ℝ, AEMeasurable (fun ω =>
      ENNReal.ofReal (Real.exp (γ * c)) • (μ ω).restrict (ball 0 ρ)) P := by
    intro c
    exact (hshift.comp (measurable_id.prodMk measurable_const)).aemeasurable
  have hresult := ae_no_defect_of_shifted_law P
    (fun c ω => ENNReal.ofReal (Real.exp (γ * c)) • (μ ω).restrict (ball 0 ρ))
    E hE hY (hshift hE) hcount hlaw
  filter_upwards [hresult, hrep] with ω hω hr hc
  have heq := hr 0
  simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_smul] at heq hω
  by_contra hne
  exact hω (heq.mpr ⟨hc, hne⟩)

/-- The measurable-representative reduction also applies to an almost
surely measurable random measure. -/
theorem ae_no_regularization_defect_of_ae_measurable_representative
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμm : AEMeasurable μ P) {ρ t γ : ℝ} {z : ℂ}
    (hρ : 0 < ρ) (ht : 0 < t) (hγ : γ ≠ 0) (hz : z ∈ ball 0 ρ)
    (hregular : ∀ᵐ ω ∂P, ∃ βm βp : ℝ, IsLocallyFiniteMeasure (μ ω) ∧
      VolumeGrowth (μ ω) ρ βm βp ∧
      ∀ s : ℝ, 0 < s → closure (cluster (μ ω) ρ z s) ⊆ ball 0 ρ →
        μ ω (frontier (cluster (μ ω) ρ z s)) = 0)
    (E : Set (Measure ℂ)) (hE : MeasurableSet E)
    (hrep : ∀ᵐ ω ∂P, ∀ c : ℝ,
      (ENNReal.ofReal (Real.exp (γ * c)) • (μ ω).restrict (ball 0 ρ) ∈ E) ↔
      (ENNReal.ofReal (Real.exp (γ * c)) • μ ω ∈
        confinedRegularizationDefect ρ t z))
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
  have hrepν : ∀ᵐ ω ∂P, ∀ c : ℝ,
      (ENNReal.ofReal (Real.exp (γ * c)) • (ν ω).restrict (ball 0 ρ) ∈ E) ↔
      (ENNReal.ofReal (Real.exp (γ * c)) • ν ω ∈
        confinedRegularizationDefect ρ t z) := by
    filter_upwards [hrep, heq] with ω hω hν
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
  have hresult := ae_no_regularization_defect_of_measurable_representative
    P ν hνm hρ ht hγ hz hregν E hE hrepν hlawν
  filter_upwards [hresult, heq] with ω hω hν
  simpa only [hν] using hω

end MatedCRT
