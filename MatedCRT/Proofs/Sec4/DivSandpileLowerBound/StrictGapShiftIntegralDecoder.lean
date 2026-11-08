import HarmonicBalls.Proofs.Sec11.AbsoluteLQGMassShiftDecoder
import HarmonicBalls.Proofs.Sec5.LQGIntegralLaw
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-! # Compactly supported LQG integrals under pinned shifts -/

noncomputable section

open MeasureTheory Filter Set Metric HarmonicBalls ProbabilityTheory
open scoped Topology ENNReal

namespace MatedCRT

/-- Compactly supported integrals of the shifted LQG measure are measurable
    functions of the global field modulo constants, uniformly over continuous
    shifts preserving the unit-circle normalization. -/
theorem exists_global_shifted_lqgIntegral_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (A : Set ℂ) (hA : MeasurableSet A)
    (hbuffer : ∀ n z, z ∈ A → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hsupp : Function.support f ⊆ A) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℝ≥0∞, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g → Real.circleAverage g 0 1 = 0 →
        F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ ω) =
          ENNReal.ofReal (∫ z, f z ∂((μ ω).withDensity
            (fun z => ENNReal.ofReal (Real.exp (γ * g z))))) := by
  obtain ⟨D, hDm, hDeq⟩ := hGFF.exists_global_joint_absolute_circle_shift_decoders
    (α := α) (ε := ε) dyadicScale dyadicScale_pos
  let M : ℕ → (LocalZeroMeanTest univ → ℝ) → Measure ℂ := fun n v =>
    (volume.restrict A).withDensity fun z => ENNReal.ofReal
      ((dyadicScale n) ^ (γ ^ 2 / 2) * Real.exp (γ * D n v z))
  have hM (n : ℕ) : Measurable (M n) := by
    apply measurable_withDensity
    exact (measurable_const.mul ((measurable_const.mul (hDm n)).exp)).ennreal_ofReal
  let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
  have hI : Measurable (fun m : Measure ℂ => ∫ z, f z ∂m) :=
    (hf.stronglyMeasurable.integral_kernel (κ := K)).measurable
  let F : (LocalZeroMeanTest univ → ℝ) → ℝ≥0∞ := fun v =>
    liminf (fun n => ENNReal.ofReal (∫ z, f z ∂(M n v))) atTop
  refine ⟨F, Measurable.liminf (fun n => (hI.comp (hM n)).ennreal_ofReal), ?_⟩
  have hc := ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α (dyadicScale_pos n)
  filter_upwards [hμ, hc, hDeq] with ω hω hcω heqω g hg hpin
  have hshift := Section6.isLQGLimit_addCircleAverage hω hcω g hg
  let ρ : ℕ → Measure ℂ := fun n => lqgApprox γ
    (addCircleAverage (fieldCircleAverage α (hcirc ω)) g) (dyadicScale n)
  have hrestrict (n : ℕ) : M n (localModConstPairings α
      (fun ω => addFunPairing (hC ω) g) univ ω) = (ρ n).restrict A := by
    dsimp [M, ρ, lqgApprox]
    rw [restrict_withDensity hA]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hA] with z hz
    rw [heqω n g hg hpin z (hbuffer n z hz)]
    rfl
  have hind : A.indicator f = f := by
    funext z
    by_cases hz : z ∈ A
    · simp [hz]
    · have hzero : f z = 0 := by
        by_contra h
        exact hz (hsupp h)
      simp [hz, hzero]
  have hIeq (n : ℕ) : (∫ z, f z ∂((ρ n).restrict A)) = ∫ z, f z ∂(ρ n) := by
    rw [← integral_indicator hA, hind]
  apply Tendsto.liminf_eq
  apply (ENNReal.continuous_ofReal.tendsto _).comp
  convert hshift.tendsto_integral f hf hfc using 1
  funext n
  rw [hrestrict, hIeq]

/-- Open-set mass is the supremum of integrals of compactly supported
    continuous functions whose support lies in the open set. -/
theorem exists_open_mass_supported_test_functions {U : Set ℂ} (hU : IsOpen U) :
    ∃ f : ℕ → ℂ → ℝ,
      (∀ n, Continuous (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      (∀ n, Function.support (f n) ⊆ U) ∧
      ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ →
        μ U = ⨆ n, ENNReal.ofReal (∫ z, f n z ∂μ) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : CompactExhaustion U := CompactExhaustion.choice U
  let C : ℕ → Set ℂ := fun n => Subtype.val '' K n
  have hC (n : ℕ) : IsCompact (C n) := (K.isCompact n).image continuous_subtype_val
  have hCU (n : ℕ) : C n ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    exact x.property
  have hmono : Monotone C := fun i j hij => image_mono (K.subset hij)
  have hcover : (⋃ n, C n) = U := by
    rw [← image_iUnion, K.iUnion_eq, image_univ]
    exact Subtype.range_coe
  have hcut (n : ℕ) : ∃ g : C(ℂ, ℝ), EqOn g 1 (C n) ∧ EqOn g 0 Uᶜ ∧
      HasCompactSupport g ∧ ∀ z, g z ∈ Icc (0 : ℝ) 1 :=
    exists_continuous_one_zero_of_isCompact (hC n) hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hCU n))
  choose g hgOne hgZero hgComp hgRange using hcut
  refine ⟨fun n => g n, fun n => (g n).continuous, hgComp, ?_, ?_⟩
  · intro n z hz
    by_contra hzU
    exact hz (hgZero n hzU)
  · intro μ hμ
    let _ := hμ
    apply le_antisymm
    · rw [← hcover, hmono.measure_iUnion]
      apply iSup_le
      intro n
      apply le_iSup_of_le n
      apply ((g n).continuous.integrable_of_hasCompactSupport (hgComp n)).measure_le_integral
      · exact Filter.Eventually.of_forall fun z => (hgRange n z).1
      · intro z hz
        simpa using le_of_eq (hgOne n hz).symm
    · apply iSup_le
      intro n
      apply integral_le_measure
      · intro z hz
        exact (hgRange n z).2
      · intro z hz
        exact le_of_eq (hgZero n hz)

/-- A buffered open-set mass is decoded from the global field for all
    continuous shifts preserving the circle normalization. -/
theorem exists_global_shifted_lqgOpenMass_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (A U : Set ℂ) (hA : IsOpen A) (hU : IsOpen U)
    (hbuffer : ∀ n z, z ∈ A → closedBall z (dyadicScale n) ⊆ ball 0 ε) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℝ≥0∞, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g → Real.circleAverage g 0 1 = 0 →
        F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ ω) =
          ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (U ∩ A) := by
  obtain ⟨f, hf, hfc, hfsupp, hmass⟩ := exists_open_mass_supported_test_functions (hU.inter hA)
  choose F hFm hFe using fun n => exists_global_shifted_lqgIntegral_decoder hGFF hμ A
    hA.measurableSet hbuffer (f n) (hf n) (hfc n) ((hfsupp n).trans inter_subset_right)
  refine ⟨fun v => ⨆ n, F n v, Measurable.iSup hFm, ?_⟩
  have hc := ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α (dyadicScale_pos n)
  filter_upwards [hμ, hc, ae_all_iff.mpr hFe] with ω hω hcω hFeω g hg hpin
  have hshift := Section6.isLQGLimit_addCircleAverage hω hcω g hg
  rw [hmass _ hshift.isLocallyFiniteMeasure]
  congr 1
  funext n
  exact hFeω n g hg hpin

end MatedCRT
