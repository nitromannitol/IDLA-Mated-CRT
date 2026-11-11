import MatedCRT.FirstPass.LPBridge.ConeMeanZeroRestriction
import MatedCRT.LPStaging.Prob.GaussianShiftMoment
import MarkovProcess.Examples.BrownianMotion

/-!
# Absolute integrability of the radial pairings of a quantum cone

`ConeRadialAbsIntegrable` (input H5 of `ConeMeanZeroRestriction`): for a `γ`-quantum cone `(hC, hcirc)`
(`IsQuantumCone`, Definition 2.1) and a test function `φ` supported in the unit disc, the radial pairing
`∫ φ(x) h_{|x|}(0) dx` converges absolutely almost surely.

Route. Polar coordinates (`integrableOn_fun_norm_addHaar`) reduce the claim to `∫_{(0,1)} y |h_y(0)| dy < ∞`
almost surely. By Tonelli, its expectation is `∫_{(0,1)} y E|h_y(0)| dy`. The one-dimensional marginal of the
radial process `t ↦ h_{e^{-t}}(0)` is the law of `B_t + γ t` (`radial_law`), and
`E|B_t + c| ≤ (1 + t)/2 + |c|`, because `B_t` is centred Gaussian with variance `t`. For `y ∈ (0,1)` and
`t = -log y` one has `y · t ≤ 1`, so `y E|h_y(0)| ≤ 1 + |γ|`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped NNReal ENNReal

namespace MatedCRT.ConeMeanZeroRestriction

/-- Lebesgue measure on the open interval `(0,1)`, viewed as a measure on the subtype. -/
noncomputable abbrev ioo01 : Measure (Ioo (0 : ℝ) 1) := Measure.comap Subtype.val (volume : Measure ℝ)

lemma measurableSet_Ioo01 : MeasurableSet (Ioo (0 : ℝ) 1) := measurableSet_Ioo

instance ioo01_isFiniteMeasure : IsFiniteMeasure ioo01 := by
  refine ⟨?_⟩
  rw [ioo01, (MeasurableEmbedding.subtype_coe measurableSet_Ioo01).comap_apply,
    Subtype.coe_image_univ, Real.volume_Ioo]
  exact ENNReal.ofReal_lt_top

section Gaussian

/-- For `Z = N(0, t)` and `c ∈ ℝ`: `∫⁻ |x + c| dZ ≤ (1 + t)/2 + |c|`. -/
lemma lintegral_enorm_add_const_gaussianReal_le (t : ℝ≥0) (c : ℝ) :
    ∫⁻ x, ‖x + c‖ₑ ∂(gaussianReal 0 t) ≤ ENNReal.ofReal ((1 + (t : ℝ)) / 2 + |c|) :=
  LatticeProb.lintegral_enorm_add_const_gaussianReal_le t c

/-- For the standard Brownian motion `B` and `c ∈ ℝ`: `∫⁻ |B_t + c| dP ≤ (1 + t)/2 + |c|`. -/
lemma lintegral_enorm_brownian_add_le (c : ℝ) (t : ℝ≥0) :
    ∫⁻ w, ‖w t + c‖ₑ ∂(brownianMotion 0) ≤ ENNReal.ofReal ((1 + (t : ℝ)) / 2 + |c|) := by
  have hL : HasLaw (fun w : ContinuousPath ℝ => w t - 0) (gaussianReal 0 t) (brownianMotion 0) :=
    (isBrownianReal_brownianMotion 0).hasLaw_eval t
  have hf : Measurable fun x : ℝ => ‖x + c‖ₑ := by fun_prop
  calc ∫⁻ w, ‖w t + c‖ₑ ∂(brownianMotion 0)
      = ∫⁻ w, (fun x : ℝ => ‖x + c‖ₑ) (w t - 0) ∂(brownianMotion 0) := by simp
    _ = ∫⁻ x, ‖x + c‖ₑ ∂(gaussianReal 0 t) := hL.lintegral_comp hf.aemeasurable
    _ ≤ _ := lintegral_enorm_add_const_gaussianReal_le t c

end Gaussian

section Radial

variable {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- One-dimensional marginal of the radial process of a quantum cone (Definition 2.1, `radial_law`):
`E‖h_{e^{-t}}(0)‖ = E‖B_t + γ t‖` for the standard Brownian motion `B`. -/
lemma lintegral_enorm_circle_exp_eq (hQ : IsQuantumCone γ P hC hcirc) (t : ℝ≥0) :
    ∫⁻ ω, ‖hcirc ω (Real.exp (-(t : ℝ))) 0‖ₑ ∂P =
      ∫⁻ w, ‖w t + γ * t‖ₑ ∂(brownianMotion 0) := by
  obtain ⟨ν, ⟨hν, -⟩, hmap⟩ := hQ.radial_law
  have hmeas : Measurable fun ω => radialProcess (hcirc ω) := by
    unfold radialProcess
    exact Measurable.prodMk
      (Measurable.of_eval fun _ => hQ.measurable_circle _ _ (Real.exp_pos _))
      (Measurable.of_eval fun _ => hQ.measurable_circle _ _ (Real.exp_pos _))
  have hG : Measurable fun f : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => ‖f.1 t‖ₑ :=
    ((measurable_pi_apply t).comp measurable_fst).enorm
  have hg : Measurable fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s - γ * s :=
    Measurable.of_eval fun s =>
      (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) s).sub_const _
  have hΦ : Measurable fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s + γ * s :=
    Measurable.of_eval fun s =>
      (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) s).add_const _
  have hmass : (ν.map fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s - γ * s) Set.univ = 1 := by
    rw [Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ, measure_univ]
  calc ∫⁻ ω, ‖hcirc ω (Real.exp (-(t : ℝ))) 0‖ₑ ∂P
      = ∫⁻ f, ‖f.1 t‖ₑ ∂(P.map fun ω => radialProcess (hcirc ω)) :=
        (lintegral_map hG hmeas).symm
    _ = ∫⁻ f, ‖f.1 t‖ₑ ∂(quantumConeRadialLaw γ ν) := by rw [hmap]
    _ = ∫⁻ x, ‖x t‖ₑ ∂((brownianMotion 0).map fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s + γ * s) := by
        unfold quantumConeRadialLaw
        rw [lintegral_prod _ hG.aemeasurable]
        simp [lintegral_const, hmass]
    _ = ∫⁻ w, ‖w t + γ * t‖ₑ ∂(brownianMotion 0) := by
        rw [lintegral_map ((measurable_pi_apply t).enorm) hΦ]

/-- Pointwise bound on `(0,1)`: `y · E|h_y(0)| ≤ 1 + |γ|`, from `E|B_t + γ t| ≤ (1 + t)/2 + |γ| t` at
`t = -log y` and `y (-log y) ≤ 1`. -/
lemma ofReal_mul_lintegral_enorm_circle_le (hQ : IsQuantumCone γ P hC hcirc) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal y * ∫⁻ ω, ‖hcirc ω y 0‖ₑ ∂P ≤ ENNReal.ofReal (1 + |γ|) := by
  obtain ⟨hy0, hy1⟩ := hy
  set t : ℝ≥0 := Real.toNNReal (-Real.log y) with ht_def
  have hlog : Real.log y ≤ 0 := Real.log_nonpos hy0.le hy1.le
  have hL0 : (0 : ℝ) ≤ -Real.log y := by linarith
  have ht : (t : ℝ) = -Real.log y := Real.coe_toNNReal _ hL0
  have hexp : Real.exp (-(t : ℝ)) = y := by rw [ht, neg_neg, Real.exp_log hy0]
  have hylog : y * (-Real.log y) ≤ 1 := by
    have h1 := Real.one_sub_inv_le_log_of_pos hy0
    have h2 : y * (1 - y⁻¹) ≤ y * Real.log y := mul_le_mul_of_nonneg_left h1 hy0.le
    have h3 : y * (1 - y⁻¹) = y - 1 := by
      rw [mul_sub, mul_one, mul_inv_cancel₀ hy0.ne']
    nlinarith
  have habs : |γ * (t : ℝ)| = |γ| * (-Real.log y) := by
    rw [ht, abs_mul, abs_of_nonneg hL0]
  have key := lintegral_enorm_circle_exp_eq hQ t
  rw [hexp] at key
  rw [key]
  calc ENNReal.ofReal y * ∫⁻ w, ‖w t + γ * t‖ₑ ∂(brownianMotion 0)
      ≤ ENNReal.ofReal y * ENNReal.ofReal ((1 + (t : ℝ)) / 2 + |γ * t|) := by
        gcongr
        exact lintegral_enorm_brownian_add_le (γ * t) t
    _ = ENNReal.ofReal (y * ((1 + (t : ℝ)) / 2 + |γ * t|)) :=
        (ENNReal.ofReal_mul hy0.le).symm
    _ ≤ ENNReal.ofReal (1 + |γ|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [habs, ht]
        nlinarith [mul_le_mul_of_nonneg_left hylog (abs_nonneg γ), abs_nonneg γ, hy0, hy1]

end Radial

section Tonelli

variable {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Joint measurability of `(ω, y) ↦ 1_{Nᶜ}(ω) · y |h_y(0)|` on `Ω × (0,1)`: for each `ω` the map
`y ↦ 1_{Nᶜ}(ω) y |h_y(0)|` is continuous, and for each `y` it is measurable in `ω`; the Carathéodory
lemma `measurable_uncurry_of_continuous_of_measurable` gives joint measurability. -/
lemma measurable_radial_indicator (hQ : IsQuantumCone γ P hC hcirc) {N : Set Ω} (hN : MeasurableSet N)
    (hgood : ∀ ω ∉ N, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) :
    Measurable fun p : Ω × Ioo (0 : ℝ) 1 =>
      ENNReal.ofReal (Nᶜ.indicator (fun ω' => ((p.2 : ℝ)) * ‖hcirc ω' (p.2 : ℝ) 0‖) p.1) := by
  have hcont : ∀ ω : Ω, Continuous fun y : Ioo (0 : ℝ) 1 =>
      Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω := by
    intro ω
    by_cases hω : ω ∈ N
    · have hz : ∀ y : Ioo (0 : ℝ) 1,
          Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω = 0 :=
        fun y => Set.indicator_of_notMem (fun h : ω ∈ Nᶜ => h hω) _
      simp only [hz]
      exact continuous_const
    · have hz : ∀ y : Ioo (0 : ℝ) 1,
          Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω
            = (y : ℝ) * ‖hcirc ω (y : ℝ) 0‖ :=
        fun y => Set.indicator_of_mem (show ω ∈ Nᶜ from hω) _
      simp only [hz]
      have h2 : ContinuousOn (fun r : ℝ => hcirc ω r 0) (Ioi 0) :=
        (hgood ω hω).comp (f := fun r : ℝ => (r, (0 : ℂ))) (by fun_prop)
          (by intro r hr; exact ⟨hr, mem_univ _⟩)
      exact continuous_subtype_val.mul
        ((h2.norm).comp_continuous continuous_subtype_val fun y => y.2.1)
  have hmeas : ∀ y : Ioo (0 : ℝ) 1, Measurable fun ω : Ω =>
      Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω := by
    intro y
    exact (measurable_const.mul (hQ.measurable_circle _ _ y.2.1).norm).indicator hN.compl
  have hJ := measurable_uncurry_of_continuous_of_measurable
    (u := fun (y : Ioo (0 : ℝ) 1) (ω : Ω) =>
      Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω) hcont hmeas
  exact ENNReal.measurable_ofReal.comp (hJ.comp measurable_swap)

/-- Tonelli: the `P`-expectation of `∫_{(0,1)} y |h_y(0)| dy` (restricted to `Nᶜ`) is at most `1 + |γ|`. -/
lemma lintegral_radial_indicator_le [IsProbabilityMeasure P] (hQ : IsQuantumCone γ P hC hcirc)
    {N : Set Ω} (hN : MeasurableSet N)
    (hPN : P N = 0) (hgood : ∀ ω ∉ N, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ∫⁻ ω, ∫⁻ y : Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω) ∂ioo01 ∂P
      ≤ ENNReal.ofReal (1 + |γ|) := by
  have hJ := measurable_radial_indicator hQ hN hgood
  calc ∫⁻ ω, ∫⁻ y : Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω) ∂ioo01 ∂P
      = ∫⁻ y : Ioo (0 : ℝ) 1, ∫⁻ ω,
          ENNReal.ofReal (Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω) ∂P ∂ioo01 := by
        refine lintegral_lintegral_swap ?_
        exact hJ.aemeasurable
    _ ≤ ∫⁻ _ : Ioo (0 : ℝ) 1, ENNReal.ofReal (1 + |γ|) ∂ioo01 := by
        refine lintegral_mono fun y => ?_
        have hae : ∀ᵐ ω ∂P,
            ENNReal.ofReal (Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω)
              = ENNReal.ofReal (y : ℝ) * ‖hcirc ω (y : ℝ) 0‖ₑ := by
          filter_upwards [compl_mem_ae_iff.mpr hPN] with ω hω
          rw [Set.indicator_of_mem hω, ENNReal.ofReal_mul y.2.1.le, ofReal_norm]
        rw [lintegral_congr_ae hae, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ofReal_mul_lintegral_enorm_circle_le hQ y.2
    _ = ENNReal.ofReal (1 + |γ|) := by
        have h := lintegral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioo01
          (fun _ : ℝ => ENNReal.ofReal (1 + |γ|))
        simp only [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one] at h
        exact h

end Tonelli

section Main

variable {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Almost surely the circle average process is continuous on `(0,∞) × ℂ` and
`y ↦ y |h_y(0)|` is integrable on `(0,1)`. -/
lemma ae_radial_good [IsProbabilityMeasure P] (hQ : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      IntegrableOn (fun y : ℝ => y * ‖hcirc ω y 0‖) (Ioo 0 1) := by
  classical
  set bad : Set Ω := {ω | ¬ ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)}
    with hbad
  have hP : P bad = 0 := ae_iff.mp hQ.ae_continuousOn_circle
  set N : Set Ω := toMeasurable P bad with hNdef
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hPN : P N = 0 := by rw [hNdef, measure_toMeasurable]; exact hP
  have hgood : ∀ ω ∉ N, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P bad h)
  have hfin : ∫⁻ ω, ∫⁻ y : Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω) ∂ioo01 ∂P ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_radial_indicator_le hQ hN hPN hgood)
  have hmeasI := (measurable_radial_indicator hQ hN hgood).lintegral_prod_right' (ν := ioo01)
  filter_upwards [ae_lt_top hmeasI hfin, compl_mem_ae_iff.mpr hPN] with ω hωlt hωN
  refine ⟨hgood ω hωN, ?_⟩
  have hcontR : ContinuousOn (fun y : ℝ => y * ‖hcirc ω y 0‖) (Ioi 0) := by
    have h2 : ContinuousOn (fun r : ℝ => hcirc ω r 0) (Ioi 0) :=
      (hgood ω hωN).comp (f := fun r : ℝ => (r, (0 : ℂ))) (by fun_prop)
        (by intro r hr; exact ⟨hr, mem_univ _⟩)
    exact continuousOn_id.mul h2.norm
  have hωeq : ∫⁻ y : Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Nᶜ.indicator (fun ω' => ((y : ℝ)) * ‖hcirc ω' (y : ℝ) 0‖) ω) ∂ioo01
      = ∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (y * ‖hcirc ω y 0‖) := by
    rw [← lintegral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Ioo01
      (fun y : ℝ => ENNReal.ofReal (y * ‖hcirc ω y 0‖))]
    refine lintegral_congr fun y => ?_
    rw [Set.indicator_of_mem hωN]
  have hωlt' : ∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (y * ‖hcirc ω y 0‖) < ∞ := by
    rw [← hωeq]
    exact hωlt
  refine ⟨(hcontR.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo01, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal ?_).mpr hωlt'
  exact (ae_restrict_mem measurableSet_Ioo01).mono fun y hy => mul_nonneg hy.1.le (norm_nonneg _)

end Main

/-- **H5.** For a `γ`-quantum cone and a test function `φ` supported in the unit disc, the radial pairing
`∫ φ(x) h_{|x|}(0) dx` converges absolutely almost surely (`ConeRadialAbsIntegrable`). -/
theorem coneRadialAbsIntegrable_holds : ConeRadialAbsIntegrable := by
  unfold ConeRadialAbsIntegrable
  intro γ Ω _ P hC hcirc _ hQ φ hφ
  filter_upwards [ae_radial_good hQ] with ω hω
  obtain ⟨hcont, hint⟩ := hω
  obtain ⟨C, hC'⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  have hcontC : ContinuousOn (fun x : ℂ => hcirc ω ‖x‖ 0) {0}ᶜ :=
    hcont.comp (f := fun x : ℂ => (‖x‖, (0 : ℂ)))
      (continuous_norm.prodMk continuous_const).continuousOn
      (by intro x hx; exact ⟨norm_pos_iff.mpr hx, mem_univ _⟩)
  have hae : AEStronglyMeasurable (fun x : ℂ => hcirc ω ‖x‖ 0) volume := by
    have h1 := hcontC.aestronglyMeasurable (μ := volume) isClosed_singleton.isOpen_compl.measurableSet
    have hae0 : ∀ᵐ x ∂(volume : Measure ℂ), x ∈ ({0} : Set ℂ)ᶜ :=
      compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))
    rwa [Measure.restrict_eq_self_of_ae_mem hae0] at h1
  have hmeasφ : AEStronglyMeasurable (fun x : ℂ => φ x * hcirc ω ‖x‖ 0) volume :=
    hφ.1.continuous.aestronglyMeasurable.mul hae
  have hball : IntegrableOn (fun x : ℂ => ‖hcirc ω ‖x‖ 0‖) (ball (0 : ℂ) 1) := by
    refine (integrableOn_fun_norm_addHaar (μ := (volume : Measure ℂ)) (f := fun r : ℝ => ‖hcirc ω r 0‖)
      (r := 1)).mpr ?_
    simpa [Complex.finrank_real_complex] using hint
  have hint2 : Integrable (fun x : ℂ => C * (ball (0 : ℂ) 1).indicator (fun x => ‖hcirc ω ‖x‖ 0‖) x)
      volume :=
    ((integrable_indicator_iff measurableSet_ball).mpr hball).const_mul C
  refine hint2.mono' hmeasφ ?_
  refine Filter.Eventually.of_forall fun x => ?_
  by_cases hx : x ∈ ball (0 : ℂ) 1
  · rw [Set.indicator_of_mem hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC' x) (norm_nonneg _)
  · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)
    rw [Set.indicator_of_notMem hx, hφx]
    simp

end MatedCRT.ConeMeanZeroRestriction
