import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.Final
import MatedCRT.Proofs.Measurability.LQGMeasureField
import MatedCRT.Proofs.Measurability.EnvSigmaCore
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.Approx
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-!
# Lemma 3.4: measurability of the Green integral in the environment

This file proves `lbmGreenIntegralMeasurableStep_holds : LBMGreenIntegralMeasurableStep 𝒮`, the step
`hUmStep` of `integralConvergenceGreenFunction_of_steps`. For a test function `f ω` that is Hölder on the
ball `B = ball z r`, measurable in the environment for `σ(h, η)` and bounded, the map
`ω ↦ ∫_B G_B(y, x) f ω x μ_h(dx)` is `σ(h, η)`-measurable, hence almost surely measurable.

Route (all inputs are proved Lean statements; no new mathematics):
* `lqgMeasureFieldMeasurableStep`: `μ_h` agrees almost surely with a `σ(h)`-measurable random measure `μ'`;
* `ae_isLocallyFiniteMeasure`: `μ_h` is almost surely locally finite, so `μ_h(B) < ∞` almost surely;
* Carathéodory joint measurability (`measurable_uncurry_of_continuous_of_measurable`) on the subtype `B`:
  `f ω` is continuous on `B` and `f · x` is measurable;
* the normalized kernel `ω ↦ (1 + μ'_ω(B))⁻¹ • (μ'_ω|_B)` is a finite kernel, so the Bochner integral against
  it is measurable (`StronglyMeasurable.integral_kernel_prod_right'`); undoing the normalization gives the
  integral over `B`, and `measurable_greenFunction` gives measurability of the Green function `G_B(y, ·)`.

Terminology: LQG measure `μ_h` (Duplantier–Sheffield); Green function `G_B` of the ball (Armitage–Gardiner).
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Carathéodory joint measurability on a ball: a family `a ↦ f a` of functions on `ℂ`, measurable in `a` at
each point and continuous on the ball, is jointly measurable on `α × B` with `B` the ball as a subtype. -/
theorem lbmGreen_uncurry_ball {α : Type} [MeasurableSpace α] (z : ℂ) (r : ℝ) (f : α → ℂ → ℝ)
    (hm : ∀ x : ℂ, Measurable fun a => f a x) (hc : ∀ a, ContinuousOn (f a) (ball z r)) :
    Measurable fun p : α × ball z r => f p.1 (p.2 : ℂ) := by
  have hu : Measurable (Function.uncurry fun (i : ball z r) (a : α) => f a (i : ℂ)) :=
    measurable_uncurry_of_continuous_of_measurable (fun a => (hc a).domRestrict) (fun i => hm (i : ℂ))
  exact hu.comp measurable_swap

/-- Measurability of a Bochner integral over the ball against a measurable family of measures `ν a`, with
`ν a (ball z r) < ∞` for every `a`, for an integrand jointly measurable on `α × B`. The proof integrates against
the normalized kernel `(1 + ν a B)⁻¹ • (ν a)|_B`, which is a finite kernel (bound `1`). -/
theorem lbmGreen_integral_ball {α : Type} [MeasurableSpace α] (z : ℂ) (r : ℝ) (ν : α → Measure ℂ)
    (hν : Measurable ν) (hfin : ∀ a, ν a (ball z r) ≠ ⊤) (g : α → ℂ → ℝ)
    (hg : Measurable fun p : α × ball z r => g p.1 (p.2 : ℂ)) :
    Measurable fun a => ∫ x in ball z r, g a x ∂(ν a) := by
  have hB : MeasurableSet (ball z r) := measurableSet_ball
  have hνB : Measurable fun a => ν a (ball z r) := (Measure.measurable_coe hB).comp hν
  have hcomap : ∀ (a : α) (A : Set (ball z r)), (ν a).comap Subtype.val A = ν a (Subtype.val '' A) :=
    fun a A => (MeasurableEmbedding.subtype_coe hB).comap_apply (ν a) A
  set c : α → ℝ≥0∞ := fun a => (1 + ν a (ball z r))⁻¹ with hc_def
  set κ : α → Measure (ball z r) := fun a => c a • (ν a).comap Subtype.val with hκ_def
  have hκm : Measurable κ := by
    refine Measure.measurable_of_measurable_coe κ fun A hA => ?_
    have h1 : Measurable fun a => ν a (Subtype.val '' A) :=
      (Measure.measurable_coe (MeasurableSet.subtype_image hB hA)).comp hν
    have h2 : Measurable c := (measurable_const.add hνB).inv
    have hfun : (fun a => κ a A) = fun a => c a * ν a (Subtype.val '' A) := by
      funext a
      simp only [hκ_def, Measure.smul_apply, smul_eq_mul, hcomap]
    rw [hfun]
    exact h2.mul h1
  let K : ProbabilityTheory.Kernel α (ball z r) := ⟨κ, hκm⟩
  have hbound : ∀ a, K a Set.univ ≤ 1 := by
    intro a
    have hx : ν a (ball z r) ≠ ⊤ := hfin a
    show (c a • (ν a).comap Subtype.val) Set.univ ≤ 1
    rw [Measure.smul_apply, smul_eq_mul, hcomap a Set.univ, Subtype.coe_image_univ]
    calc c a * ν a (ball z r) ≤ c a * (1 + ν a (ball z r)) :=
          mul_le_mul_of_nonneg_left le_add_self zero_le
      _ = 1 := by
        show (1 + ν a (ball z r))⁻¹ * (1 + ν a (ball z r)) = 1
        exact ENNReal.inv_mul_cancel (by simp) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hx⟩)
  have : ProbabilityTheory.IsFiniteKernel K := ⟨⟨1, ENNReal.one_lt_top, hbound⟩⟩
  have hid : ∀ a, ∫ x in ball z r, g a x ∂(ν a)
      = (1 + (ν a (ball z r)).toReal) * ∫ x : ball z r, g a (x : ℂ) ∂(K a) := by
    intro a
    have hx : ν a (ball z r) ≠ ⊤ := hfin a
    have hcr : (c a).toReal * (1 + (ν a (ball z r)).toReal) = 1 := by
      show ((1 + ν a (ball z r))⁻¹).toReal * (1 + (ν a (ball z r)).toReal) = 1
      rw [ENNReal.toReal_inv, ENNReal.toReal_add ENNReal.one_ne_top hx, ENNReal.toReal_one]
      have h0 : (0 : ℝ) ≤ (ν a (ball z r)).toReal := ENNReal.toReal_nonneg
      exact inv_mul_cancel₀ (ne_of_gt (by linarith))
    have hK : ∫ x : ball z r, g a (x : ℂ) ∂(K a)
        = (c a).toReal * ∫ x in ball z r, g a x ∂(ν a) := by
      show ∫ x : ball z r, g a (x : ℂ) ∂(c a • (ν a).comap Subtype.val) = _
      rw [integral_smul_measure, smul_eq_mul, integral_subtype_comap hB (g a)]
    rw [hK]
    linear_combination (-(∫ x in ball z r, g a x ∂(ν a))) * hcr
  have hmeasK : Measurable fun a => ∫ x : ball z r, g a (x : ℂ) ∂(K a) := by
    have hF : StronglyMeasurable (fun p : α × ball z r => g p.1 (p.2 : ℂ)) := hg.stronglyMeasurable
    exact (hF.integral_kernel_prod_right' (κ := K)).measurable
  have hmul : Measurable fun a => 1 + (ν a (ball z r)).toReal :=
    measurable_const.add hνB.ennreal_toReal
  have heq : (fun a => ∫ x in ball z r, g a x ∂(ν a))
      = fun a => (1 + (ν a (ball z r)).toReal) * ∫ x : ball z r, g a (x : ℂ) ∂(K a) :=
    funext hid
  rw [heq]
  exact hmul.mul hmeasK

/-- The Green integral over a ball, for a Hölder family of test functions measurable in the environment, is
measurable in the environment. -/
theorem lbmGreen_measurable_integral {α : Type} [MeasurableSpace α] (z y : ℂ) (r : ℝ) (f : α → ℂ → ℝ)
    (ν : α → Measure ℂ) (hν : Measurable ν) (hfin : ∀ a, ν a (ball z r) ≠ ⊤)
    (hm : ∀ x : ℂ, Measurable fun a => f a x) (hc : ∀ a, ContinuousOn (f a) (ball z r)) :
    Measurable fun a => ∫ x in ball z r, greenFunction (ball z r) y x * f a x ∂(ν a) := by
  have hG : Measurable fun p : α × ball z r => greenFunction (ball z r) y (p.2 : ℂ) :=
    (measurable_greenFunction isOpen_ball y).comp (measurable_subtype_coe.comp measurable_snd)
  have hg : Measurable fun p : α × ball z r => greenFunction (ball z r) y (p.2 : ℂ) * f p.1 (p.2 : ℂ) :=
    hG.mul (lbmGreen_uncurry_ball z r f hm hc)
  exact lbmGreen_integral_ball z r ν hν hfin (fun a x => greenFunction (ball z r) y x * f a x) hg

/-- **Measurability of the Green integral in the environment** (the step `LBMGreenIntegralMeasurableStep`, the
hypothesis `hUmStep` of `integralConvergenceGreenFunction_of_steps`), proved from the Lean statements
`lqgMeasureFieldMeasurableStep` (the LQG measure is a.s. a `σ(h)`-measurable random measure) and
`ae_isLocallyFiniteMeasure` (the LQG measure is a.s. locally finite). -/
theorem lbmGreenIntegralMeasurableStep_holds (𝒮 : SpaceFillingSLEModel) :
    LBMGreenIntegralMeasurableStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hball hy f hfmeas hfbound hfcont
  obtain ⟨μ', hμ'm, hμ'eq⟩ := MatedCRT.LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮 γ hγ hγ2 Ω S hS
  have hloc : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) :=
    MatedCRT.LQGMeasure.ae_isLocallyFiniteMeasure hS.isConeField
  have hμ'e : Measurable[S.envSigma] μ' := hμ'm.mono le_sup_left le_rfl
  have hball_m : Measurable[S.envSigma] fun ω => μ' ω (ball z r) :=
    (Measure.measurable_coe measurableSet_ball).comp hμ'e
  obtain ⟨ν, hνdef⟩ : ∃ ν : Ω → Measure ℂ, ∀ ω, ν ω = if μ' ω (ball z r) = ⊤ then 0 else μ' ω :=
    ⟨fun ω => if μ' ω (ball z r) = ⊤ then 0 else μ' ω, fun ω => rfl⟩
  have hνm : Measurable[S.envSigma] ν := by
    have hfun : ν = fun ω => if μ' ω (ball z r) = ⊤ then 0 else μ' ω := funext hνdef
    rw [hfun]
    exact Measurable.ite (hball_m (measurableSet_singleton ⊤)) measurable_const hμ'e
  have hνfin : ∀ ω, ν ω (ball z r) ≠ ⊤ := by
    intro ω
    rw [hνdef ω]
    split_ifs with h
    · simp
    · exact h
  have hcont : ∀ ω, ContinuousOn (f ω) (ball z r) := fun ω => by
    obtain ⟨C, χ, hχ, _, hH⟩ := hfcont ω
    exact hH.continuousOn hχ
  have hmeasI : @Measurable Ω ℝ S.envSigma _ fun ω =>
      ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂(ν ω) :=
    @lbmGreen_measurable_integral Ω S.envSigma z y r f ν hνm hνfin hfmeas hcont
  have hfinal : AEMeasurable (fun ω => S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂(ν ω))
      S.P :=
    MatedCRTEnv.IsValid.aemeasurable_of_envSigma hS (hmeasI.const_mul S.c₀)
  have hae : ∀ᵐ ω ∂S.P, ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂(S.μ ω)
      = ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂(ν ω) := by
    filter_upwards [hμ'eq, hloc] with ω hω hlocω
    have := hlocω
    have hfin : μ' ω (ball z r) ≠ ⊤ := by
      rw [hω]
      exact (measure_ball_lt_top).ne
    rw [hνdef ω]
    simp only [hfin, ↓reduceIte]
    rw [hω]
  exact hfinal.congr (by filter_upwards [hae] with ω hω; rw [hω])

end MatedCRT
