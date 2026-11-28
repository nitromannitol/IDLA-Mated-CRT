import Mathlib
import MatedCRT.FirstPass.Derived.GFFLocalRegularity.NewtonGradient

/-!
# Green's representation formula in `L^q`, and integrals of `L²`-valued families

Both statements below are instances of one fact: if `x ↦ F x` is a Bochner-integrable family in `L^p(m)`
(`m` a finite measure, `1 ≤ p < ∞`) and `F x = φ x` almost everywhere with `φ` jointly measurable, then the
`L^p(m)`-valued integral `∫ F x dx` is, almost everywhere, the pointwise integral `a ↦ ∫ φ x a dx`
(`coeFn_integral_ae_eq_integral_apply`).

## Sources of the standard facts used

* Fubini's theorem (`MeasureTheory.integral_integral_swap`, `MeasureTheory.integrable_prod_iff`) to
  interchange the integrals over a product of two σ-finite measure spaces.
* Hille's theorem, the commutation of a Bochner integral with a bounded linear map
  (`ContinuousLinearMap.integral_comp_comm`), applied to the bounded linear functional `f ↦ ∫_S f dm` on
  `L^p(m)`.
* Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, (2.17), the compactly
  supported form of Green's representation formula (2.16), in the form
  `MatedCRT.GFFLocalRegularity.eq_sum_integral_newtonGrad`.

## Main results

* `MatedCRT.GFFLocalRegularity.sum_integral_smul_newtonGrad_toLp`: for compactly supported smooth `v`,
  `∑ i, ∫ ∂_i v(x) • newtonGrad i x dx = v` in `L^q` of a ball, `1 < q < 2`.
* `MatedCRT.GFFLocalRegularity.coeFn_integral_smul_ae_eq`: for a continuous family `u` and a continuous
  linear map `T` into `L²(P)`, the `L²(P)`-valued integral `∫ g(x) T(u x) dx` is almost surely the
  pathwise integral `∫ g(x) Y_x dx` of any jointly measurable version `Y` of `x ↦ T (u x)`.
-/

namespace MatedCRT.GFFLocalRegularity

open MeasureTheory Metric Set
open scoped NNReal ENNReal

section Generic

variable {α : Type*} [MeasurableSpace α] {m : Measure α} [IsFiniteMeasure m]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On a finite measure space, `∫ |f| ≤ C ‖f‖_{L^p}` for `1 ≤ p < ∞` (Hölder). -/
theorem integral_norm_le_const_mul_norm_Lp (hp : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℝ p m, ∫ a, ‖f a‖ ∂m ≤ C * ‖f‖ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp1' : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hp hp1
  have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
    have h : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1'
    simp only [ENNReal.toReal_one, div_one]
    linarith
  refine ⟨(m Set.univ).toReal ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal), by positivity, fun f => ?_⟩
  have hfi : Integrable f m := (Lp.memLp f).integrable hp1
  have h1 : ENNReal.ofReal (∫ a, ‖f a‖ ∂m) = eLpNorm f 1 m := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hfi, eLpNorm_one_eq_lintegral_enorm]
    exact hfi.aestronglyMeasurable
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 (Lp.memLp f).aestronglyMeasurable
  have hfin : eLpNorm f p m ≠ ⊤ := Lp.eLpNorm_ne_top f
  have hmfin : m Set.univ ≠ ⊤ := measure_ne_top _ _
  calc ∫ a, ‖f a‖ ∂m = (eLpNorm f 1 m).toReal := by
        rw [← h1, ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
    _ ≤ (eLpNorm f p m * m Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hfin (ENNReal.rpow_ne_top_of_nonneg hexp hmfin)) h2
    _ = (m Set.univ).toReal ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) * ‖f‖ := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Lp.norm_def, mul_comm]

/-- On a finite measure space, `f ↦ ∫_S f` is a continuous linear functional on `L^p`, `1 ≤ p < ∞`. -/
theorem exists_continuousLinearMap_setIntegral_Lp (hp : p ≠ ⊤) (S : Set α) :
    ∃ Λ : Lp ℝ p m →L[ℝ] ℝ, ∀ f : Lp ℝ p m, Λ f = ∫ a in S, f a ∂m := by
  obtain ⟨C, -, hC⟩ := integral_norm_le_const_mul_norm_Lp (m := m) hp
  have hint : ∀ f : Lp ℝ p m, Integrable f m := fun f => (Lp.memLp f).integrable Fact.out
  let L : Lp ℝ p m →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ a in S, f a ∂m
      map_add' := fun f g => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))]
        exact integral_add (hint f).integrableOn (hint g).integrableOn
      map_smul' := fun c f => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))]
        exact integral_smul (μ := m.restrict S) c (fun a => f a) }
  refine ⟨L.mkContinuous (max C 0) (fun f => ?_), fun f => rfl⟩
  show ‖∫ a in S, f a ∂m‖ ≤ max C 0 * ‖f‖
  calc ‖∫ a in S, f a ∂m‖ ≤ ∫ a in S, ‖f a‖ ∂m := norm_integral_le_integral_norm _
    _ ≤ ∫ a, ‖f a‖ ∂m :=
        setIntegral_le_integral (hint f).norm (ae_of_all _ fun _ => norm_nonneg _)
    _ ≤ C * ‖f‖ := hC f
    _ ≤ max C 0 * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- **Pointwise representative of an `L^p`-valued integral.** If `F : X → L^p(m)` is Bochner integrable,
`F x = φ x` almost everywhere for each `x`, and `(x, a) ↦ φ x a` is jointly measurable, then the
`L^p(m)`-valued integral `∫ F x dν` is almost everywhere `a ↦ ∫ φ x a dν`. -/
theorem coeFn_integral_ae_eq_integral_apply {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [SFinite ν] (hp : p ≠ ⊤) (F : X → Lp ℝ p m) (hF : Integrable F ν) (φ : X → α → ℝ)
    (hφ : ∀ x, F x =ᵐ[m] φ x) (hmeas : AEStronglyMeasurable (Function.uncurry φ) (ν.prod m)) :
    ((∫ x, F x ∂ν : Lp ℝ p m) : α → ℝ) =ᵐ[m] fun a => ∫ x, φ x a ∂ν := by
  obtain ⟨C, -, hC⟩ := integral_norm_le_const_mul_norm_Lp (m := m) hp
  have hint : Integrable (Function.uncurry φ) (ν.prod m) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨ae_of_all _ fun x => ?_, ?_⟩
    · exact ((Lp.memLp (F x)).integrable Fact.out).congr (hφ x)
    · refine Integrable.mono' (hF.norm.const_mul C) hmeas.norm.integral_prod_right'
        (ae_of_all _ fun x => ?_)
      simp only [Function.uncurry_apply_pair]
      have e : ∫ a, ‖φ x a‖ ∂m = ∫ a, ‖F x a‖ ∂m :=
        integral_congr_ae ((hφ x).symm.mono fun a ha => by simp only [ha])
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e]
      exact hC (F x)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s _ _
    exact ((Lp.memLp _).integrable Fact.out).integrableOn
  · intro s _ _
    exact hint.integral_prod_right.integrableOn
  · intro s hs _
    obtain ⟨Λ, hΛ⟩ := exists_continuousLinearMap_setIntegral_Lp (m := m) hp s
    have hprod : Integrable (Function.uncurry φ) (ν.prod (m.restrict s)) := by
      have : ν.prod (m.restrict s) = (ν.prod m).restrict (univ ×ˢ s) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [this]
      exact hint.restrict
    calc ∫ a in s, (∫ x, F x ∂ν) a ∂m = Λ (∫ x, F x ∂ν) := (hΛ _).symm
      _ = ∫ x, Λ (F x) ∂ν := (ContinuousLinearMap.integral_comp_comm Λ hF).symm
      _ = ∫ x, ∫ a in s, φ x a ∂m ∂ν := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          dsimp only
          rw [hΛ]
          exact integral_congr_ae (ae_restrict_of_ae (hφ x))
      _ = ∫ a in s, ∫ x, φ x a ∂ν ∂m := integral_integral_swap hprod

end Generic

/-- **Integrals of `L²`-valued families.** Let `T` be a continuous linear map into `L²(P)`, `u : ℂ → E`
continuous, and `Y x` a measurable version of `T (u x)` that is continuous in `x` for every `ω`. For
`g` continuous with compact support, the `L²(P)`-valued integral `∫ g(x) T(u x) dx` is almost surely
`ω ↦ ∫ g(x) Y x ω dx`. -/
theorem coeFn_integral_smul_ae_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (T : E →L[ℝ] Lp ℝ 2 P) {u : ℂ → E} (hu : Continuous u) {Y : ℂ → Ω → ℝ}
    (hYm : ∀ x, Measurable (Y x)) (hY : ∀ x, Y x =ᵐ[P] ⇑(T (u x)))
    (hYc : ∀ ω, Continuous fun x => Y x ω) {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ((∫ x, g x • T (u x) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun ω => ∫ x, g x * Y x ω := by
  have hcont : Continuous fun x => g x • T (u x) := hg.smul (T.continuous.comp hu)
  have hcs : HasCompactSupport fun x => g x • T (u x) :=
    HasCompactSupport.intro hgc.isCompact fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  refine coeFn_integral_ae_eq_integral_apply (p := 2) (by simp) (fun x => g x • T (u x))
    (hcont.integrable_of_hasCompactSupport hcs) (fun x ω => g x * Y x ω) (fun x => ?_) ?_
  · filter_upwards [Lp.coeFn_smul (g x) (T (u x)), hY x] with ω h1 h2
    rw [h1, Pi.smul_apply, ← h2, smul_eq_mul]
  · have hY' : Measurable (Function.uncurry Y) := measurable_uncurry_of_continuous_of_measurable hYc hYm
    exact ((hg.measurable.comp measurable_fst).mul hY').aestronglyMeasurable

/-- The kernel `y ↦ newtonGrad i x y` as an element of `L^q(B(c, r))`. -/
noncomputable def newtonGradLp {q : ℝ≥0} {c : ℂ} {r : ℝ} (hq1 : 1 < q) (hq2 : q < 2) (i : Fin 2)
    (x : ℂ) : Lp ℝ q (volume.restrict (ball c r)) :=
  (memLp_newtonGrad (c := c) (r := r) hq1 hq2 i x).toLp (fun y => newtonGrad i x y)

/-- For `g` continuous with compact support, `x ↦ g x • newtonGradLp i x` is Bochner integrable in
`L^q(B(c, r))`, since it is continuous (`continuous_newtonGrad_toLp`) with compact support. -/
theorem integrable_smul_newtonGradLp {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))] (hq1 : 1 < q) (hq2 : q < 2)
    (i : Fin 2) {c : ℂ} {r : ℝ} {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => g x • newtonGradLp (c := c) (r := r) hq1 hq2 i x) (volume : Measure ℂ) := by
  have hcont : Continuous fun x => g x • newtonGradLp (c := c) (r := r) hq1 hq2 i x :=
    hg.smul (continuous_newtonGrad_toLp hq1 hq2 i c r)
  have hcs : HasCompactSupport fun x => g x • newtonGradLp (c := c) (r := r) hq1 hq2 i x :=
    HasCompactSupport.intro hgc.isCompact fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  exact hcont.integrable_of_hasCompactSupport hcs

/-- **Green's representation formula in `L^q` of a ball.** For `1 < q < 2` and `v` smooth with compact
support, `∑ i, ∫ ∂_i v(x) • newtonGrad i x dx = v` in `L^q(B(c, r))`. -/
theorem sum_integral_smul_newtonGrad_toLp {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))] (hq1 : 1 < q)
    (hq2 : q < 2) {c : ℂ} {r : ℝ} {v : ℂ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvm : MemLp v q (volume.restrict (ball c r))) :
    ∑ i : Fin 2, ∫ x, (fderiv ℝ v x (basis i)) • newtonGradLp (c := c) (r := r) hq1 hq2 i x =
      hvm.toLp v := by
  have : IsFiniteMeasure (volume.restrict (ball c r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by exact_mod_cast le_top)
  have hGc : ∀ i : Fin 2, Continuous fun x => fderiv ℝ v x (basis i) := fun i =>
    (hv1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hGs : ∀ i : Fin 2, HasCompactSupport fun x => fderiv ℝ v x (basis i) := fun i =>
    hvc.fderiv_apply ℝ _
  have key : ∀ i : Fin 2,
      ((∫ x, (fderiv ℝ v x (basis i)) • newtonGradLp (c := c) (r := r) hq1 hq2 i x :
          Lp ℝ q (volume.restrict (ball c r))) : ℂ → ℝ) =ᵐ[volume.restrict (ball c r)]
        fun y => ∫ x, newtonGrad i x y * fderiv ℝ v x (basis i) := by
    intro i
    have hmeas : AEStronglyMeasurable
        (Function.uncurry fun x y => fderiv ℝ v x (basis i) * newtonGrad i x y)
        (volume.prod (volume.restrict (ball c r))) := by
      have : Measurable
          (Function.uncurry fun x y => fderiv ℝ v x (basis i) * newtonGrad i x y) :=
        ((hGc i).measurable.comp measurable_fst).mul
          ((measurable_newtonGradKernel i).comp (measurable_snd.sub measurable_fst))
      exact this.aestronglyMeasurable
    have h := coeFn_integral_ae_eq_integral_apply (p := (q : ℝ≥0∞)) (ν := volume)
      (m := volume.restrict (ball c r)) ENNReal.coe_ne_top
      (fun x => (fderiv ℝ v x (basis i)) • newtonGradLp (c := c) (r := r) hq1 hq2 i x)
      (integrable_smul_newtonGradLp hq1 hq2 i (hGc i) (hGs i))
      (fun x y => fderiv ℝ v x (basis i) * newtonGrad i x y)
      (fun x => by
        filter_upwards [Lp.coeFn_smul (fderiv ℝ v x (basis i))
          (newtonGradLp (c := c) (r := r) hq1 hq2 i x),
          (memLp_newtonGrad (c := c) (r := r) hq1 hq2 i x).coeFn_toLp] with y h1 h2
        have h2' : (⇑(newtonGradLp (c := c) (r := r) hq1 hq2 i x)) y = newtonGrad i x y := h2
        rw [h1, Pi.smul_apply, smul_eq_mul, h2'])
      hmeas
    refine h.trans (ae_of_all _ fun y => ?_)
    exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  rw [Fin.sum_univ_two]
  apply Lp.ext
  have hadd := Lp.coeFn_add
    (∫ x, (fderiv ℝ v x (basis 0)) • newtonGradLp (c := c) (r := r) hq1 hq2 0 x :
      Lp ℝ q (volume.restrict (ball c r)))
    (∫ x, (fderiv ℝ v x (basis 1)) • newtonGradLp (c := c) (r := r) hq1 hq2 1 x :
      Lp ℝ q (volume.restrict (ball c r)))
  filter_upwards [hadd, key 0, key 1, hvm.coeFn_toLp] with y hy h0 h1 hv'
  rw [hy, Pi.add_apply, h0, h1, hv']
  have := eq_sum_integral_newtonGrad hv hvc y
  rw [Fin.sum_univ_two] at this
  exact this.symm

end MatedCRT.GFFLocalRegularity
