import MatedCRT.FirstPass.Derived.ZeroConePolygonalPhaseBase
import MatedCRT.FirstPass.Derived.ConeOffsetDensityProof
import MatedCRT.FirstPass.Derived.ConeAreaBumpTiltProof
import MatedCRT.FirstPass.Derived.ConeLQGAreaMeasurable
import MatedCRT.FirstPass.Derived.IGCurveScaleLaw
import MatedCRT.FirstPass.Derived.ZeroConeTailOfLemmaA1

/-!
# The tilted area measure of the zero cone: absolute continuity of the law of `(μ, ηL)`

Let `μ_ω = ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω)` be the area measure of the zero-cone field and
`ηL` the Lebesgue-parametrized space-filling curve of the mating-of-trees coupling. For a smooth `g` with support in the
punctured unit disk, `tiltArea g μ_ω` is the area measure of the field with the bump added. This file proves that the
law of `(tiltArea g μ_ω, ηL)` is absolutely continuous with respect to the law of `(μ_ω, ηL)`, and deduces a transfer
statement that is uniform in the test function and carries an independent uniform phase.

The Cameron–Martin step is already proved: the null sets of the shifted and unshifted cone data (the lateral part of the
field and the two radial Brownian motions) jointly with an independent random element coincide
(`measure_coneShift_eq_zero_iff`), and the area form `coneAreaBumpTilt` states that
`law(e, μ_h) ≪ law(e, e^{γ f} μ_h)` for a smooth `f` supported in the punctured unit disk and an independent curve `e`.
Nothing about Gaussian shifts is reproved here. The direction needed here,
`law(e, e^{γ f} μ) ≪ law(e, μ)`, comes from `coneAreaBumpTilt` applied to `-f` and pushed forward by the measurable map
`ν ↦ e^{γ f} ν`, because `e^{γ f} (e^{-γ f} ν) = ν`. The bump is used only through the property that it is smooth with
support in the punctured unit disk.

## Main statements

* `zeroConeArea`: the area measure `μ_ω` of the zero-cone field.
* `zeroConeArea_ae_eq_quantumConeArea`: `μ_ω` is almost surely the area `quantumConeArea γ 0 X₀ B₀ B₀' ω`.
* `ae_tilt_law_abs`: `law(tiltArea g μ, ηL) ≪ law(μ, ηL)`.
* `exists_integral_le_of_absolutelyContinuous`: for finite measures `ρ' ≪ ρ`, the integrals against `ρ'` of the
  `[0, 1]`-valued measurable functions are small once those against `ρ` are small.
* `exists_tilt_transfer`: the uniform statement for the enlarged experiment (sample, uniform phase, independent
  probability space), where the phase is shifted modulo `1` by a measurable function of `(μ, ηL)`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b
open scoped NNReal ENNReal

section Tilt

/-- For a measurable density `f`, the map `ν ↦ ν.withDensity f` of measures is measurable. -/
theorem measurable_withDensity_fun {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun ν : Measure ℂ => ν.withDensity f := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have : (fun ν : Measure ℂ => ν.withDensity f s) = fun ν : Measure ℂ => ∫⁻ a, s.indicator f a ∂ν := by
    funext ν
    rw [withDensity_apply _ hs, lintegral_indicator hs]
  rw [this]
  exact Measure.measurable_lintegral (hf.indicator hs)

/-- The tilt `ν ↦ e^g ν` is a measurable map of measures when `g` is measurable. -/
theorem measurable_tiltArea {g : ℂ → ℝ} (hg : Measurable g) : Measurable (tiltArea g) :=
  measurable_withDensity_fun (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hg))

/-- **The tilt by `-g` is undone by the tilt by `g`**: `e^g (e^{-g} ν) = ν`, in the form with the density
`e^{γ (-g/γ)}` produced by `coneAreaBumpTilt` applied to `-g/γ`. -/
theorem tiltArea_withDensity_neg {γ : ℝ} (hγ : γ ≠ 0) {g : ℂ → ℝ} (hg : Measurable g) (ν : Measure ℂ) :
    tiltArea g (ν.withDensity fun z => ENNReal.ofReal (Real.exp (γ * (-g z / γ)))) = ν := by
  have h1 : Measurable fun z => ENNReal.ofReal (Real.exp (γ * (-g z / γ))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      ((hg.neg).div_const γ)))
  have h2 : Measurable fun z => ENNReal.ofReal (Real.exp (g z)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hg)
  rw [tiltArea, ← withDensity_mul _ h1 h2]
  have : ((fun z => ENNReal.ofReal (Real.exp (γ * (-g z / γ)))) *
      fun z => ENNReal.ofReal (Real.exp (g z))) = 1 := by
    funext z
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    have : γ * (-g z / γ) + g z = 0 := by field_simp; ring
    rw [this, Real.exp_zero, ENNReal.ofReal_one]
  rw [this, withDensity_one]

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The area measure `μ_ω` of the zero-cone field `zeroConeFieldOf γ X₀ B₀ B₀' ω` (the Borel area map `fieldArea` of
the field). -/
abbrev zeroConeArea (γ : ℝ) {Ω : Type} (X₀ : Ω → Field) (B₀ B₀' : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℂ :=
  ZeroConeRoot.fieldArea γ (zeroConeFieldOf γ X₀ B₀ B₀' ω)

/-- **The zero-cone area is almost surely the area of the `0`-quantum cone**: `zeroConeArea` agrees almost surely with
`quantumConeArea γ 0 X₀ B₀ B₀'`, the quantity to which `coneAreaBumpTilt` applies. -/
theorem zeroConeArea_ae_eq_quantumConeArea
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, zeroConeArea γ X₀ B₀ B₀' ω = quantumConeArea γ 0 X₀ B₀ B₀' ω := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have h1 := ZeroConeRoot.ae_isVagueLimitC_fieldArea hγ D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀.1 D.indep_cone₀.2
  have h2 := ae_of_ae_map
    (ZeroConeRoot.aemeasurable_zeroConeFieldOf γ D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀.2) h1
  filter_upwards [h2] with ω hω
  exact (MatedCRTHarmonic.LQGCoord.lqgArea_eq_of_isVagueLimitC hω).symm

/-- The zero-cone area is almost everywhere measurable as a map to measures. -/
theorem aemeasurable_zeroConeArea
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    AEMeasurable (zeroConeArea γ X₀ B₀ B₀') P := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  exact (ZeroConeRoot.measurable_fieldArea γ).comp_aemeasurable
    (ZeroConeRoot.aemeasurable_zeroConeFieldOf γ D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀.2)

/-- **The law of the tilted area and the curve is absolutely continuous with respect to the law of the area and the
curve.** For `g` smooth with support in the punctured unit disk, `law(tiltArea g μ, ηL) ≪ law(μ, ηL)`, where `μ` is
the area measure of the zero-cone field. This is `coneAreaBumpTilt` at `-g/γ`, pushed forward by `ν ↦ tiltArea g ν`. -/
theorem ae_tilt_law_abs
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {g : ℂ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hs : tsupport g ⊆ Metric.ball (0 : ℂ) 1 \ {0}) :
    P.map (fun ω => (tiltArea g (zeroConeArea γ X₀ B₀ B₀' ω), ηL ω)) ≪
      P.map (fun ω => (zeroConeArea γ X₀ B₀ B₀' ω, ηL ω)) := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hηL : Measurable ηL := D.measurable_curves.1
  have hind := Sec1.indepFun_igCurve_cone D
  have hψ₀ : Measurable fun p : Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
      (p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2) :=
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
      ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        measurable_snd)))).prodMk (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))))
  have hie₀ : IndepFun ηL (fun ω => (X₀ ω, (fun t => B₀ t ω), (fun t => B₀' t ω))) P :=
    hind.comp measurable_id hψ₀
  have hA0 : AEMeasurable (quantumConeArea γ 0 X₀ B₀ B₀') P :=
    Sec1.aemeasurable_lqgArea_of_aemeasurable γ (MatedCRTHarmonic.GMS4.aemeasurable_prop48ZeroConeField D)
      (MatedCRTHarmonic.MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ D hγ)
  have hγ0 : γ ≠ 0 := hγ.1.ne'
  have hgm : Measurable g := hg.continuous.measurable
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => -g z / γ) := (hg.neg).div_const γ
  have hfs : tsupport (fun z => -g z / γ) ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
    refine (closure_mono (fun z hz => ?_)).trans hs
    simp only [mem_support, ne_eq, div_eq_zero_iff, neg_eq_zero, not_or] at hz
    exact hz.1
  have hT : P.map (fun ω => (ηL ω, quantumConeArea γ 0 X₀ B₀ B₀' ω)) ≪
      P.map (fun ω => (ηL ω, (quantumConeArea γ 0 X₀ B₀ B₀' ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * (-g z / γ)))))) :=
    coneAreaBumpTilt γ P 0 X₀ B₀ B₀' ηL hγ (Or.inl rfl) D.gff₀ D.bm_B₀ D.bm_B₀' D.indep_cone₀ hηL
      hie₀ (fun z => -g z / γ) hf hfs
  have hΘ : Measurable fun p : C(ℝ, ℂ) × Measure ℂ => (tiltArea g p.2, p.1) :=
    ((measurable_tiltArea hgm).comp measurable_snd).prodMk measurable_fst
  have hu : AEMeasurable (fun ω => (ηL ω, quantumConeArea γ 0 X₀ B₀ B₀' ω)) P :=
    hηL.aemeasurable.prodMk hA0
  have hdens : Measurable fun z : ℂ => ENNReal.ofReal (Real.exp (γ * (-g z / γ))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul ((hgm.neg).div_const γ)))
  have hv : AEMeasurable (fun ω => (ηL ω, (quantumConeArea γ 0 X₀ B₀ B₀' ω).withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * (-g z / γ)))))) P :=
    (measurable_fst.prodMk ((measurable_withDensity_fun hdens).comp measurable_snd)).comp_aemeasurable hu
  have h3 := hT.map hΘ
  rw [AEMeasurable.map_map_of_aemeasurable hΘ.aemeasurable hu,
    AEMeasurable.map_map_of_aemeasurable hΘ.aemeasurable hv] at h3
  have hR : ((fun p : C(ℝ, ℂ) × Measure ℂ => (tiltArea g p.2, p.1)) ∘ fun ω => (ηL ω,
      (quantumConeArea γ 0 X₀ B₀ B₀' ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * (-g z / γ)))))) =
      fun ω => (quantumConeArea γ 0 X₀ B₀ B₀' ω, ηL ω) := by
    funext ω
    simp only [Function.comp_apply]
    rw [tiltArea_withDensity_neg hγ0 hgm]
  rw [hR] at h3
  have hae := zeroConeArea_ae_eq_quantumConeArea D hγ
  have hL : P.map ((fun p : C(ℝ, ℂ) × Measure ℂ => (tiltArea g p.2, p.1)) ∘ fun ω => (ηL ω,
      quantumConeArea γ 0 X₀ B₀ B₀' ω)) =
      P.map (fun ω => (tiltArea g (zeroConeArea γ X₀ B₀ B₀' ω), ηL ω)) :=
    Measure.map_congr (hae.mono fun ω hω => by simp only [Function.comp_apply, hω])
  have hR' : P.map (fun ω => (quantumConeArea γ 0 X₀ B₀ B₀' ω, ηL ω)) =
      P.map (fun ω => (zeroConeArea γ X₀ B₀ B₀' ω, ηL ω)) :=
    Measure.map_congr (hae.mono fun ω hω => by simp only [hω])
  rw [hL, hR'] at h3
  exact h3

end Coupling

end Tilt

section Uniform

/-- **Uniform absolute continuity for `[0, 1]`-valued test functions.** If `ρ' ≪ ρ` are finite measures, then for every
`ε > 0` there is `δ > 0` such that every measurable `G` with values in `[0, 1]` and `∫ G dρ ≤ δ` has `∫ G dρ' ≤ ε`. -/
theorem exists_integral_le_of_absolutelyContinuous {S : Type*} [MeasurableSpace S] {ρ ρ' : Measure S}
    [IsFiniteMeasure ρ] [IsFiniteMeasure ρ'] (h : ρ' ≪ ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ G : S → ℝ, Measurable G → (∀ x, 0 ≤ G x ∧ G x ≤ 1) →
      ∫ x, G x ∂ρ ≤ δ → ∫ x, G x ∂ρ' ≤ ε := by
  have hc0 : 0 ≤ ρ'.real univ := measureReal_nonneg
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / (2 * (ρ'.real univ + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηc : η * ρ'.real univ ≤ ε / 2 := by
    have h1 : η * (ρ'.real univ + 1) = ε / 2 := by rw [hη]; field_simp
    nlinarith
  have hfin : ∫⁻ x, ρ'.rnDeriv ρ x ∂ρ ≠ ∞ := (Measure.lintegral_rnDeriv_lt_top ρ' ρ).ne
  obtain ⟨δ', hδ'0, hδ'⟩ := exists_pos_setLIntegral_lt_of_measure_lt hfin
    (ε := ENNReal.ofReal (ε / 2)) (by simpa using hε)
  have hρ's : ∀ s, MeasurableSet s → ρ s < δ' → ρ' s < ENNReal.ofReal (ε / 2) := fun s hs hρ => by
    have key : ρ' = ρ.withDensity (ρ'.rnDeriv ρ) := (Measure.withDensity_rnDeriv_eq ρ' ρ h).symm
    have h1 := hδ' s hρ
    rw [key, withDensity_apply _ hs]
    exact h1
  have hδ₁0 : 0 < min δ' 1 := lt_min hδ'0 one_pos
  have hδ₁top : min δ' 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (min δ' 1).toReal / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    have := ENNReal.toReal_pos hδ₁0.ne' hδ₁top
    rw [hr]
    positivity
  refine ⟨η * r, by positivity, fun G hGm hG hint => ?_⟩
  have hGint : ∀ ν : Measure S, IsFiniteMeasure ν → Integrable G ν := fun ν _ =>
    Integrable.of_bound hGm.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hG x).1]
      exact (hG x).2)
  have hs : MeasurableSet {x | η ≤ G x} := measurableSet_le measurable_const hGm
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := ρ) (ae_of_all _ fun x => (hG x).1)
    (hGint ρ inferInstance) η
  have h1 : ρ.real {x | η ≤ G x} ≤ r := by
    have : η * ρ.real {x | η ≤ G x} ≤ η * r := hmark.trans hint
    exact le_of_mul_le_mul_left this hη0
  have h2 : ρ {x | η ≤ G x} < δ' := by
    have h3 : ρ {x | η ≤ G x} < min δ' 1 := by
      rw [← ENNReal.toReal_lt_toReal (measure_ne_top _ _) hδ₁top]
      have : ρ.real {x | η ≤ G x} = (ρ {x | η ≤ G x}).toReal := rfl
      have := ENNReal.toReal_pos hδ₁0.ne' hδ₁top
      linarith
    exact h3.trans_le (min_le_left _ _)
  have h4 : ρ'.real {x | η ≤ G x} ≤ ε / 2 := by
    have h5 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hρ's _ hs h2).le
    rw [ENNReal.toReal_ofReal (by positivity)] at h5
    exact h5
  have hpt : ∀ x, G x ≤ {x | η ≤ G x}.indicator (fun _ => (1 : ℝ)) x + η := fun x => by
    by_cases hx : x ∈ {x | η ≤ G x}
    · rw [indicator_of_mem hx]
      linarith [(hG x).2]
    · rw [indicator_of_notMem hx]
      have : G x < η := not_le.1 hx
      linarith
  have hind : Integrable ({x | η ≤ G x}.indicator fun _ => (1 : ℝ)) ρ' :=
    (integrable_const (1 : ℝ)).indicator hs
  calc ∫ x, G x ∂ρ' ≤ ∫ x, ({x | η ≤ G x}.indicator (fun _ => (1 : ℝ)) x + η) ∂ρ' :=
        integral_mono (hGint ρ' inferInstance) (hind.add (integrable_const η)) hpt
    _ = ρ'.real {x | η ≤ G x} + ρ'.real univ * η := by
        rw [integral_add hind (integrable_const η), integral_indicator_const _ hs, integral_const]
        simp only [smul_eq_mul, mul_one]
    _ ≤ ε / 2 + ε / 2 := add_le_add h4 (by linarith)
    _ = ε := by ring

end Uniform

section Transfer

variable {M C E : Type*} [MeasurableSpace M] [MeasurableSpace C] [MeasurableSpace E]

/-- **The measure-level core of the transfer.** Let `ρ` be a finite measure on `M × C`, `κ` a probability measure on
`E`, `τ : M → M` measurable with `ρ.map (τ × id) ≪ ρ`, and `d` a measurable function on `M × C`. Then the image of
`ρ ⊗ (uniform phase ⊗ κ)` under `((m, e), (θ, s)) ↦ (τ m, e, (θ + d (m, e)) mod 1, s)` is absolutely continuous with
respect to its image under `((m, e), (θ, s)) ↦ (m, e, θ, s)`: the phase shift by a function of `(m, e)` preserves the
uniform law, and `τ` is absolutely continuous by assumption. -/
theorem map_tiltPhase_absolutelyContinuous {ρ : Measure (M × C)} [IsFiniteMeasure ρ] {κ : Measure E}
    [IsProbabilityMeasure κ] {τ : M → M} (hτ : Measurable τ) {d : M × C → ℝ} (hd : Measurable d)
    (hρ : ρ.map (Prod.map τ id) ≪ ρ) :
    (ρ.prod (zeroConePhase.prod κ)).map
        (fun p : (M × C) × ℝ × E =>
          (τ p.1.1, p.1.2, toIcoMod (zero_lt_one' ℝ) 0 (p.2.1 + d p.1), p.2.2)) ≪
      (ρ.prod (zeroConePhase.prod κ)).map (fun p : (M × C) × ℝ × E => (p.1.1, p.1.2, p.2.1, p.2.2)) := by
  set Λ : Measure (ℝ × E) := zeroConePhase.prod κ with hΛ
  have hTI : ∀ c : ℝ, Measurable fun x : ℝ => toIcoMod (zero_lt_one' ℝ) 0 (x + c) := fun c =>
    (LatticeProb.measurable_toIcoMod_zero (zero_lt_one' ℝ)).comp (measurable_id.add_const c)
  have hphase : ∀ c : ℝ, zeroConePhase.map (fun x => toIcoMod (zero_lt_one' ℝ) 0 (x + c)) = zeroConePhase :=
    fun c => Measure.ext fun S hS => by
      rw [Measure.map_apply (hTI c) hS, zeroConePhase_toIcoMod_preimage c hS]
  have hg : ∀ a : M × C, Λ.map (fun q : ℝ × E => (toIcoMod (zero_lt_one' ℝ) 0 (q.1 + d a), q.2)) = Λ :=
    fun a => by
      have := Measure.map_prod_map zeroConePhase κ (hTI (d a)) measurable_id
      rw [hphase, Measure.map_id] at this
      exact this.symm
  have hgm : Measurable (Function.uncurry fun (a : M × C) (q : ℝ × E) =>
      (toIcoMod (zero_lt_one' ℝ) 0 (q.1 + d a), q.2)) :=
    ((LatticeProb.measurable_toIcoMod_zero (zero_lt_one' ℝ)).comp
      ((measurable_fst.comp measurable_snd).add (hd.comp measurable_fst))).prodMk
      (measurable_snd.comp measurable_snd)
  have h1 : (ρ.prod Λ).map
      (fun p : (M × C) × ℝ × E => (p.1, toIcoMod (zero_lt_one' ℝ) 0 (p.2.1 + d p.1), p.2.2)) = ρ.prod Λ :=
    ((MeasurePreserving.id ρ).skew_product (μc := Λ) (μd := Λ)
      (g := fun a q => (toIcoMod (zero_lt_one' ℝ) 0 (q.1 + d a), q.2)) hgm (ae_of_all _ hg)).map_eq
  have hΞ₁ : Measurable fun p : (M × C) × ℝ × E =>
      (p.1, toIcoMod (zero_lt_one' ℝ) 0 (p.2.1 + d p.1), p.2.2) :=
    measurable_fst.prodMk (((LatticeProb.measurable_toIcoMod_zero (zero_lt_one' ℝ)).comp
      ((measurable_fst.comp measurable_snd).add (hd.comp measurable_fst))).prodMk
      (measurable_snd.comp measurable_snd))
  have hΞ₂ : Measurable fun p : (M × C) × ℝ × E => (τ p.1.1, p.1.2, p.2.1, p.2.2) := by fun_prop
  have hΞ₀ : Measurable fun p : (M × C) × ℝ × E => (p.1.1, p.1.2, p.2.1, p.2.2) := by fun_prop
  have hcomp : (fun p : (M × C) × ℝ × E =>
      (τ p.1.1, p.1.2, toIcoMod (zero_lt_one' ℝ) 0 (p.2.1 + d p.1), p.2.2)) =
      (fun p : (M × C) × ℝ × E => (τ p.1.1, p.1.2, p.2.1, p.2.2)) ∘
        fun p : (M × C) × ℝ × E => (p.1, toIcoMod (zero_lt_one' ℝ) 0 (p.2.1 + d p.1), p.2.2) := rfl
  have h2 : (ρ.prod Λ).map (fun p : (M × C) × ℝ × E =>
      (τ p.1.1, p.1.2, toIcoMod (zero_lt_one' ℝ) 0 (p.2.1 + d p.1), p.2.2)) =
      (ρ.prod Λ).map (fun p : (M × C) × ℝ × E => (τ p.1.1, p.1.2, p.2.1, p.2.2)) := by
    rw [hcomp, ← Measure.map_map hΞ₂ hΞ₁, h1]
  have hτid : Measurable (Prod.map τ (id : C → C)) := hτ.prodMap measurable_id
  have h3 : (ρ.prod Λ).map (fun p : (M × C) × ℝ × E => (τ p.1.1, p.1.2, p.2.1, p.2.2)) =
      ((ρ.map (Prod.map τ id)).prod Λ).map (fun p : (M × C) × ℝ × E => (p.1.1, p.1.2, p.2.1, p.2.2)) := by
    have := Measure.map_prod_map ρ Λ hτid (measurable_id : Measurable (id : ℝ × E → ℝ × E))
    rw [Measure.map_id] at this
    rw [this, Measure.map_map hΞ₀ (hτid.prodMap measurable_id)]
    rfl
  rw [h2, h3]
  exact (Measure.AbsolutelyContinuous.prod hρ (Measure.AbsolutelyContinuous.refl _)).map hΞ₀

/-- **The transfer for a measurable family of areas and curves.** Let `f : Ω → M × C` be measurable and `P` a
probability measure with `law(τ ∘ fst ∘ f, snd ∘ f) ≪ law(f)`. Then for every measurable `d` and every probability space
`(E, κ)`, the integrals of `[0, 1]`-valued measurable functions against the law of
`(f, phase, s)` control those against the law of `(τ f₁, f₂, (phase + d f) mod 1, s)`, uniformly in the function. -/
theorem exists_tilt_transfer_of_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → M × C} (hf : Measurable f) {τ : M → M} (hτ : Measurable τ)
    {d : M × C → ℝ} (hd : Measurable d)
    (hac : P.map (fun ω => (τ (f ω).1, (f ω).2)) ≪ P.map f) (κ : Measure E) [IsProbabilityMeasure κ] :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ G : M × C × ℝ × E → ℝ, Measurable G → (∀ x, 0 ≤ G x ∧ G x ≤ 1) →
      ∫ x, G ((f x.1.1).1, (f x.1.1).2, x.1.2, x.2) ∂((P.prod zeroConePhase).prod κ) ≤ δ →
      ∫ x, G (τ (f x.1.1).1, (f x.1.1).2, toIcoMod (zero_lt_one' ℝ) 0 (x.1.2 + d (f x.1.1)), x.2)
        ∂((P.prod zeroConePhase).prod κ) ≤ ε := by
  intro ε hε
  set Q : Measure ((Ω × ℝ) × E) := (P.prod zeroConePhase).prod κ with hQ
  have hF : Measurable fun x : (Ω × ℝ) × E => (f x.1.1, (x.1.2, x.2)) := by fun_prop
  have hFmap : Q.map (fun x : (Ω × ℝ) × E => (f x.1.1, (x.1.2, x.2))) =
      (P.map f).prod (zeroConePhase.prod κ) := by
    have h1 : (fun x : (Ω × ℝ) × E => (f x.1.1, (x.1.2, x.2))) =
        Prod.map f (id : ℝ × E → ℝ × E) ∘ MeasurableEquiv.prodAssoc := rfl
    rw [h1, ← Measure.map_map (hf.prodMap measurable_id) MeasurableEquiv.prodAssoc.measurable, hQ,
      Measure.prodAssoc_prod]
    have := Measure.map_prod_map P (zeroConePhase.prod κ) hf (measurable_id : Measurable (id : ℝ × E → ℝ × E))
    rw [Measure.map_id] at this
    exact this.symm
  have hτid : Measurable (Prod.map τ (id : C → C)) := hτ.prodMap measurable_id
  have hρ : (P.map f).map (Prod.map τ id) ≪ P.map f := by
    rw [Measure.map_map hτid hf]
    exact hac
  have hAC := map_tiltPhase_absolutelyContinuous (κ := κ) hτ hd hρ
  set Ξ₀ : (M × C) × ℝ × E → M × C × ℝ × E := fun p => (p.1.1, p.1.2, p.2.1, p.2.2) with hΞ₀def
  set Ξ : (M × C) × ℝ × E → M × C × ℝ × E := fun p =>
    (τ p.1.1, p.1.2, toIcoMod (zero_lt_one' ℝ) 0 (p.2.1 + d p.1), p.2.2) with hΞdef
  have hΞ₀ : Measurable Ξ₀ := by fun_prop
  have hΞ : Measurable Ξ :=
    ((hτ.comp (measurable_fst.comp measurable_fst))).prodMk
      ((measurable_snd.comp measurable_fst).prodMk
        (((LatticeProb.measurable_toIcoMod_zero (zero_lt_one' ℝ)).comp
          ((measurable_fst.comp measurable_snd).add (hd.comp measurable_fst))).prodMk
          (measurable_snd.comp measurable_snd)))
  set F : (Ω × ℝ) × E → (M × C) × ℝ × E := fun x => (f x.1.1, (x.1.2, x.2)) with hFdef
  have hA : Q.map (Ξ₀ ∘ F) = ((P.map f).prod (zeroConePhase.prod κ)).map Ξ₀ := by
    rw [← Measure.map_map hΞ₀ hF, hFmap]
  have hA' : Q.map (Ξ ∘ F) = ((P.map f).prod (zeroConePhase.prod κ)).map Ξ := by
    rw [← Measure.map_map hΞ hF, hFmap]
  haveI : IsProbabilityMeasure (Q.map (Ξ₀ ∘ F)) :=
    Measure.isProbabilityMeasure_map (hΞ₀.comp hF).aemeasurable
  haveI : IsProbabilityMeasure (Q.map (Ξ ∘ F)) :=
    Measure.isProbabilityMeasure_map (hΞ.comp hF).aemeasurable
  obtain ⟨δ, hδ0, hδ⟩ := exists_integral_le_of_absolutelyContinuous (ρ := Q.map (Ξ₀ ∘ F))
    (ρ' := Q.map (Ξ ∘ F)) (by rw [hA, hA']; exact hAC) hε
  refine ⟨δ, hδ0, fun G hG hG01 hint => ?_⟩
  have e1 : ∫ x, G x ∂(Q.map (Ξ₀ ∘ F)) =
      ∫ x, G ((f x.1.1).1, (f x.1.1).2, x.1.2, x.2) ∂Q :=
    integral_map (hΞ₀.comp hF).aemeasurable hG.aestronglyMeasurable
  have e2 : ∫ x, G x ∂(Q.map (Ξ ∘ F)) =
      ∫ x, G (τ (f x.1.1).1, (f x.1.1).2, toIcoMod (zero_lt_one' ℝ) 0 (x.1.2 + d (f x.1.1)), x.2) ∂Q :=
    integral_map (hΞ.comp hF).aemeasurable hG.aestronglyMeasurable
  rw [← e2]
  exact hδ G hG hG01 (by rw [e1]; exact hint)

/-- **The transfer for an almost everywhere measurable family of areas and curves**: the statement of
`exists_tilt_transfer_of_measurable` for `f` measurable up to a null set. -/
theorem exists_tilt_transfer_of_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → M × C} (hf : AEMeasurable f P) {τ : M → M} (hτ : Measurable τ)
    {d : M × C → ℝ} (hd : Measurable d)
    (hac : P.map (fun ω => (τ (f ω).1, (f ω).2)) ≪ P.map f) (κ : Measure E) [IsProbabilityMeasure κ] :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ G : M × C × ℝ × E → ℝ, Measurable G → (∀ x, 0 ≤ G x ∧ G x ≤ 1) →
      ∫ x, G ((f x.1.1).1, (f x.1.1).2, x.1.2, x.2) ∂((P.prod zeroConePhase).prod κ) ≤ δ →
      ∫ x, G (τ (f x.1.1).1, (f x.1.1).2, toIcoMod (zero_lt_one' ℝ) 0 (x.1.2 + d (f x.1.1)), x.2)
        ∂((P.prod zeroConePhase).prod κ) ≤ ε := by
  intro ε hε
  have hfeq : f =ᵐ[P] hf.mk f := hf.ae_eq_mk
  have hmap : P.map (hf.mk f) = P.map f := (Measure.map_congr hfeq).symm
  have hac' : P.map (fun ω => (τ (hf.mk f ω).1, (hf.mk f ω).2)) ≪ P.map (hf.mk f) := by
    have e1 : P.map (fun ω => (τ (hf.mk f ω).1, (hf.mk f ω).2)) =
        P.map (fun ω => (τ (f ω).1, (f ω).2)) :=
      Measure.map_congr (hfeq.mono fun ω hω => by rw [← hω])
    rw [e1, hmap]
    exact hac
  obtain ⟨δ, hδ0, hδ⟩ := exists_tilt_transfer_of_measurable hf.measurable_mk hτ hd hac' κ ε hε
  refine ⟨δ, hδ0, fun G hG hG01 hint => ?_⟩
  have hae : ∀ᵐ x ∂((P.prod zeroConePhase).prod κ), f x.1.1 = hf.mk f x.1.1 :=
    ZeroConeRoot.ae_prod_fst_of_ae (p := fun z : Ω × ℝ => f z.1 = hf.mk f z.1)
      (ZeroConeRoot.ae_prod_fst_of_ae (p := fun ω => f ω = hf.mk f ω) hfeq)
  have i1 : ∫ x, G ((f x.1.1).1, (f x.1.1).2, x.1.2, x.2) ∂((P.prod zeroConePhase).prod κ) =
      ∫ x, G ((hf.mk f x.1.1).1, (hf.mk f x.1.1).2, x.1.2, x.2) ∂((P.prod zeroConePhase).prod κ) :=
    integral_congr_ae (hae.mono fun x hx => by rw [← hx])
  have i2 : ∫ x, G (τ (f x.1.1).1, (f x.1.1).2, toIcoMod (zero_lt_one' ℝ) 0 (x.1.2 + d (f x.1.1)), x.2)
        ∂((P.prod zeroConePhase).prod κ) =
      ∫ x, G (τ (hf.mk f x.1.1).1, (hf.mk f x.1.1).2,
        toIcoMod (zero_lt_one' ℝ) 0 (x.1.2 + d (hf.mk f x.1.1)), x.2) ∂((P.prod zeroConePhase).prod κ) :=
    integral_congr_ae (hae.mono fun x hx => by rw [← hx])
  rw [i2]
  exact hδ G hG hG01 (by rw [← i1]; exact hint)

end Transfer

section Main

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Uniform absolute continuity for the enlarged experiment.** Let `g` be smooth with support in the punctured unit
disk, `d` a measurable function of `(μ, ηL)`, and `(E, κ)` a probability space (for the grid, the root and the level).
For every `ε > 0` there is `δ > 0` such that for every measurable `G` with values in `[0, 1]`, the bound
`∫ G(μ, ηL, θ, s) ≤ δ` over the sample, a uniform phase `θ` and `s ∼ κ` implies the bound
`∫ G(e^g μ, ηL, (θ + d(μ, ηL)) mod 1, s) ≤ ε` over the same space. -/
theorem exists_tilt_transfer
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {g : ℂ → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hs : tsupport g ⊆ Metric.ball (0 : ℂ) 1 \ {0})
    {d : Measure ℂ × C(ℝ, ℂ) → ℝ} (hd : Measurable d)
    {E : Type*} [MeasurableSpace E] (κ : Measure E) [IsProbabilityMeasure κ] :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ G : Measure ℂ × C(ℝ, ℂ) × ℝ × E → ℝ, Measurable G →
      (∀ x, 0 ≤ G x ∧ G x ≤ 1) →
      ∫ x, G (zeroConeArea γ X₀ B₀ B₀' x.1.1, ηL x.1.1, x.1.2, x.2)
        ∂((P.prod zeroConePhase).prod κ) ≤ δ →
      ∫ x, G (tiltArea g (zeroConeArea γ X₀ B₀ B₀' x.1.1), ηL x.1.1,
          toIcoMod (zero_lt_one' ℝ) 0 (x.1.2 + d (zeroConeArea γ X₀ B₀ B₀' x.1.1, ηL x.1.1)), x.2)
        ∂((P.prod zeroConePhase).prod κ) ≤ ε := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hfae : AEMeasurable (fun ω => (zeroConeArea γ X₀ B₀ B₀' ω, ηL ω)) P :=
    (aemeasurable_zeroConeArea D).prodMk D.measurable_curves.1.aemeasurable
  exact exists_tilt_transfer_of_aemeasurable (f := fun ω => (zeroConeArea γ X₀ B₀ B₀' ω, ηL ω)) hfae
    (measurable_tiltArea hg.continuous.measurable) hd (ae_tilt_law_abs D hγ hg hs) κ

end Main

end MatedCRT.ZeroConePolygonal
