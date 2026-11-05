import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.Proofs.Sec1.ConeScaleRadius
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.LQGScaling
import MatedCRT.External.SLE
import MatedCRT.Draft.Section2

/-!
# The rescaled environment is valid (`ConeEnvironmentScalingStep`; eq:scale-invariance-of-field-and-eta)

For a valid environment `S` and `b > 0`, with `R = R_b` the cone scale radius (eq:cone-scale-radius, line 451), the
rescaled environment `S.rescaleWith γ b hC' clock'` has
* circle averages `h^b_r(z) = h_{Rr}(Rz) + Q log R - γ⁻¹ log b` (`rescaledCircle`) and pairings `hC'`,
* LQG measure `A ↦ b⁻¹ μ_h(R A)` (`rescaledMeasure`), curve `η^b = R⁻¹ η(b ·)`,
* boundary-length pair `b^{-1/2} (L, R)(b ·)` (`rescaledPair`) and LQG clock `clock'`.

`coneEnvironmentScalingStep_of_inputs` proves `ConeEnvironmentScalingStep` (Theorems 1.4, 1.6, 4.1). The fields of
`MatedCRTEnv.IsValid` for the rescaled environment are obtained as follows.
* `isProbabilityMeasure`: same `P`.
* `isAreaParametrized`: deterministic (`isAreaParametrized_rescale`), `μ'(η'[s,t]) = b⁻¹ μ(η[bs,bt]) = t - s`, on the
  event `R_b > 0` (a.s. by `QuantumConeScalingInput`, `Sec1.ae_coneScaleRadius_pos`, worker c3).
* `isLQGMeasure`: Fact 2.2 III, IV (`LQGMeasurePropertiesStmt`) through worker c5's `coneLQGScalingStep_of_steps`.
* `isQuantumCone`: `ae_continuousOn_circle` (pathwise, `R_b > 0`) and `radial_law` (the radial process is a measurable
  function of the circle average process, whose law is preserved by `QuantumConeScalingInput`) are derived here;
  `measurable_pairing`, `measurable_circle`, `indep`, `lateral_law` come from the requested input.
* `isSLE`: from `SLEReparametrizationInput` (`s ↦ b s`), `SLEScaleInvarianceInput` (the `σ(h)`-measurable factor
  `R_b⁻¹`) and `SLEIndepMonoInput` (`σ(h^b) ≤ σ(h)`), given the measurability facts of the requested input.
* `isLQGClock`, `matingOfTrees`: from the requested input.

## The requested input (`RescaledEnvironmentInput`, INPUT-REQUESTS IR-c1-1)

One combined literature input; for `S` valid and `b > 0` there are pairings `hC'` and a clock `clock'` such that
1. DMS14 Proposition 4.13(i) at the level of the field: the subfields `measurable_pairing`, `measurable_circle`, `indep`
   and `lateral_law` of `IsQuantumCone` hold for `(hC', h^b_·)` (`QuantumConeScalingInput` only gives the law of the
   circle average process);
2. `h^b` is a function of `h` (line 455): `σ(hC') ≤ σ(hC)`, and `R_b` agrees a.s. with a `σ(hC)`-measurable random
   variable (`R_b` is a function of the circle averages, which are a.s. limits of pairings);
3. Liouville Brownian motion coordinate change (GRV16 Theorem 2.4 / Berestycki 2015, Section 2.7 line 712): an LQG
   clock of planar Brownian motion for `h^b` (e.g. `B ↦ b⁻¹ φ_h(R B(R⁻² ·))(R² ·)`);
4. scaling of the mating-of-trees coupling (DMS14 Theorem 1.9 for `h^b`, which is a `γ`-quantum cone by 1., and
   `η^b`, with Brownian scaling of `(L, R)`): Leo Bonanno's `IsMatingOfTreesCoupling` (REUSE-LEO.md 1.5) for
   `(h^b, η^b, b^{-1/2} (L, R)(b ·))`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- The rescaled boundary-length pair `s ↦ b^{-1/2} (L, R)(b s)` (Brownian scaling). -/
noncomputable def rescaledPair (b : ℝ) (w : C(ℝ, ℝ × ℝ)) : C(ℝ, ℝ × ℝ) :=
  ⟨fun s => (Real.sqrt b)⁻¹ • w (b * s), by fun_prop⟩

/-- Evaluation of `rescaledPair`. -/
theorem rescaledPair_apply (b : ℝ) (w : C(ℝ, ℝ × ℝ)) (s : ℝ) :
    rescaledPair b w s = (Real.sqrt b)⁻¹ • w (b * s) :=
  rfl

/-- The rescaled environment of eq:scale-invariance-of-field-and-eta (lines 3286-3293), with given pairings `hC'` of
`h^b` and LQG clock `clock'`: circle averages `rescaledCircle`, measure `rescaledMeasure`, curve `R_b⁻¹ η(b ·)` and
boundary-length pair `rescaledPair`. -/
noncomputable def MatedCRTEnv.rescaleWith {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (γ b : ℝ)
    (hC' : Ω → (ℂ → ℝ) → ℝ) (clock' : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ) : MatedCRTEnv Ω where
  P := S.P
  hC := hC'
  hcirc := fun ω => rescaledCircle γ (S.hcirc ω) (coneScaleRadius γ (S.hcirc ω) b) b
  μ := fun ω => rescaledMeasure (S.μ ω) (coneScaleRadius γ (S.hcirc ω) b) b
  η := fun ω s => ((coneScaleRadius γ (S.hcirc ω) b : ℝ) : ℂ)⁻¹ * S.η ω (b * s)
  clock := clock'
  bm := fun ω => rescaledPair b (S.bm ω)

/-- **Requested input (IR-c1-1): the rescaled environment of eq:scale-invariance-of-field-and-eta.** See the module
docstring for the four parts and their sources (DMS14 Prop 4.13(i) at field level; `h^b` is a function of `h`;
LBM coordinate change, GRV16 / Berestycki 2015; DMS14 Thm 1.9 with Brownian scaling, Leo Bonanno's bundle). -/
def RescaledEnvironmentInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ b : ℝ, 0 < b → ∃ (hC' : Ω → (ℂ → ℝ) → ℝ) (clock' : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ),
    -- 1. DMS14 Prop 4.13(i) for the pairings and the lateral part of `h^b`
    (∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC' ω φ) ∧
    (∀ r z, 0 < r → Measurable fun ω => (S.rescaleWith γ b hC' clock').hcirc ω r z) ∧
    IndepFun (fun ω => radialProcess ((S.rescaleWith γ b hC' clock').hcirc ω))
      (fun ω => lateralProcess (hC' ω) ((S.rescaleWith γ b hC' clock').hcirc ω)) S.P ∧
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC'' : Ω' → (ℂ → ℝ) → ℝ)
        (hcirc'' : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC'' hcirc'' ∧
      S.P.map (fun ω => lateralProcess (hC' ω) ((S.rescaleWith γ b hC' clock').hcirc ω)) =
        P'.map (fun ω => lateralProcess (hC'' ω) (hcirc'' ω))) ∧
    -- 2. `h^b` and `R_b` are functions of `h`
    (S.rescaleWith γ b hC' clock').fieldSigma ≤ S.fieldSigma ∧
    (∃ R : Ω → ℝ, Measurable[S.fieldSigma] R ∧ R =ᵐ[S.P] fun ω => coneScaleRadius γ (S.hcirc ω) b) ∧
    -- 3. the LQG clock of `h^b`
    (∀ᵐ ω ∂S.P, ∀ z : ℂ, IsLQGClock planarBrownianMotion γ ((S.rescaleWith γ b hC' clock').hcirc ω) z (clock' ω) ∧
      ∀ᵐ B ∂planarBrownianMotion z, IsTimeChangeClock (clock' ω B)) ∧
    -- 4. the mating-of-trees coupling of `(h^b, η^b, b^{-1/2} (L, R)(b ·))`
    (∃ (X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η' η₀ : Ω → C(ℝ, ℂ)),
      MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀
          (S.rescaleWith γ b hC' clock').bm ∧
        ∀ᵐ ω ∂S.P, ⇑(η' ω) = (S.rescaleWith γ b hC' clock').η ω ∧ ∀ φ : LQGMetric.TestC,
          hC' ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
            (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ)

namespace Sec1

/-- **Area parametrization is preserved by the rescaling** (deterministic): if `η` is parametrized by `μ`-area with
`η(0) = 0`, then `R⁻¹ η(b ·)` is parametrized by the area of `A ↦ b⁻¹ μ(R A)`. -/
theorem isAreaParametrized_rescale {μ : Measure ℂ} {η : ℝ → ℂ} {R b : ℝ} (hR : 0 < R) (hb : 0 < b)
    (h : IsAreaParametrized μ η) :
    IsAreaParametrized (rescaledMeasure μ R b) (fun s => (R : ℂ)⁻¹ * η (b * s)) := by
  obtain ⟨hc, h0, hsurj, harea⟩ := h
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hbs : ∀ s : ℝ, b * (s / b) = s := fun s => by field_simp
  have hcont : Continuous fun s => (R : ℂ)⁻¹ * η (b * s) :=
    continuous_const.mul (hc.comp (continuous_const.mul continuous_id))
  refine ⟨hcont, by simp [h0], fun w => ?_, fun a c hac => ?_⟩
  · obtain ⟨s, hs⟩ := hsurj ((R : ℂ) * w)
    refine ⟨s / b, ?_⟩
    simp only [hbs, hs]
    exact inv_mul_cancel_left₀ hRc w
  · have himg : (fun x : ℂ => (R : ℂ)⁻¹ * x) ⁻¹' ((fun s => (R : ℂ)⁻¹ * η (b * s)) '' Icc a c) =
        η '' Icc (b * a) (b * c) := by
      ext x
      constructor
      · rintro ⟨s, hs, hsx⟩
        exact ⟨b * s, ⟨mul_le_mul_of_nonneg_left hs.1 hb.le, mul_le_mul_of_nonneg_left hs.2 hb.le⟩,
          mul_left_cancel₀ (inv_ne_zero hRc) hsx⟩
      · rintro ⟨t, ht, rfl⟩
        refine ⟨t / b, ⟨?_, ?_⟩, ?_⟩
        · rw [le_div_iff₀ hb]
          linarith [ht.1]
        · rw [div_le_iff₀ hb]
          linarith [ht.2]
        · show (R : ℂ)⁻¹ * η (b * (t / b)) = (R : ℂ)⁻¹ * η t
          rw [hbs]
    have hmeas : MeasurableSet ((fun s => (R : ℂ)⁻¹ * η (b * s)) '' Icc a c) :=
      (isCompact_Icc.image hcont).isClosed.measurableSet
    have hba : b * a < b * c := mul_lt_mul_of_pos_left hac hb
    have hmul : Measurable fun x : ℂ => (R : ℂ)⁻¹ * x := by fun_prop
    rw [rescaledMeasure, Measure.smul_apply, Measure.map_apply hmul hmeas, himg,
      harea _ _ hba, smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 hb.le)]
    congr 1
    rw [← mul_sub, ← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]

/-- **The circle average process of `h^b` is a.s. continuous** where `R_b > 0` (pathwise). -/
theorem ae_continuousOn_rescaledCircle {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) {b : ℝ}
    (hpos : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b) :
    ∀ᵐ ω ∂P, ContinuousOn
      (fun p : ℝ × ℂ => rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b p.1 p.2)
      (Ioi 0 ×ˢ univ) := by
  filter_upwards [hcone.ae_continuousOn_circle, hpos] with ω hω hR
  have hmaps : MapsTo (fun p : ℝ × ℂ => (coneScaleRadius γ (hcirc ω) b * p.1,
      ((coneScaleRadius γ (hcirc ω) b : ℝ) : ℂ) * p.2)) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) :=
    fun p hp => ⟨mul_pos hR hp.1, mem_univ _⟩
  have hg : Continuous fun p : ℝ × ℂ => (coneScaleRadius γ (hcirc ω) b * p.1,
      ((coneScaleRadius γ (hcirc ω) b : ℝ) : ℂ) * p.2) :=
    (continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)
  exact ((hω.comp hg.continuousOn hmaps).add continuousOn_const).sub continuousOn_const

/-- **The radial law of `h^b`** (Definition 2.1): the radial process is a measurable function of the circle average
process, whose law is that of `h` by `QuantumConeScalingInput`. -/
theorem radial_law_rescaledCircle (hscale : QuantumConeScalingInput) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) {b : ℝ} (hb : 0 < b) :
    ∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - γ) ν ∧
      P.map (fun ω => radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) =
        quantumConeRadialLaw γ ν := by
  obtain ⟨ν, hν, hlaw⟩ := hcone.radial_law
  refine ⟨ν, hν, ?_⟩
  let G : (Ioi (0 : ℝ) × ℂ → ℝ) → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) := fun p =>
    (fun t => p (⟨Real.exp (-(t : ℝ)), mem_Ioi.2 (Real.exp_pos _)⟩, 0),
      fun s => p (⟨Real.exp (s : ℝ), mem_Ioi.2 (Real.exp_pos _)⟩, 0))
  have hG : Measurable G :=
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _).prodMk (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
  have hF := aemeasurable_circleProcess_rescaledCircle hscale hγ hγ2 hcone hb
  have hF0 := measurable_circleProcess_of_isQuantumCone hcone
  have h1 : (fun ω => radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) =
      G ∘ fun ω => circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b) := rfl
  have h2 : (fun ω => radialProcess (hcirc ω)) = G ∘ fun ω => circleProcess (hcirc ω) := rfl
  rw [h1, ← AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hF,
    hscale γ hγ hγ2 Ω P hC hcirc inferInstance hcone b hb, Measure.map_map hG hF0, ← h2, hlaw]

end Sec1

/-- **`ConeEnvironmentScalingStep`** (eq:scale-invariance-of-field-and-eta, lines 3286-3293) from DMS14 Prop 4.13(i)
(`QuantumConeScalingInput`), Fact 2.2 (`LQGMeasurePropertiesStmt`), the SLE-model inputs (scale invariance,
reparametrization, independence of a smaller σ-algebra) and the requested `RescaledEnvironmentInput`. -/
theorem coneEnvironmentScalingStep_of_inputs (𝒮 : SpaceFillingSLEModel) (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) (hSc : SLEScaleInvarianceInput 𝒮) (hRe : SLEReparametrizationInput 𝒮)
    (hMo : SLEIndepMonoInput 𝒮) (hin : RescaledEnvironmentInput 𝒮) : ConeEnvironmentScalingStep 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS b hb
  obtain ⟨hC', clock', hpair, hcircm, hind, hlat, hsig, ⟨R₀, hR₀m, hR₀⟩, hclock, hmot⟩ :=
    hin γ hγ hγ2 Ω S hS b hb
  have := hS.isProbabilityMeasure
  have hpos : ∀ᵐ ω ∂S.P, 0 < coneScaleRadius γ (S.hcirc ω) b :=
    Sec1.ae_coneScaleRadius_pos hscale hγ hγ2 hS.isQuantumCone hb
  have hκ : (4 : ℝ) < 16 / γ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  refine ⟨S.rescaleWith γ b hC' clock', ⟨hS.isProbabilityMeasure, ?_, ?_, ?_, ?_, hclock, hmot⟩, rfl,
    ae_of_all _ fun _ _ => rfl, ae_of_all _ fun ω s => rescaledPair_apply b (S.bm ω) s,
    ae_of_all _ fun _ => rfl⟩
  · -- `isQuantumCone`
    obtain ⟨ν, hν, hrad⟩ := Sec1.radial_law_rescaledCircle hscale hγ hγ2 hS.isQuantumCone hb
    exact { measurable_pairing := hpair
            measurable_circle := hcircm
            ae_continuousOn_circle := Sec1.ae_continuousOn_rescaledCircle hS.isQuantumCone hpos
            radial_law := ⟨ν, hν, hrad⟩
            indep := hind
            lateral_law := hlat }
  · -- `isLQGMeasure`: Fact 2.2 III, IV
    have h := coneLQGScalingStep_of_steps h22 (coneScaleRadiusPosStep_of_input hscale) γ hγ hγ2 Ω S.P S.hC
      S.hcirc S.μ ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩ b hb
    exact h.mono fun _ hω => hω.2
  · -- `isSLE`: reparametrization `s ↦ b s`, scaling by the `σ(h)`-measurable `R_b⁻¹`, then `σ(h^b) ≤ σ(h)`
    let R' : Ω → ℝ := fun ω => if 0 < R₀ ω then R₀ ω else 1
    have hR'm : Measurable[S.fieldSigma] R' :=
      Measurable.ite (measurableSet_lt measurable_const hR₀m) hR₀m measurable_const
    have hR'pos : ∀ ω, 0 < R' ω := fun ω => by
      by_cases h : 0 < R₀ ω
      · simp only [R', h, ↓reduceIte]
      · simp only [R', h, ↓reduceIte, zero_lt_one]
    have hR'ae : ∀ᵐ ω ∂S.P, R' ω = coneScaleRadius γ (S.hcirc ω) b := by
      filter_upwards [hR₀, hpos] with ω h1 h2
      simp only [R', h1, h2, ↓reduceIte]
    have hη1 : 𝒮.IsSLE S.P S.fieldSigma (16 / γ ^ 2) (fun ω s => S.η ω (b * s)) :=
      hRe Ω _ S.P S.fieldSigma _ S.η _ hκ hS.isSLE (ae_of_all _ fun _ =>
        ⟨Homeomorph.mulLeft₀ b hb.ne', fun x y hxy => mul_lt_mul_of_pos_left hxy hb, rfl⟩)
    have hη2 := hSc Ω _ S.P S.fieldSigma _ _ hκ hη1 (fun ω => (R' ω)⁻¹) hR'm.inv
      (fun ω => inv_pos.2 (hR'pos ω))
    have hη3 : 𝒮.IsSLE S.P S.fieldSigma (16 / γ ^ 2) (S.rescaleWith γ b hC' clock').η :=
      hRe Ω _ S.P S.fieldSigma _ _ _ hκ hη2 (by
        filter_upwards [hR'ae] with ω hω
        refine ⟨Homeomorph.refl ℝ, strictMono_id, ?_⟩
        funext s
        simp [hω, MatedCRTEnv.rescaleWith])
    exact hMo Ω _ S.P S.fieldSigma _ _ _ hκ hη3 hsig
  · -- `isAreaParametrized`: deterministic
    filter_upwards [hS.isAreaParametrized, hpos] with ω hω hR
    exact Sec1.isAreaParametrized_rescale hR hb hω

end MatedCRT
