import MatedCRT.FirstPass.Derived.HN9OfWindowCharts

/-!
# The chart field `h ∘ φ + Q log |φ'|` of a window

For an inverse chart `ψ` of a bounded open set `U` at `z` (`IsInverseChart U z ψ`), with conformal map
`φ = ψ⁻¹ : 𝔻 → U`, the chart field of a distribution `h` on `ℂ` is the field `h ∘ φ + Q log |φ'|` on the unit disc
(Berestycki–Gwynne (2020), proof of Lemma 7.18, with the coordinate change (2.1)). Its pairing with a test function
`f` on `𝔻` is, by the change of variables `w = ψ(x)` with Jacobian `|ψ'(x)|²`,
`⟨h ∘ φ, f⟩ = ⟨h, (f ∘ ψ) |ψ'|²⟩`, plus `Q ∫ log |φ'(w)| f(w) dw`.

* `chartTestFun U ψ f`: the function `x ↦ f(ψ x) |ψ'(x)|²` on `U`, extended by `0`. For an inverse chart of a
  bounded open set it is smooth with compact support in `U` (`contDiff_chartTestFun`,
  `hasCompactSupport_chartTestFun`): its support lies in the compact set `closure U ∩ ψ⁻¹(tsupport f)`, which is
  inside `U` because `ψ` maps the frontier of `U` to the unit circle.
* `chartTest`: the corresponding test function on `ℂ`.
* `chartFieldPairing γ h U z ψ`: the pairings `f ↦ ⟨h, chartTest f⟩ + Q ∫ log |φ'| f` of the chart field with the
  test functions on the unit disc (`0` if `ψ` is not an inverse chart of a bounded open set).
* `windowChartField γ a u b ψ q`: the chart field of the window `(a, u, b)` of a joint-limit sample, for the field
  recovered from its coordinates (`LQGMetric.pairJInv`).

The input `BG20ChartFieldInput` is `BG20WindowChartInput` with the chart fields given by `windowChartField`
(`bg20WindowChartInput_of_chartField`); it implies the premise `hN9` exactly as typed and the counted forms of
Theorems 1.4 and 1.6.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- The open unit disc, as an open set of `ℂ`. -/
def unitDiscOpens : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- The conformal map `φ : 𝔻 → U` of an inverse chart `ψ`: the inverse of `ψ` on `U`. -/
noncomputable def chartMap (U : Set ℂ) (ψ : C(ℂ, ℂ)) : ℂ → ℂ :=
  Function.invFunOn ψ U

/-- The transported function `x ↦ f(ψ x) |ψ'(x)|²` on `U`, extended by `0` outside `U`. -/
noncomputable def chartTestFun (U : Set ℂ) (ψ : C(ℂ, ℂ)) (f : ℂ → ℝ) : ℂ → ℝ :=
  U.indicator fun x => f (ψ x) * ‖deriv ψ x‖ ^ 2

section ChartTest

variable {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}

/-- The points of the closure of `U` which `ψ` maps into a compact subset of the open disc form a compact subset of
`U`. -/
theorem isCompact_closure_inter_preimage (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ Metric.ball 0 1) :
    IsCompact (closure U ∩ ψ ⁻¹' K) ∧ closure U ∩ ψ ⁻¹' K ⊆ U := by
  refine ⟨hUb.isCompact_closure.inter_right (hK.isClosed.preimage ψ.continuous), ?_⟩
  rintro x ⟨hxc, hxK⟩
  by_contra hxU
  have hxf : x ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨hxc, hxU⟩
  have hs : ψ x ∈ Metric.sphere (0 : ℂ) 1 := hψ.image_frontier ▸ mem_image_of_mem ψ hxf
  have hb := hKD hxK
  rw [Metric.mem_sphere, dist_zero_right] at hs
  rw [Metric.mem_ball, dist_zero_right, hs] at hb
  exact lt_irrefl _ hb

theorem chartTestFun_eq_zero_of_notMem (f : ℂ → ℝ) {x : ℂ} (hx : x ∉ closure U ∩ ψ ⁻¹' tsupport f) :
    chartTestFun U ψ f x = 0 := by
  by_contra hne
  have hxU : x ∈ U := by
    by_contra hxU
    exact hne (indicator_of_notMem hxU _)
  rw [chartTestFun, indicator_of_mem hxU] at hne
  have hf : f (ψ x) ≠ 0 := fun h => hne (by rw [h, zero_mul])
  exact hx ⟨subset_closure hxU, subset_tsupport f hf⟩

theorem hasCompactSupport_chartTestFun (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (f : 𝓓(unitDiscOpens, ℝ)) :
    HasCompactSupport (chartTestFun U ψ f) :=
  HasCompactSupport.intro (isCompact_closure_inter_preimage hψ hU hUb f.hasCompactSupport
    f.tsupport_subset).1 fun _ hx => chartTestFun_eq_zero_of_notMem _ hx

theorem contDiff_chartTestFun (hψ : IsInverseChart U z ψ) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (f : 𝓓(unitDiscOpens, ℝ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chartTestFun U ψ f) := by
  have hψd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ U := (hψ.differentiableOn.contDiffOn hU).restrict_scalars ℝ
  have hψ'd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv ψ) U :=
    ((hψ.differentiableOn.deriv hU).contDiffOn hU).restrict_scalars ℝ
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => f (ψ x) * ‖deriv ψ x‖ ^ 2) U :=
    (f.contDiff.comp_contDiffOn hψd).mul ((contDiff_norm_sq ℝ).comp_contDiffOn hψ'd)
  obtain ⟨hK, hKU⟩ := isCompact_closure_inter_preimage hψ hU hUb f.hasCompactSupport f.tsupport_subset
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · refine (hG.contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy
    exact indicator_of_mem hy _
  · have hxK : x ∉ closure U ∩ ψ ⁻¹' tsupport f := fun h => hx (hKU h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact chartTestFun_eq_zero_of_notMem _ hy

/-- The transported test function `(f ∘ ψ) |ψ'|²` on `ℂ`, for an inverse chart `ψ` of a bounded open set. -/
noncomputable def chartTest (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (f : 𝓓(unitDiscOpens, ℝ)) : LQGMetric.TestC :=
  ⟨chartTestFun U ψ f, contDiff_chartTestFun hψ hU hUb f, hasCompactSupport_chartTestFun hψ hU hUb f,
    fun _ _ => trivial⟩

theorem chartTest_apply (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (f : 𝓓(unitDiscOpens, ℝ)) (x : ℂ) :
    chartTest hψ hU hUb f x = chartTestFun U ψ f x :=
  rfl

end ChartTest

open Classical in
/-- **The chart field `h ∘ φ + Q log |φ'|`**, as its pairings with the test functions on the unit disc:
`f ↦ ⟨h, (f ∘ ψ) |ψ'|²⟩ + Q ∫ log |φ'(w)| f(w) dw` for an inverse chart `ψ` of a bounded open set `U` at `z`, with
`φ = chartMap U ψ` (and `0` otherwise). -/
noncomputable def chartFieldPairing (γ : ℝ) (h : LQGMetric.DistC) (U : Set ℂ) (z : ℂ) (ψ : C(ℂ, ℂ))
    (f : 𝓓(unitDiscOpens, ℝ)) : ℝ :=
  if hc : IsInverseChart U z ψ ∧ IsOpen U ∧ Bornology.IsBounded U then
    h (chartTest hc.1 hc.2.1 hc.2.2 f) + MatedCRTHarmonic.MatedCRT.lqgQ γ * ∫ w, Real.log ‖deriv (chartMap U ψ) w‖ * f w
  else 0

/-- The chart field of the window `(a, u, b)` of a joint-limit sample `q` for the inverse chart `ψ`, for the field
`pairJInv ⊤ q.1.1.1` with the field coordinates of `q`. -/
noncomputable def windowChartField (γ a u b : ℝ) (ψ : C(ℂ, ℂ)) (q : JointSample) :
    𝓓(unitDiscOpens, ℝ) → ℝ :=
  chartFieldPairing γ (LQGMetric.pairJInv ⊤ q.1.1.1) (windowDomain q.1.2 a u b) (q.1.2 u) ψ

/-- **Literature input (Berestycki–Gwynne (2020), Lemma 7.20 without the time change, and Lemma 7.21, on the joint
limit, with inverse charts and chart fields).** As `BG20WindowChartInput`, with the chart fields of the two windows
given by `windowChartField` (the field `h ∘ φ + Q log |φ'|` of Berestycki–Gwynne, as its pairings with test
functions on the unit disc), so that the existential objects are the inverse charts `ψ`, `ψ'` and the kernel `K` of
the chart Liouville Brownian motion. For times `a < u < b < a' < u' < b'`:

* almost surely `ψ` and `ψ'` are inverse charts of the two windows;
* `K` and the chart fields and window chart laws depend measurably on the sample (Borel choice of the charts);
* (Lemma 7.20 without the time change; Berestycki (2015), Theorem 1.3) almost surely the chart image of the
  Liouville Brownian law of the field from `η(u)` is `K` of the chart field, and likewise for the second window;
* (Lemma 7.21) the pairs (chart field, window chart law) of the two windows are independent. -/
def BG20ChartFieldInput (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    ∀ ν'' : Measure JointSample, IsProbabilityMeasure ν'' →
    (∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), interpWalkLaw S η' (ε n) ω) ∂S.P)
        atTop (𝓝 (∫ q, f q ∂ν''))) →
    (∀ᵐ q ∂ν'', ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z) →
    ∀ a u b a' u' b' : ℝ, a < u → u < b → b < a' → a' < u' → u' < b' →
    ∃ (K : (𝓓(unitDiscOpens, ℝ) → ℝ) → Measure (ContinuousPath ℂ)) (ψ ψ' : JointSample → C(ℂ, ℂ)),
      (∀ᵐ q ∂ν'', IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) (ψ q)) ∧
      (∀ᵐ q ∂ν'', IsInverseChart (windowDomain q.1.2 a' u' b') (q.1.2 u') (ψ' q)) ∧
      Measurable K ∧ Measurable (fun q => windowChartField γ a u b (ψ q) q) ∧
      Measurable (fun q => windowChartField γ a' u' b' (ψ' q) q) ∧
      Measurable (fun q => windowChartLaw a u b (ψ q) q) ∧
      Measurable (fun q => windowChartLaw a' u' b' (ψ' q) q) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a u b (ψ q) q = K (windowChartField γ a u b (ψ q) q)) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a' u' b' (ψ' q) q = K (windowChartField γ a' u' b' (ψ' q) q)) ∧
      IndepFun (fun q => (windowChartField γ a u b (ψ q) q, windowChartLaw a u b (ψ q) q))
        (fun q => (windowChartField γ a' u' b' (ψ' q) q, windowChartLaw a' u' b' (ψ' q) q)) ν''

/-- The input with chart fields implies `BG20WindowChartInput` (take `F` the space of pairings with test functions
on the unit disc and the chart fields `windowChartField`). -/
theorem bg20WindowChartInput_of_chartField {𝒮 : SpaceFillingSLEModel}
    (hC : BG20ChartFieldInput 𝒮) : BG20WindowChartInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
    hau hub hba' ha'u' hu'b'
  obtain ⟨K, ψ, ψ', hψ, hψ', hK, hhD, hhD', hm, hm', hb, hb', hind⟩ :=
    hC γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
      hau hub hba' ha'u' hu'b'
  exact ⟨𝓓(unitDiscOpens, ℝ) → ℝ, inferInstance, K, ψ, ψ', fun q => windowChartField γ a u b (ψ q) q,
    fun q => windowChartField γ a' u' b' (ψ' q) q, hψ, hψ', hK, hhD, hhD', hm, hm', hb, hb', hind⟩

/-- The input with chart fields implies `BG20LocalSpeedRecoveryInput`. -/
theorem bg20LocalSpeedRecoveryInput_of_chartField {𝒮 : SpaceFillingSLEModel}
    (hC : BG20ChartFieldInput 𝒮) : BG20LocalSpeedRecoveryInput 𝒮 :=
  bg20LocalSpeedRecoveryInput_of_chartLaws
    (bg20ChartLawInput_of_jointChartLaws (bg20JointChartLawInput_of_windowCharts
      (bg20WindowChartInput_of_chartField hC)))

/-- **Berestycki–Gwynne (2020), Lemma 7.18, from the chart forms of Lemmas 7.20 and 7.21 with inverse charts and
chart fields.** The premise `hN9` of `randomWalkToLBMStmt_of_markovLimit_derived`, exactly as typed, from
`BG20ChartFieldInput`. -/
theorem hN9_of_bg20ChartField {𝒮 : SpaceFillingSLEModel} (hC : BG20ChartFieldInput 𝒮) :
    ∀ γ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → (∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ E : Ω → LQGData, Measurable E → ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      ∀ ν' : Measure (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily), IsProbabilityMeasure ν' →
      (∀ f : (((LQGMetric.CoordJ → ℝ) × LQGData) × PathLawFamily) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f ((LQGMetric.pairJ ⊤ (H ω), E ω), interpWalkLaw S η' (ε n) ω) ∂S.P) atTop
          (𝓝 (∫ p, f p ∂ν'))) →
      (∀ᵐ p ∂ν', ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ z, p.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ p.1.1) z) →
      ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ ∀ᵐ p ∂ν', ∀ z, p.2 z = LatticeProb.timeScalePathKernel c₀ (lbmPathLawField γ p.1.1) z :=
  hN9_of_bg20LocalSpeedRecovery (bg20LocalSpeedRecoveryInput_of_chartField hC)

/-- **Theorem 2.11 (Berestycki–Gwynne (2020), Theorem 1.2)** with the premises `h1 h2 hN4 h10` and
`BG20ChartFieldInput` in place of `hN9`. -/
theorem randomWalkToLBMStmt_of_markovLimit_bg20ChartField {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮) (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hC : BG20ChartFieldInput 𝒮) :
    RandomWalkToLBMStmt 𝒮 :=
  randomWalkToLBMStmt_of_markovLimit_bg20LocalSpeedRecovery h1 h2 hN4 h10
    (bg20LocalSpeedRecoveryInput_of_chartField hC)

/-- **Theorem 1.4** in the counted form `closed_1_4_quantumConeScaling_coneDimension`, with the premise `hN9`
(Berestycki–Gwynne (2020), Lemma 7.18) of `closed_1_4_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`
replaced by `BG20ChartFieldInput`; the remaining premises are `h1 h2 hN4 h10 hC`. Same conclusion. -/
theorem closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20ChartField
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hC : BG20ChartFieldInput 𝒮) :
    ConvergenceOfIDLAStmt 𝒮 :=
  closed_1_4_quantumConeScaling_coneDimension_markovLimit_bg20LocalSpeedRecovery ν h1 h2 hN4 h10
    (bg20LocalSpeedRecoveryInput_of_chartField hC)

/-- **Theorem 1.6** in the counted form `closed_1_6_quantumConeScaling_coneDimension`, with the premise `hN9`
(Berestycki–Gwynne (2020), Lemma 7.18) of `closed_1_6_quantumConeScaling_coneDimension_markovLimit_noHN5_noHN8`
replaced by `BG20ChartFieldInput`; the remaining premises are `h1 h2 hN4 h10 hC`. Same conclusion. -/
theorem closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20ChartField
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hN4 : GMS21UniformStartInput 𝒮)
    (h10 : HasReferenceEnvironments 𝒮) (hC : BG20ChartFieldInput 𝒮) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  closed_1_6_quantumConeScaling_coneDimension_markovLimit_bg20LocalSpeedRecovery ν h1 h2 hN4 h10
    (bg20LocalSpeedRecoveryInput_of_chartField hC)

end MatedCRT
