import MatedCRT.FirstPass.Derived.ChartLimitTransport
import MatedCRT.FirstPass.Derived.RandomWalkToLBMStmtOfConeInputs
import MatedCRT.FirstPass.Derived.RandomWalkToLBMIdentificationAssembly
import MatedCRT.FirstPass.Derived.ValidApproximantBallBound
import MatedCRT.FirstPass.Derived.HN9OfChartField
import MatedCRT.FirstPass.Derived.WindowInverseChart
import MatedCRT.FirstPass.Derived.ProbabilityMeasurePolish
import MatedCRT.FirstPass.Derived.TimeScaledLawField
import MatedCRT.FirstPass.Derived.LQGDataSpace

/-!
# The chart image of Liouville Brownian motion is a function of the chart field

Steps R3-R6 of the Revuz route to Berestycki (2015), Theorem 1.3 (*Diffusion in planar Liouville quantum gravity*,
arXiv:1301.3356), and the form `(I3)` of the chart input of the joint limit (`BG20ChartFieldInput`, conjuncts
`windowLBMChartLaw γ a u b (ψ q) q = K (windowChartField γ a u b (ψ q) q)`).

From Lévy's conformal invariance (`LevyConformalChartStmt`) the chart image of the Liouville Brownian motion of the
field from `z`, stopped at its exit from `U`, is the weak limit of the transported approximating laws
`chartTransportApproxLaw` from `ψ(z) = 0` (`tendsto_integral_chartTransportApproxLaw_of_levy`). What remains of
Berestycki's theorem is that this limit is a measurable function of the chart field `h ∘ φ + Q log |φ'|` alone,
simultaneously for all inverse charts (`ChartFieldLBMLimitStmt`). On the Revuz route it splits into

* `LQGMeasureChartStmt` (step R3): the LQG measure of the chart field is the image under `ψ` of the LQG measure of
  the field restricted to `U`, simultaneously for all inverse charts (Duplantier–Sheffield (2011), Proposition 2.1;
  Sheffield–Wang (2016), Theorem 1.1);
* `ChartTransportRevuzStmt` (steps R2, R4-R6): the transported approximating laws converge to the time change of
  Brownian motion killed on exiting the unit disc by the positive continuous additive functional whose Revuz measure
  is that image measure, a measurable function of the measure;

and `chartFieldLBMLimitStmt_of_lqgMeasureChart_of_chartTransportRevuz` combines them.

## Main statements

* `chartStopPath_timeScalePath_any`, `map_chartStopPath_map_timeScalePath_any`: the chart image commutes with every
  linear time change (also `c = 0`).
* `continuousPath_measure_eq_of_integral_eq`: laws of continuous planar paths are determined by bounded continuous
  tests.
* `ae_chartLaw_lbmPathLawField_eq_of_chartTransportLimit`: in a valid environment, almost surely, for every bounded
  open `U` and inverse chart `ψ` of `U` at `z`, the chart image of the rescaled Liouville Brownian law of the field
  from `z` is the time scaling by the median `m_γ` of `K₀` of the chart field.
* `ae_windowLBMChartLaw_eq_of_chartTransportLimit`: the same on a joint weak limit `ν''`, for the window `(a, u, b)`
  and its normalized inverse chart `windowChart a u b η`.
* `exists_kernel_ae_windowLBMChartLaw_eq`: from `LevyConformalChartStmt` and `ChartFieldLBMLimitStmt`, a measurable
  kernel `K` with the conjunct `(I3)` for every window.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData)

namespace MatedCRT

/-! ### Chart images and linear time changes -/

/-- The chart image of a path commutes with every linear time change, including the constant time change `c = 0`. -/
theorem chartStopPath_timeScalePath_any (U : Set ℂ) (ψ : C(ℂ, ℂ)) (c : ℝ≥0) (f : ContinuousPath ℂ) :
    chartStopPath U ψ (timeScalePath c f) = timeScalePath c (chartStopPath U ψ f) := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : exitClamp (ContinuousPath.exitTime U f) 0 = 0 := by
      by_cases hτ : ContinuousPath.exitTime U f = ⊤
      · simp only [exitClamp_apply, hτ, ↓reduceIte]
      · simp only [exitClamp_apply, hτ, ↓reduceIte]
        exact min_eq_left zero_le
    ext t
    simp only [chartStopPath, stopAtExitTime, ContinuousMap.comp_apply, timeScalePath_apply, zero_mul, h0]
  · exact chartStopPath_timeScalePath U ψ hc f

/-- The chart image of a time-changed law is the time change of the chart image, for every `c ≥ 0`. -/
theorem map_chartStopPath_map_timeScalePath_any (U : Set ℂ) (hU : IsOpen U) (ψ : C(ℂ, ℂ)) (c : ℝ≥0)
    (μ : Measure (ContinuousPath ℂ)) :
    (μ.map (timeScalePath c)).map (chartStopPath U ψ) =
      (μ.map (chartStopPath U ψ)).map (timeScalePath c) := by
  rw [Measure.map_map (measurable_chartStopPath U hU ψ) (measurable_timeScalePath c),
    Measure.map_map (measurable_timeScalePath c) (measurable_chartStopPath U hU ψ)]
  congr 1
  funext f
  exact chartStopPath_timeScalePath_any U ψ c f

/-- **Laws of continuous planar paths are determined by bounded continuous tests.** Two Borel probability measures on
continuous planar paths with the same integrals of all bounded continuous functions are equal (the topology of
convergence in distribution on the laws of paths is Hausdorff). -/
theorem continuousPath_measure_eq_of_integral_eq {μ ν : Measure (ContinuousPath ℂ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ f : ContinuousPath ℂ →ᵇ ℝ, ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν := by
  let P : ProbabilityMeasure (ContinuousPath ℂ) := ⟨μ, inferInstance⟩
  let Q : ProbabilityMeasure (ContinuousPath ℂ) := ⟨ν, inferInstance⟩
  have h1 : Tendsto (fun _ : ℕ => P) atTop (𝓝 Q) := by
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun f => ?_
    change Tendsto (fun _ : ℕ => ∫ x, f x ∂μ) atTop (𝓝 (∫ x, f x ∂ν))
    rw [h f]
    exact tendsto_const_nhds
  exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique tendsto_const_nhds h1)

/-! ### The remaining coordinate change -/

/-- **The transported approximating laws converge to `K₀` of the chart field.** At the field coordinates `x`: for every
bounded open set `U` and every inverse chart `ψ` of `U` at `z`, the transported approximating laws
`chartTransportApproxLaw γ h n U ψ 0` (`h` the circle-average process of `x`; Brownian motion from `ψ(z) = 0` in the
unit disc run with the rate `(ε_n^{γ²/2} e^{γ h_{ε_n}(φ v)} + ε_n) |φ'(v)|²`, `φ = ψ⁻¹`, and stopped at its exit from
the disc) converge weakly to `K₀` of the chart field `h ∘ φ + Q log |φ'|` (`chartFieldPairing`). -/
def ChartTransportLimit (γ : ℝ) (K₀ : (𝓓(unitDiscOpens, ℝ) → ℝ) → ProbabilityMeasure (ContinuousPath ℂ))
    (x : LQGMetric.CoordJ → ℝ) : Prop :=
  ∀ (U : Set ℂ) (z : ℂ) (ψ : C(ℂ, ℂ)), IsOpen U → Bornology.IsBounded U → IsInverseChart U z ψ →
    ∀ f : ContinuousPath ℂ →ᵇ ℝ,
      Tendsto (fun n : ℕ => ∫ W, f W ∂chartTransportApproxLaw γ (coordCircleAverage x) n U ψ 0) atTop
        (𝓝 (∫ W, f W ∂(K₀ (chartFieldPairing γ (LQGMetric.pairJInv ⊤ x) U z ψ) : Measure (ContinuousPath ℂ))))

/-- **GAP (steps R2-R6): the chart image of Liouville Brownian motion is the Liouville Brownian motion of the chart
field.** There is a Borel map `K₀` from fields on the unit disc (pairings with the test functions on the disc) to laws
of continuous paths such that, in every valid environment and for every measurable version `H` of the field, almost
surely, simultaneously for all bounded open sets `U` and inverse charts `ψ` of `U` at `z`, the transported
approximating laws from `ψ(z) = 0` converge weakly to `K₀` of the chart field `h ∘ φ + Q log |φ'|`
(`ChartTransportLimit`).

Source: Berestycki (2015), Theorem 1.3 (the image under a conformal map of Liouville Brownian motion, up to its exit
time, is the Liouville Brownian motion of the field `h ∘ φ + Q log |φ'|`), whose proof (§2, steps C1-C5 of the
basis approximation) identifies the limit of the transported clocks; simultaneity in the chart: Sheffield–Wang (2016),
Theorem 1.1, for the LQG measures. On the Revuz route it follows from `LQGMeasureChartStmt` and
`ChartTransportRevuzStmt` (`chartFieldLBMLimitStmt_of_lqgMeasureChart_of_chartTransportRevuz`). -/
def ChartFieldLBMLimitStmt (γ : ℝ) : Prop :=
  ∃ K₀ : (𝓓(unitDiscOpens, ℝ) → ℝ) → ProbabilityMeasure (ContinuousPath ℂ), Measurable K₀ ∧
    ∀ (𝒮 : SpaceFillingSLEModel) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ᵐ ω ∂S.P, ChartTransportLimit γ K₀ (LQGMetric.pairJ ⊤ (H ω))

/-- **GAP (step R3): the coordinate change of the LQG measure, simultaneously for all inverse charts.** There is a
Borel map `M` from fields on the unit disc to measures such that, in every valid environment and for every measurable
version `H` of the field, almost surely, simultaneously for all bounded open sets `U` and inverse charts `ψ` of `U`
at `z`, `M` of the chart field `h ∘ φ + Q log |φ'|` is the image under `ψ` of the LQG measure `μ_h` restricted to
`U`.

Source: Duplantier–Sheffield (2011), *Liouville quantum gravity and KPZ*, Proposition 2.1 (the coordinate change
`μ_{h ∘ φ + Q log |φ'|} = φ^* μ_h` for a fixed conformal map); Sheffield–Wang (2016), *Field-measure correspondence in
Liouville quantum gravity almost surely commutes with all conformal maps simultaneously*, Theorem 1.1 (almost surely
for all conformal maps at once). -/
def LQGMeasureChartStmt (γ : ℝ) : Prop :=
  ∃ M : (𝓓(unitDiscOpens, ℝ) → ℝ) → Measure ℂ, Measurable M ∧
    ∀ (𝒮 : SpaceFillingSLEModel) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ᵐ ω ∂S.P, ∀ (U : Set ℂ) (z : ℂ) (ψ : C(ℂ, ℂ)), IsOpen U → Bornology.IsBounded U → IsInverseChart U z ψ →
      M (chartFieldPairing γ (LQGMetric.pairJInv ⊤ (LQGMetric.pairJ ⊤ (H ω))) U z ψ) =
        ((S.μ ω).restrict U).map ψ

/-- **GAP (steps R2, R4-R6): the transported approximating laws converge to the time change of killed Brownian motion
by the additive functional with the transported Revuz measure.** There is a Borel map `L` from measures to laws of
continuous paths such that, in every valid environment and for every measurable version `H` of the field, almost
surely, simultaneously for all bounded open sets `U` and inverse charts `ψ` of `U` at `z`, the transported
approximating laws from `ψ(z) = 0` converge weakly to `L` of the image under `ψ` of the LQG measure `μ_h` restricted to
`U`.

Here `L(ν)` is the law of planar Brownian motion from `0` killed on exiting the unit disc and time-changed by the
positive continuous additive functional whose Revuz measure is `ν`. Sources: the Liouville clock is the positive
continuous additive functional with Revuz measure `μ_h` (Garban–Rhodes–Vargas (2016), *Liouville Brownian motion*,
§2; in the repository for whole-plane Brownian motion, `ae_lintegral_revuz_eq_of_isValid`); under the chart, by Lévy's
theorem and the conformal invariance of the Green function of a domain, it becomes the additive functional of
Brownian motion killed on exiting the disc with Revuz measure `ψ_* (μ_h|_U)`; a smooth measure determines its additive
functional (Fukushima–Oshima–Takeda (2011), Theorem 5.1.4) and hence the law of the time change (§6.2). -/
def ChartTransportRevuzStmt (γ : ℝ) : Prop :=
  ∃ L : Measure ℂ → ProbabilityMeasure (ContinuousPath ℂ), Measurable L ∧
    ∀ (𝒮 : SpaceFillingSLEModel) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
    ∀ᵐ ω ∂S.P, ∀ (U : Set ℂ) (z : ℂ) (ψ : C(ℂ, ℂ)), IsOpen U → Bornology.IsBounded U → IsInverseChart U z ψ →
      ∀ f : ContinuousPath ℂ →ᵇ ℝ,
        Tendsto (fun n : ℕ => ∫ W, f W ∂chartTransportApproxLaw γ
            (coordCircleAverage (LQGMetric.pairJ ⊤ (H ω))) n U ψ 0) atTop
          (𝓝 (∫ W, f W ∂(L (((S.μ ω).restrict U).map ψ) : Measure (ContinuousPath ℂ))))

/-- **The coordinate change of the Liouville Brownian motion from the Revuz route.** The coordinate change of the LQG
measure (`LQGMeasureChartStmt`) and the identification of the limit of the transported approximating laws through
the transported Revuz measure (`ChartTransportRevuzStmt`) give `ChartFieldLBMLimitStmt`, with `K₀ = L ∘ M`. -/
theorem chartFieldLBMLimitStmt_of_lqgMeasureChart_of_chartTransportRevuz {γ : ℝ} (h3 : LQGMeasureChartStmt γ)
    (h56 : ChartTransportRevuzStmt γ) : ChartFieldLBMLimitStmt γ := by
  obtain ⟨M, hM, hMeq⟩ := h3
  obtain ⟨L, hL, hLlim⟩ := h56
  refine ⟨fun g => L (M g), hL.comp hM, fun 𝒮 Ω _ S hS H hH hrep => ?_⟩
  filter_upwards [hMeq 𝒮 Ω S hS H hH hrep, hLlim 𝒮 Ω S hS H hH hrep] with ω h1 h2 U z ψ hU hUb hψ f
  have h := h2 U z ψ hU hUb hψ f
  rw [← h1 U z ψ hU hUb hψ] at h
  exact h

/-! ### The chart image of the rescaled Liouville Brownian law -/

/-- **The chart image of the rescaled Liouville Brownian law is a function of the chart field.** In a valid
environment at `0 < γ < 2`, from Lévy's conformal invariance and the convergence of the transported approximating laws
to `K₀` of the chart field: almost surely, for every bounded open set `U` and every inverse chart `ψ` of `U` at `z`,
the chart image `chartLaw` of the rescaled Liouville Brownian law `lbmPathLawField γ` of the field from `z` is the time
scaling by the median `m_γ` of `K₀` of the chart field. -/
theorem ae_chartLaw_lbmPathLawField_eq_of_chartTransportLimit {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hLevy : LevyConformalChartStmt) {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {K₀ : (𝓓(unitDiscOpens, ℝ) → ℝ) → ProbabilityMeasure (ContinuousPath ℂ)}
    (hK₀ : ∀ᵐ ω ∂S.P, ChartTransportLimit γ K₀ (LQGMetric.pairJ ⊤ (H ω))) :
    ∀ᵐ ω ∂S.P, ∀ (U : Set ℂ) (z : ℂ) (ψ : C(ℂ, ℂ)), IsOpen U → Bornology.IsBounded U → IsInverseChart U z ψ →
      chartLaw (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω))) z U ψ =
        (K₀ (chartFieldPairing γ (LQGMetric.pairJInv ⊤ (LQGMetric.pairJ ⊤ (H ω))) U z ψ) :
          Measure (ContinuousPath ℂ)).map (timeScalePath (lbmExitMedian γ).toNNReal) := by
  filter_upwards [hS.ae_lbmLawFieldSelection_eq hH hrep
      (FirstPass.Derived.lbmLawContinuity_of_isValid γ hγ hγ2 Ω S hS),
    hS.ae_isLQGClock_coordCircleAverage hrep, hS.ae_continuous_coordCircleAverage_dyadicScale hrep, hK₀]
    with ω hsel hclk hcont hK U z ψ hU hUb hψ
  obtain ⟨hg, hselz⟩ := hsel z
  have hlaw : (lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) z : Measure (ContinuousPath ℂ)) =
      ((planarBrownianMotion z).map (lbmContinuousPath (S.clock ω))).map
        (timeScalePath (lbmExitMedian γ).toNNReal) := by
    simp only [lbmPathLawField, rescaledLBMLawField_apply, ProbabilityMeasure.toMeasure_map, hselz]
    rfl
  have hprob : IsProbabilityMeasure (((planarBrownianMotion z).map (lbmContinuousPath (S.clock ω))).map
      (chartStopPath U ψ)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_chartStopPath U hU ψ).aemeasurable).2
      ((Measure.isProbabilityMeasure_map_iff hg).2 inferInstance)
  have heq : ((planarBrownianMotion z).map (lbmContinuousPath (S.clock ω))).map (chartStopPath U ψ) =
      (K₀ (chartFieldPairing γ (LQGMetric.pairJInv ⊤ (LQGMetric.pairJ ⊤ (H ω))) U z ψ) :
        Measure (ContinuousPath ℂ)) := by
    refine continuousPath_measure_eq_of_integral_eq fun f => ?_
    have h1 := tendsto_integral_chartTransportApproxLaw_of_levy hLevy hψ hU hUb hψ.mem (hclk z).1 (hclk z).2
      hcont f
    rw [hψ.apply_point] at h1
    have e1 : ∫ W, f W ∂(((planarBrownianMotion z).map (lbmContinuousPath (S.clock ω))).map
        (chartStopPath U ψ)) =
        ∫ b, f (chartStopPath U ψ (lbmContinuousPath (S.clock ω) b)) ∂planarBrownianMotion z := by
      rw [integral_map (measurable_chartStopPath U hU ψ).aemeasurable f.continuous.aestronglyMeasurable]
      exact integral_map hg (f.continuous.measurable.comp (measurable_chartStopPath U hU ψ)).aestronglyMeasurable
    rw [e1]
    exact tendsto_nhds_unique h1 (hK U z ψ hU hUb hψ f)
  rw [chartLaw, hlaw, map_chartStopPath_map_timeScalePath_any U hU ψ, heq]

/-! ### Transfer to the joint limit -/

private theorem isBounded_windowDomain_of_compact (η : C(ℝ, ℂ)) (a u b : ℝ) :
    Bornology.IsBounded (windowDomain η a u b) :=
  (isCompact_Icc.image η.continuous).isBounded.subset
    ((connectedComponentIn_subset _ _).trans interior_subset)

/-- **The chart image of the rescaled Liouville Brownian law on the joint limit.** Let `ν''` be a weak limit of the
joint laws of the field coordinates, a measurable coordinate `E`, the curve `η'` and a sequence of path-law families
`Z n`. If almost surely the transported approximating laws converge to `K₀` of the chart field (`ChartTransportLimit`),
then for the window `(a, u, b)` and its normalized inverse chart `windowChart a u b η` (given that the window chart law
of the Liouville Brownian law and the chart field are measurable functions of the sample), for `ν''`-almost every
sample whose window has an inverse chart at `η(u)`, the chart image of the rescaled Liouville Brownian law from
`η(u)` is the time scaling by `m_γ` of `K₀` of the chart field. -/
theorem ae_windowLBMChartLaw_eq_of_chartTransportLimit {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (hLevy : LevyConformalChartStmt) {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {K₀ : (𝓓(unitDiscOpens, ℝ) → ℝ) → ProbabilityMeasure (ContinuousPath ℂ)} (hK₀m : Measurable K₀)
    (hK₀ : ∀ᵐ ω ∂S.P, ChartTransportLimit γ K₀ (LQGMetric.pairJ ⊤ (H ω)))
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') {E : Ω → LQGData} (hE : Measurable E)
    {Z : ℕ → Ω → PathLawFamily} {ν'' : Measure JointSample} [IsProbabilityMeasure ν'']
    (hconv : ∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
        (𝓝 (∫ q, f q ∂ν'')))
    (a u b : ℝ)
    (hLm : Measurable fun q : JointSample => windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q)
    (hFm : Measurable fun q : JointSample => windowChartField γ a u b (windowChart a u b q.1.2) q) :
    ∀ᵐ q ∂ν'', (∃ ψ, IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) ψ) →
      windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q =
        (K₀ (windowChartField γ a u b (windowChart a u b q.1.2) q) : Measure (ContinuousPath ℂ)).map
          (timeScalePath (lbmExitMedian γ).toNNReal) := by
  have := hS.isProbabilityMeasure
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  set m : ℝ≥0 := (lbmExitMedian γ).toNNReal with hm
  let Data := ((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)
  have hD : Measurable fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    ((measurable_pairJ_top.comp hH).prodMk hE).prodMk hη'
  have hmarg : ν''.map Prod.fst = S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    FirstPass.Derived.map_fst_eq_map_of_tendsto_integral hD hconv
  -- the window chart law of the Liouville Brownian law, as a law of paths
  have hprob : ∀ q : JointSample,
      IsProbabilityMeasure (windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q) := fun q =>
    (Measure.isProbabilityMeasure_map_iff
      (measurable_chartStopPath _ (isOpen_windowDomain _ _ _ _) _).aemeasurable).2 inferInstance
  have hL' : Measurable fun q : JointSample =>
      (⟨windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q, hprob q⟩ :
        ProbabilityMeasure (ContinuousPath ℂ)) :=
    hLm.subtype_mk
  have hR' : Measurable fun q : JointSample =>
      timeScaleLaw m (K₀ (windowChartField γ a u b (windowChart a u b q.1.2) q)) :=
    (timeScaleLaw m).continuous.measurable.comp (hK₀m.comp hFm)
  have hEq : ∀ q : JointSample,
      ((⟨windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q, hprob q⟩ :
        ProbabilityMeasure (ContinuousPath ℂ)) =
          timeScaleLaw m (K₀ (windowChartField γ a u b (windowChart a u b q.1.2) q))) ↔
        windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q =
          (K₀ (windowChartField γ a u b (windowChart a u b q.1.2) q) :
            Measure (ContinuousPath ℂ)).map (timeScalePath m) := by
    intro q
    constructor
    · intro h
      have h' := congrArg ProbabilityMeasure.toMeasure h
      rw [coe_timeScaleLaw] at h'
      exact h'
    · intro h
      apply ProbabilityMeasure.toMeasure_injective
      rw [coe_timeScaleLaw]
      exact h
  -- the good set of samples, and its trace on the data
  let T : Set JointSample :=
    {q | q.1.2 ∈ {η : C(ℝ, ℂ) | ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ}}ᶜ ∪
      {q | (⟨windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q, hprob q⟩ :
        ProbabilityMeasure (ContinuousPath ℂ)) =
          timeScaleLaw m (K₀ (windowChartField γ a u b (windowChart a u b q.1.2) q))}
  have hTm : MeasurableSet T :=
    ((measurable_snd.comp measurable_fst) (measurableSet_setOf_exists_isInverseChart a u b)).compl.union
      ((hL'.prodMk hR')
        (isClosed_diagonal : IsClosed (diagonal (ProbabilityMeasure (ContinuousPath ℂ)))).measurableSet)
  let p₀ : PathLawFamily :=
    ContinuousMap.const ℂ ⟨Measure.dirac (0 : ContinuousPath ℂ), inferInstance⟩
  let T' : Set Data := (fun d : Data => ((d, p₀) : JointSample)) ⁻¹' T
  have hT'm : MeasurableSet T' := (measurable_id.prodMk measurable_const) hTm
  have hω : ∀ᵐ ω ∂S.P, (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) ∈ T' := by
    filter_upwards [ae_chartLaw_lbmPathLawField_eq_of_chartTransportLimit hγ hγ2 hS hLevy hH hrep hK₀]
      with ω hω
    by_cases hIC : ∃ ψ, IsInverseChart (windowDomain (η' ω) a u b) (η' ω u) ψ
    · right
      obtain ⟨ψ, hψ⟩ := hIC
      exact (hEq _).2 (hω (windowDomain (η' ω) a u b) (η' ω u) (windowChart a u b (η' ω))
        (isOpen_windowDomain _ _ _ _) (isBounded_windowDomain_of_compact _ _ _ _)
        (isInverseChart_windowChart hψ))
    · left
      exact hIC
  have hdata : ∀ᵐ d ∂(S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data)), d ∈ T' :=
    (ae_map_iff hD.aemeasurable hT'm).2 hω
  rw [← hmarg] at hdata
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hdata] with q hq hIC
  rcases hq with h | h
  · exact absurd hIC h
  · exact (hEq (q.1, p₀)).1 h

/-- **The conjunct `(I3)` of the chart input from Lévy's conformal invariance and the coordinate change of the
Liouville Brownian motion.** From `LevyConformalChartStmt` and `ChartFieldLBMLimitStmt γ` there is a Borel kernel `K`
from fields on the unit disc to laws of paths such that, in every valid environment, on every joint weak limit `ν''`
of the field coordinates, a measurable coordinate `E`, the curve and path-law families, for every window `(a, u, b)`
(given that the window chart law of the Liouville Brownian law and the chart field are measurable functions of the
sample), for `ν''`-almost every sample whose window has an inverse chart at `η(u)`:
`windowLBMChartLaw γ a u b (windowChart a u b η) q = K (windowChartField γ a u b (windowChart a u b η) q)`. -/
theorem exists_kernel_ae_windowLBMChartLaw_eq (hLevy : LevyConformalChartStmt) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hgap : ChartFieldLBMLimitStmt γ) :
    ∃ K : (𝓓(unitDiscOpens, ℝ) → ℝ) → Measure (ContinuousPath ℂ), Measurable K ∧
      ∀ (𝒮 : SpaceFillingSLEModel) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ η' : Ω → C(ℝ, ℂ), Measurable η' → ∀ E : Ω → LQGData, Measurable E →
      ∀ (Z : ℕ → Ω → PathLawFamily) (ν'' : Measure JointSample), IsProbabilityMeasure ν'' →
      (∀ f : JointSample →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
          (𝓝 (∫ q, f q ∂ν''))) →
      ∀ a u b : ℝ,
      Measurable (fun q : JointSample => windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q) →
      Measurable (fun q : JointSample => windowChartField γ a u b (windowChart a u b q.1.2) q) →
      ∀ᵐ q ∂ν'', (∃ ψ, IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) ψ) →
        windowLBMChartLaw γ a u b (windowChart a u b q.1.2) q =
          K (windowChartField γ a u b (windowChart a u b q.1.2) q) := by
  obtain ⟨K₀, hK₀m, hK₀⟩ := hgap
  refine ⟨fun g => (K₀ g : Measure (ContinuousPath ℂ)).map (timeScalePath (lbmExitMedian γ).toNNReal), ?_, ?_⟩
  · have h : (fun g => (K₀ g : Measure (ContinuousPath ℂ)).map (timeScalePath (lbmExitMedian γ).toNNReal)) =
        fun g => ((timeScaleLaw (lbmExitMedian γ).toNNReal (K₀ g) : ProbabilityMeasure (ContinuousPath ℂ)) :
          Measure (ContinuousPath ℂ)) :=
      funext fun g => (coe_timeScaleLaw _ _).symm
    rw [h]
    exact measurable_subtype_coe.comp ((timeScaleLaw _).continuous.measurable.comp hK₀m)
  · intro 𝒮 Ω _ S hS H hH hrep η' hη' E hE Z ν'' hν'' hconv a u b hLm hFm
    exact ae_windowLBMChartLaw_eq_of_chartTransportLimit hγ hγ2 hS hLevy hH hrep hK₀m
      (hK₀ 𝒮 Ω S hS H hH hrep) hη' hE hconv a u b hLm hFm

end MatedCRT
