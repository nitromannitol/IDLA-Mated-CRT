import MatedCRT.FirstPass.Derived.HN9OfJointChartLaws
import MatedCRT.FirstPass.Derived.LBMPathLawFieldStartExit

/-!
# Inverse charts of the windows and the non-degeneracy of the chart Liouville Brownian motion

For the window `(a, u, b)` of the curve, Berestycki–Gwynne (2020) use the conformal map `φ : 𝔻 → U` onto the
component `U` of the interior of `η([a, b])` containing `η(u)`, with `φ(0) = η(u)`, extended to a homeomorphism of
the closures (Pommerenke (1992), Theorem 2.6). Its inverse, extended continuously to `ℂ`, is an inverse chart
(`IsInverseChart U η(u) ψ`): `ψ(η(u)) = 0`, `ψ` is injective on the closure of `U`, holomorphic on `U`, and maps
`U` onto the unit disc and the frontier of `U` onto the unit circle.

For an inverse chart, the chart image of a path from `η(u)` that leaves `U` starts at `0` and leaves the unit disc
(`chartStopPath_start_exit`). Since `U ⊆ η([a, b])` is bounded and the rescaled Liouville Brownian motion leaves
every ball (`ae_lbmPathLawField_curvePoint_start_exit`), the chart image of the Liouville Brownian law of the
field from `η(u)` is non-degenerate on the joint limit (`ae_windowLBMChartLaw_start_exit`). This discharges the
non-degeneracy clause of `BG20JointChartLawInput`: the input `BG20WindowChartInput` asks instead that the chart maps
be inverse charts, and implies `BG20JointChartLawInput` (`bg20JointChartLawInput_of_windowCharts`).

## Main statements

* `IsInverseChart`, `chartStopPath_start_exit`, `exists_nat_windowDomain_subset_ball`,
  `ae_windowLBMChartLaw_start_exit`.
* `BG20WindowChartInput`, `bg20JointChartLawInput_of_windowCharts`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set MarkovProcess
open _root_.HarmonicBalls _root_.MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal BoundedContinuousFunction
open MatedCRT.FirstPass.Derived (LQGData LQGData.toMeasure)

namespace MatedCRT

/-- `ψ` is an inverse chart of the open set `U` at the point `z ∈ U`: `ψ z = 0`, `ψ` is injective on the closure
of `U` and holomorphic on `U`, and maps `U` onto the unit disc and the frontier of `U` onto the unit circle (the
inverse of the normalized conformal map `φ : 𝔻 → U`, `φ(0) = z`, extended to the closures and then continuously to
`ℂ`). -/
structure IsInverseChart (U : Set ℂ) (z : ℂ) (ψ : C(ℂ, ℂ)) : Prop where
  mem : z ∈ U
  apply_point : ψ z = 0
  injOn : InjOn ψ (closure U)
  differentiableOn : DifferentiableOn ℂ ψ U
  image_eq : ψ '' U = Metric.ball 0 1
  image_frontier : ψ '' frontier U = Metric.sphere 0 1

theorem IsInverseChart.mapsTo_frontier {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)} (h : IsInverseChart U z ψ) :
    MapsTo ψ (frontier U) (Metric.ball (0 : ℂ) 1)ᶜ := by
  intro w hw hmem
  have hs : ψ w ∈ Metric.sphere (0 : ℂ) 1 := h.image_frontier ▸ mem_image_of_mem ψ hw
  rw [Metric.mem_sphere, dist_zero_right] at hs
  rw [Metric.mem_ball, dist_zero_right, hs] at hmem
  exact lt_irrefl _ hmem

/-- **The chart image of a path is non-degenerate.** If `ψ z = 0` with `z ∈ U` open and `ψ` maps the frontier of
`U` outside the unit disc, then the chart image of a path from `z` which leaves `U` starts at `0` and leaves the unit
disc. -/
theorem chartStopPath_start_exit {U : Set ℂ} (hU : IsOpen U) {z : ℂ} {ψ : C(ℂ, ℂ)} (hz : z ∈ U)
    (hψz : ψ z = 0) (hψf : MapsTo ψ (frontier U) (Metric.ball (0 : ℂ) 1)ᶜ) {f : ContinuousPath ℂ}
    (hf0 : f 0 = z) (hfin : ContinuousPath.exitTime U f ≠ ⊤) :
    chartStopPath U ψ f 0 = 0 ∧
      ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) (chartStopPath U ψ f) ≠ ⊤ := by
  have hstop : ∀ t, stopAtExitTime U f t = f (min t (ContinuousPath.exitTime U f).toNNReal) := by
    intro t
    show f (exitClamp _ t) = _
    simp only [exitClamp_apply, hfin, ↓reduceIte]
  have hf0U : f 0 ∈ U := by
    rw [hf0]
    exact hz
  refine ⟨?_, ?_⟩
  · show ψ (stopAtExitTime U f 0) = 0
    rw [hstop, min_eq_left zero_le, hf0, hψz]
  · have hfront := ContinuousPath.coordinate_exitTime_mem_frontier U hU f hf0U hfin
    have hmem : chartStopPath U ψ f (ContinuousPath.exitTime U f).toNNReal ∉ Metric.ball (0 : ℂ) 1 := by
      show ψ (stopAtExitTime U f _) ∉ _
      rw [hstop, min_self]
      exact hψf hfront
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (ContinuousPath.exitTime_le_of_notMem _ _ _ hmem)

/-- The domain of a window of a continuous curve is bounded. -/
theorem exists_nat_windowDomain_subset_ball (η : C(ℝ, ℂ)) (a u b : ℝ) :
    ∃ R : ℕ, windowDomain η a u b ⊆ Metric.ball (0 : ℂ) R := by
  have hsub : windowDomain η a u b ⊆ η '' Icc a b :=
    (connectedComponentIn_subset _ _).trans interior_subset
  obtain ⟨r, hr⟩ := ((isCompact_Icc.image η.continuous).isBounded.subset hsub).subset_ball (0 : ℂ)
  obtain ⟨R, hR⟩ := exists_nat_ge r
  exact ⟨R, hr.trans (Metric.ball_subset_ball hR)⟩

/-- **Non-degeneracy of the chart Liouville Brownian motion, on the joint limit.** If almost surely `ψ q` is an
inverse chart of the window `(a, u, b)` at `η(u)`, then almost surely almost every path of the chart image of the
Liouville Brownian law of the field from `η(u)` starts at `0` and leaves the unit disc. -/
theorem ae_windowLBMChartLaw_start_exit {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {E : Ω → LQGData} (hE : Measurable E) {Z : ℕ → Ω → PathLawFamily}
    {ν'' : Measure JointSample} [IsProbabilityMeasure ν'']
    (hconv : ∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
        (𝓝 (∫ q, f q ∂ν''))) (a u b : ℝ) {ψ : JointSample → C(ℂ, ℂ)}
    (hψ : ∀ᵐ q ∂ν'', IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) (ψ q)) :
    ∀ᵐ q ∂ν'', ∀ᵐ f ∂windowLBMChartLaw γ a u b (ψ q) q,
      f 0 = 0 ∧ ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f ≠ ⊤ := by
  filter_upwards [hψ, ae_lbmPathLawField_curvePoint_start_exit hγ hγ2 hS hη' hH hrep hE hconv u]
    with q hq hl
  obtain ⟨R, hR⟩ := exists_nat_windowDomain_subset_ball q.1.2 a u b
  have hset : MeasurableSet {f : ContinuousPath ℂ | f 0 = 0 ∧
      ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f ≠ ⊤} :=
    ((continuous_eval_const (0 : ℝ≥0)).measurable (measurableSet_singleton 0)).inter
      ((ContinuousPath.measurable_exitTime _ Metric.isOpen_ball) (measurableSet_singleton ⊤)).compl
  refine (ae_map_iff (measurable_chartStopPath _ (isOpen_windowDomain _ _ _ _) _).aemeasurable hset).2 ?_
  filter_upwards [hl] with f hf
  exact chartStopPath_start_exit (isOpen_windowDomain _ _ _ _) hq.mem hq.apply_point hq.mapsTo_frontier
    hf.1 (ne_top_of_le_ne_top (hf.2 R) (ContinuousPath.exitTime_mono hR f))

/-- **Literature input (Berestycki–Gwynne (2020), Lemma 7.20 without the time change, and Lemma 7.21, on the joint
limit, with inverse charts).** As `BG20JointChartLawInput`, except that the chart maps `ψ`, `ψ'` are almost surely
inverse charts of the two windows (`IsInverseChart`), and the non-degeneracy of the chart Liouville Brownian
motion is not assumed (it follows, `ae_windowLBMChartLaw_start_exit`). In Berestycki–Gwynne, the inverse chart
is the inverse of the conformal map `φ : 𝔻 → windowDomain η a u b` with `φ(0) = η(u)` (Pommerenke (1992),
Theorem 2.6, the boundary being a Jordan curve by the flow-line construction of space-filling SLE), extended
continuously to `ℂ`; the remaining clauses are as in `BG20JointChartLawInput`. -/
def BG20WindowChartInput (𝒮 : SpaceFillingSLEModel) : Prop :=
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
    ∃ (F : Type) (_ : MeasurableSpace F) (K : F → Measure (ContinuousPath ℂ))
      (ψ ψ' : JointSample → C(ℂ, ℂ)) (hD hD' : JointSample → F),
      (∀ᵐ q ∂ν'', IsInverseChart (windowDomain q.1.2 a u b) (q.1.2 u) (ψ q)) ∧
      (∀ᵐ q ∂ν'', IsInverseChart (windowDomain q.1.2 a' u' b') (q.1.2 u') (ψ' q)) ∧
      Measurable K ∧ Measurable hD ∧ Measurable hD' ∧
      Measurable (fun q => windowChartLaw a u b (ψ q) q) ∧
      Measurable (fun q => windowChartLaw a' u' b' (ψ' q) q) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a u b (ψ q) q = K (hD q)) ∧
      (∀ᵐ q ∂ν'', windowLBMChartLaw γ a' u' b' (ψ' q) q = K (hD' q)) ∧
      IndepFun (fun q => (hD q, windowChartLaw a u b (ψ q) q))
        (fun q => (hD' q, windowChartLaw a' u' b' (ψ' q) q)) ν''

/-- The input with inverse charts implies `BG20JointChartLawInput`: the non-degeneracy of `K (hD)` is that of the
chart image of the Liouville Brownian law (`ae_windowLBMChartLaw_start_exit`), transported by the coordinate-change
identity. -/
theorem bg20JointChartLawInput_of_windowCharts {𝒮 : SpaceFillingSLEModel}
    (hW : BG20WindowChartInput 𝒮) : BG20JointChartLawInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
    hau hub hba' ha'u' hu'b'
  obtain ⟨F, mF, K, ψ, ψ', hD, hD', hψ, hψ', hK, hhD, hhD', hm, hm', hb, hb', hind⟩ :=
    hW γ hγ hγ2 Ω S hS η' hη' hae H hH hrep E hE ε hε0 hε ν'' hν'' hconv hspeed a u b a' u' b'
      hau hub hba' ha'u' hu'b'
  have := hS.isProbabilityMeasure
  have hk : ∀ᵐ q ∂ν'', ∀ᵐ f ∂K (hD q),
      f 0 = 0 ∧ ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f ≠ ⊤ := by
    filter_upwards [hb, ae_windowLBMChartLaw_start_exit hγ hγ2 hS hη' hH hrep hE hconv a u b hψ]
      with q hq hl
    rwa [← hq]
  have hk' : ∀ᵐ q ∂ν'', ∀ᵐ f ∂K (hD' q),
      f 0 = 0 ∧ ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) f ≠ ⊤ := by
    filter_upwards [hb', ae_windowLBMChartLaw_start_exit hγ hγ2 hS hη' hH hrep hE hconv a' u' b' hψ']
      with q hq hl
    rwa [← hq]
  exact ⟨F, mF, K, ψ, ψ', hD, hD', hK, hhD, hhD', hm, hm', hb, hb', hk, hk', hind⟩

end MatedCRT
