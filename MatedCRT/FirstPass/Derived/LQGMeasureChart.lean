import MatedCRT.FirstPass.Derived.LQGMeasureChartBorel
import MatedCRT.FirstPass.Derived.LQGMeasureChartPullback
import MatedCRT.FirstPass.Derived.LQGMeasureChartOpenProperty
import MatedCRT.FirstPass.Derived.LQGMeasureChartPerturb
import MatedCRT.FirstPass.Derived.ChartFieldLBM

/-!
# The coordinate change of the LQG measure for all inverse charts, from the property on open sets

Assembly of `LQGMeasureChartStmt`: the Borel map `M = chartMeasure γ` (the vague limit in the unit disc of the
smooth approximations of a field on the disc, Sheffield–Wang, *Field-measure correspondence in Liouville quantum
gravity almost surely commutes with all conformal maps simultaneously*, arXiv:1605.06171v2, §3.2 after (3.4)) sends
the chart field `h ∘ φ + Q log |φ'|` of every inverse chart `ψ` of a bounded open set `U` to `ψ_* (μ_h|_U)`, on the
almost sure event where the field and its LQG measure have the coordinate change on open sets (`OpenChartProp`: the
conclusion of Sheffield–Wang, Theorems 1.1, 1.2 and 1.4, at the scales `2^{-k}`; Duplantier–Sheffield,
arXiv:0808.1560v2, Proposition 2.1 for a fixed map). The event is fixed before the charts.

For a chart `ψ` of `U`, `ψ(U)` is the unit disc. On the smooth functions supported in the disc the chart field
(`chartFieldPairing`, a distribution on the disc by `chartFieldDist`) is the field `pullbackPairingOn γ h U ψ` of
`OpenChartProp`, so the two families of smooth approximations on the disc coincide; their vague limit `ν` with
`ν(A) = μ(U ∩ ψ⁻¹(A))` is `ψ_* (μ|_U)`, and `chartMeasure_eq_of_isVagueLimitOn` identifies it with `M` of the chart
field.

* `chartFieldPairing_eq_pullbackPairingOn`: the chart field of an inverse chart is `pullbackPairingOn` on the test
  functions of the unit disc.
* `isVagueLimitOn_chartFieldDist_of_openChartProp`: deterministic, the smooth approximations of the chart field
  converge vaguely in the disc to `ψ_* (μ|_U)`.
* `lqgMeasureChartStmt_of_openChartProp`: `LQGMeasureChartStmt γ` from the almost sure property on open sets in every
  valid environment, for every measurable version of the field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal Distributions

namespace MatedCRT

namespace LQGMeasureChart

/-- The pairing of a distribution on `V` with a smooth function compactly supported in `V`. -/
theorem pairFun_eq_of_mem {V : TopologicalSpace.Opens ℂ} (g : LQGMetric.DistOn V) {u : ℂ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huc : HasCompactSupport u) (huV : tsupport u ⊆ V) :
    pairFun g u = g ⟨u, hu, huc, huV⟩ := by
  unfold pairFun
  exact dite_eq_left ⟨hu, huc, huV⟩

/-- Smooth approximations of two functionals agreeing on the translates `f_ε(z - ·)` with `B̄_ε(z) ⊆ V` are equal. -/
theorem smoothApprox_congr {γ : ℝ} {f : ℂ → ℝ} {V : Set ℂ} {G G' : (ℂ → ℝ) → ℝ} {ε : ℝ}
    (hGG' : ∀ z, closedBall z ε ⊆ V → G (fun w => mollScale f ε (z - w)) = G' (fun w => mollScale f ε (z - w))) :
    smoothApprox γ f V G ε = smoothApprox γ f V G' ε := by
  unfold smoothApprox
  refine congrArg _ (funext fun z => ?_)
  by_cases hz : closedBall z ε ⊆ V
  · simp only [ite_eq_left hz, smoothExponent, hGG' z hz]
  · simp only [ite_eq_right hz]

/-- **The chart field is the pull-back field on open sets.** For an inverse chart `ψ` of a bounded open set `U`, the
pairings of the chart field `h ∘ φ + Q log |φ'|` with the test functions of the unit disc are those of
`pullbackPairingOn γ h U ψ`. -/
theorem chartFieldPairing_eq_pullbackPairingOn (γ : ℝ) (h : LQGMetric.DistC) {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) (f : 𝓓(unitDiscOpens, ℝ)) :
    chartFieldPairing γ h U z ψ f = pullbackPairingOn γ h U ψ f := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (U.indicator fun x => f (ψ x) * ‖deriv ψ x‖ ^ 2) := contDiff_chartTestFun hψ hU hUb f
  have huc : HasCompactSupport (U.indicator fun x => f (ψ x) * ‖deriv ψ x‖ ^ 2) :=
    hasCompactSupport_chartTestFun hψ hU hUb f
  rw [chartFieldPairing, dite_eq_left (show IsInverseChart U z ψ ∧ IsOpen U ∧ Bornology.IsBounded U from
    ⟨hψ, hU, hUb⟩), pullbackPairingOn, pairFun_eq_of_mem h hu huc fun _ _ => trivial]
  rfl

/-- **The smooth approximations of the chart field converge to the image of the LQG measure.** If the field `h` and
the measure `μ` have the coordinate change on open sets (`OpenChartProp`), then for every inverse chart `ψ` of a
bounded open set `U` the smooth approximations of the chart field `h ∘ φ + Q log |φ'|` on the unit disc converge
vaguely in the disc to `ψ_* (μ|_U)`. -/
theorem isVagueLimitOn_chartFieldDist_of_openChartProp {γ : ℝ} {h : LQGMetric.DistC} {μ : Measure ℂ}
    (hprop : OpenChartProp γ stdMollifier h μ) {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hψ : IsInverseChart U z ψ) :
    QuantumZipper.IsVagueLimitOn (ball 0 1)
      (fun k => smoothApprox γ stdMollifier (ball 0 1) (pairFun (chartFieldDist γ h hψ hU hUb))
        (HarmonicBalls.dyadicScale k)) ((μ.restrict U).map ψ) := by
  have hψm : Measurable ψ := ψ.continuous.measurable
  obtain ⟨ν, hν, hνA⟩ := hprop U hU ψ (hψ.injOn.mono subset_closure) hψ.differentiableOn
    (by rw [hψ.image_eq]; exact isBounded_ball)
  rw [hψ.image_eq] at hν hνA
  -- the two families of smooth approximations on the disc coincide
  have hseq : (fun k => smoothApprox γ stdMollifier (ball 0 1) (pairFun (chartFieldDist γ h hψ hU hUb))
      (HarmonicBalls.dyadicScale k)) =
      fun k => smoothApprox γ stdMollifier (ball 0 1) (pullbackPairingOn γ h U ψ) (HarmonicBalls.dyadicScale k) := by
    funext k
    refine smoothApprox_congr fun w hw => ?_
    have hε := HarmonicBalls.dyadicScale_pos k
    have hu : ContDiff ℝ (⊤ : ℕ∞) fun v => mollScale stdMollifier (HarmonicBalls.dyadicScale k) (w - v) := by
      show ContDiff ℝ (⊤ : ℕ∞) fun v => ((HarmonicBalls.dyadicScale k) ^ 2)⁻¹ *
        stdMollifier ((w - v) / ((HarmonicBalls.dyadicScale k : ℝ) : ℂ))
      exact contDiff_const.mul
        (isMollifier_stdMollifier.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))
    have huc := hasCompactSupport_mollScale_sub isMollifier_stdMollifier hε w
    have huD : tsupport (fun v => mollScale stdMollifier (HarmonicBalls.dyadicScale k) (w - v)) ⊆
        (unitDiscOpens : Set ℂ) :=
      (tsupport_mollScale_sub_subset isMollifier_stdMollifier hε w).trans (ball_subset_closedBall.trans hw)
    rw [pairFun_eq_of_mem _ hu huc huD, chartFieldDist_apply]
    exact chartFieldPairing_eq_pullbackPairingOn γ h hψ hU hUb _
  -- the limit is the image of `μ|_U`
  have hνD : ν.restrict (ball 0 1) = ν := Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hν.1)
  have hνeq : ν = (μ.restrict U).map ψ := by
    ext A hA
    have hAD : MeasurableSet (A ∩ ball 0 1) := hA.inter measurableSet_ball
    rw [← hνD, Measure.restrict_apply hA, hνA _ hAD inter_subset_right, Measure.map_apply hψm hA,
      Measure.restrict_apply (hψm hA)]
    congr 1
    ext y
    constructor
    · rintro ⟨hyU, hyA, -⟩
      exact ⟨hyA, hyU⟩
    · rintro ⟨hyA, hyU⟩
      exact ⟨hyU, hyA, hψ.image_eq ▸ mem_image_of_mem ψ hyU⟩
  rw [hνeq] at hν
  exact (congrArg (fun S => QuantumZipper.IsVagueLimitOn (ball 0 1) S ((μ.restrict U).map ψ)) hseq).mpr hν

end LQGMeasureChart

open LQGMeasureChart

/-- **The coordinate change of the LQG measure for all inverse charts, from the property on open sets.** If in every
valid environment, for every measurable version `H` of the field, almost surely the field and its LQG measure have
the coordinate change on open sets (`OpenChartProp`), then `LQGMeasureChartStmt γ` holds with the Borel map
`M = chartMeasure γ`. -/
theorem lqgMeasureChartStmt_of_openChartProp {γ : ℝ}
    (hprop : ∀ (𝒮 : SpaceFillingSLEModel) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ H : Ω → LQGMetric.DistC, Measurable H → (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) →
      ∀ᵐ ω ∂S.P, OpenChartProp γ stdMollifier (H ω) (S.μ ω)) :
    LQGMeasureChartStmt γ := by
  refine ⟨chartMeasure γ, measurable_chartMeasure γ, ?_⟩
  intro 𝒮 Ω _ S hS H hH hHae
  filter_upwards [hprop 𝒮 Ω S hS H hH hHae] with ω hω
  intro U z ψ hU hUb hψ
  rw [LQGMetric.pairJInv_pairJ, show chartFieldPairing γ (H ω) U z ψ = ⇑(chartFieldDist γ (H ω) hψ hU hUb) from
    funext fun f => (chartFieldDist_apply γ (H ω) hψ hU hUb f).symm]
  exact chartMeasure_eq_of_isVagueLimitOn γ (isVagueLimitOn_chartFieldDist_of_openChartProp hω hU hUb hψ)

end MatedCRT
