import MatedCRT.FirstPass.Derived.WindowChartBGFieldSurface
import MatedCRT.FirstPass.Derived.ChartStopPathContinuity
import MatedCRT.FirstPass.Derived.FixedMarginalAdjoin
import MatedCRT.FirstPass.Derived.WindowChartLawMeasurable
import MatedCRT.FirstPass.Derived.LBMPathLawFieldStartExit
import MatedCRT.FirstPass.Derived.ExitTimeClockAtExit
import MatedCRT.FirstPass.Derived.ExitTimeScaling
import MatedCRT.FirstPass.Derived.LQGApproxPathKernel
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import HarmonicBalls.Proofs.Sec6.BoundaryRegularityRestart

/-!
# Joint convergence of the window coordinates (Berestycki–Gwynne (2020), proof of Lemma 7.21)

This file proves `BG20WindowJointConvergenceInput` (the replacement step (7.36) of the proof of Lemma 7.21 of
Berestycki–Gwynne, arXiv:2003.10320, lines 3831-3838: "it is easily seen from the convergence `(h, η, P^ε) → (h, η, P)`
in law ...") from one named input on Jordan domains, `JordanDomainExteriorRegularity` (planar Brownian motion started on
the frontier of a Jordan domain leaves its closure at once: Lawler, Theorem 3.76).

* **Adjoining the window data.** The first marginal of the joint laws (field coordinates, `E`, curve) is the same at
  every level and in the limit. The chart field coordinates, the inverse chart `windowChartBG` and the signed distance
  `windowGapBG = d(·, Uᶜ) - d(·, closure U)` of each window are Borel functions of this marginal; they are adjoined to
  the joint convergence (`MatedCRT.tendsto_integral_comp_prodMk_of_ae_continuousAt`, Lusin's theorem).
* **The exit at a crossing.** The window is `U = {windowGapBG > 0}`; the chart law of the window is continuous in
  (law family, starting point, inverse chart, signed distance) at every point at which almost every path leaves
  `{windowGapBG ≥ 0} ⊆ closure U` no later than `U` (`MatedCRT.tendsto_integral_chartLaw_gapDomain`).
* **Almost every limiting path crosses.** Under the joint limit the law at `η(u)` is a linear time change of the
  Liouville Brownian law, a continuous strictly increasing time change of planar Brownian motion; planar Brownian motion
  from `η(u) ∈ U` leaves `closure U` when it leaves `U`
  (`HarmonicBalls.Section6.ae_exitTime_closure_eq_of_boundary_instant_exit` and `JordanDomainExteriorRegularity`), and
  time changes preserve this. Off the windows with an inverse chart the chart is `0` and the signed distance is `-1`.

## Main statements

* `MatedCRT.JordanDomainExteriorRegularity`: the named input (PENDING TRUTH CHECK).
* `MatedCRT.windowGapBG`, `MatedCRT.measurable_windowGapBG`, `MatedCRT.chartLaw_gapDomain_windowGapBG`.
* `MatedCRT.ae_jointLimit_crossing_of_speed`: almost every limiting path from `η(u)` crosses.
* `MatedCRT.bg20WindowJointConvergenceInput`: `BG20WindowJointConvergenceInput 𝒮` for every `𝒮`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set Metric MarkovProcess
open _root_.HarmonicBalls
open scoped NNReal ENNReal BoundedContinuousFunction Distributions
open MatedCRT.FirstPass.Derived (LQGData)

namespace MatedCRT

/-! ### The named input -/

/-- **Planar Brownian motion leaves the closure of a Jordan domain at once from every frontier point.** For a bounded
open set `U` with an inverse chart `ψ` at a point `z` (so that `ψ` maps `closure U` homeomorphically onto the closed
unit disc and `U` is a Jordan domain), planar Brownian motion started at any point `y` of the frontier of `U` almost
surely leaves `closure U` immediately.

Source: every point of a Jordan curve is the endpoint of an arc in the exterior domain (Pommerenke, *Boundary
Behaviour of Conformal Maps*, Springer 1992, Section 2.1); for Brownian motion started at `y`, the Beurling estimate
(Lawler, *Conformally Invariant Processes in the Plane*, AMS 2005, Theorem 3.76) applied to the portion of this arc
crossing the annulus `{δ < |w - y| < r/2}` bounds the probability of reaching distance `r` from `y` without hitting
the exterior by `O(√(δ/r))`; let `δ ↓ 0`, then `r ↓ 0`. This is the crossing step of the joint convergence in the proof
of Berestycki–Gwynne (2020), Lemma 7.21. PENDING TRUTH CHECK. -/
def JordanDomainExteriorRegularity : Prop :=
  ∀ (U : Set ℂ) (z : ℂ) (ψ : C(ℂ, ℂ)), Bornology.IsBounded U → IsInverseChart U z ψ →
    ∀ y ∈ frontier U, ∀ᵐ b ∂planarBrownianMotion y, ContinuousPath.exitTime (closure U) b = 0

/-! ### The signed distance to the frontier -/

/-- The signed distance `d(z, Uᶜ) - d(z, closure U)` of a set `U`. -/
noncomputable def signedGap (U : Set ℂ) : C(ℂ, ℝ) :=
  ⟨fun z => infDist z Uᶜ - infDist z (closure U), (continuous_infDist_pt _).sub (continuous_infDist_pt _)⟩

theorem signedGap_apply (U : Set ℂ) (z : ℂ) : signedGap U z = infDist z Uᶜ - infDist z (closure U) :=
  rfl

/-- The signed distance of an open set with nonempty complement is positive exactly on the set. -/
theorem gapDomain_signedGap {U : Set ℂ} (hU : IsOpen U) (hUc : (Uᶜ).Nonempty) : gapDomain (signedGap U) = U := by
  ext z
  show 0 < infDist z Uᶜ - infDist z (closure U) ↔ z ∈ U
  constructor
  · intro h
    by_contra hz
    have h0 : infDist z Uᶜ = 0 := infDist_zero_of_mem hz
    have h1 : 0 ≤ infDist z (closure U) := infDist_nonneg
    linarith
  · intro hz
    have h0 : infDist z (closure U) = 0 := infDist_zero_of_mem (subset_closure hz)
    have hpos : 0 < infDist z Uᶜ := by
      rcases (infDist_nonneg (x := z) (s := Uᶜ)).eq_or_lt with h | h
      · exfalso
        have hmem : z ∈ closure Uᶜ := (mem_closure_iff_infDist_zero hUc).2 h.symm
        rw [hU.isClosed_compl.closure_eq] at hmem
        exact hmem hz
      · exact h
    linarith

/-- The signed distance of a nonempty set is negative off its closure. -/
theorem setOf_nonneg_signedGap_subset {U : Set ℂ} (hU : U.Nonempty) :
    {z | 0 ≤ signedGap U z} ⊆ closure U := by
  intro z hz
  by_contra hzc
  have hzU : z ∈ Uᶜ := fun h => hzc (subset_closure h)
  have h0 : infDist z Uᶜ = 0 := infDist_zero_of_mem hzU
  have hpos : 0 < infDist z (closure U) := by
    rcases (infDist_nonneg (x := z) (s := closure U)).eq_or_lt with h | h
    · exfalso
      have hmem : z ∈ closure (closure U) := (mem_closure_iff_infDist_zero hU.closure).2 h.symm
      rw [closure_closure] at hmem
      exact hzc hmem
    · exact h
  have hz' : 0 ≤ infDist z Uᶜ - infDist z (closure U) := hz
  linarith

/-- The segment from a point of an open set to a point outside it meets the frontier. -/
theorem exists_mem_segment_frontier {U : Set ℂ} (hU : IsOpen U) {z y : ℂ} (hz : z ∈ U) (hy : y ∉ U) :
    ∃ w ∈ segment ℝ z y, w ∈ frontier U := by
  by_contra hcon
  have hfr : ∀ w ∈ segment ℝ z y, w ∉ frontier U := fun w hw hwf => hcon ⟨w, hw, hwf⟩
  have hcover : segment ℝ z y ⊆ U ∪ (closure U)ᶜ := by
    intro w hw
    by_cases hwU : w ∈ U
    · exact Or.inl hwU
    · refine Or.inr fun hwc => hfr w hw ?_
      rw [frontier, hU.interior_eq]
      exact ⟨hwc, hwU⟩
  rcases (convex_segment z y).isPreconnected.subset_or_subset hU isClosed_closure.isOpen_compl
      (Disjoint.mono_left subset_closure disjoint_compl_right) hcover with h | h
  · exact hy (h (right_mem_segment ℝ z y))
  · exact h (left_mem_segment ℝ z y) (subset_closure hz)

/-- For a point of an open set, the distance to the complement is the distance to the frontier. -/
theorem infDist_compl_eq_infDist_frontier {U : Set ℂ} (hU : IsOpen U) (hfr : (frontier U).Nonempty) {z : ℂ}
    (hz : z ∈ U) : infDist z Uᶜ = infDist z (frontier U) := by
  have hsub : frontier U ⊆ Uᶜ := by
    rw [hU.frontier_eq]
    exact fun w hw => hw.2
  refine le_antisymm (infDist_le_infDist_of_subset hsub hfr) ?_
  refine (le_infDist (hfr.mono hsub)).2 fun y hy => ?_
  obtain ⟨w, hwseg, hwfr⟩ := exists_mem_segment_frontier hU hz hy
  have hwball : w ∈ closedBall z (dist y z) :=
    (convex_closedBall z (dist y z)).segment_subset (mem_closedBall_self dist_nonneg)
      (mem_closedBall.2 le_rfl) hwseg
  rw [mem_closedBall] at hwball
  calc infDist z (frontier U) ≤ dist z w := infDist_le_dist_of_mem hwfr
    _ ≤ dist z y := by rw [dist_comm z w, dist_comm z y]; exact hwball

/-- The distance from a point to the image of a compact set under a continuous map depends continuously on the map
(compact-open topology). -/
theorem continuous_infDist_image {S : Set ℂ} (hS : IsCompact S) (hne : S.Nonempty) (z : ℂ) :
    Continuous fun Φ : C(ℂ, ℂ) => infDist z (Φ '' S) := by
  rw [continuous_iff_continuousAt]
  intro Φ₀
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hu := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
    (tendsto_id : Tendsto (id : C(ℂ, ℂ) → C(ℂ, ℂ)) (𝓝 Φ₀) (𝓝 Φ₀)) S hS
  have key : ∀ Φ₁ Φ₂ : C(ℂ, ℂ), (∀ w ∈ S, dist (Φ₁ w) (Φ₂ w) < ε / 2) →
      infDist z (Φ₁ '' S) ≤ infDist z (Φ₂ '' S) + ε / 2 := by
    intro Φ₁ Φ₂ h
    obtain ⟨y, ⟨w, hw, rfl⟩, hy⟩ := (hS.image Φ₂.continuous).exists_infDist_eq_dist (hne.image Φ₂) z
    calc infDist z (Φ₁ '' S) ≤ dist z (Φ₁ w) := infDist_le_dist_of_mem (mem_image_of_mem Φ₁ hw)
      _ ≤ dist z (Φ₂ w) + dist (Φ₂ w) (Φ₁ w) := dist_triangle _ _ _
      _ ≤ infDist z (Φ₂ '' S) + ε / 2 := by
          rw [hy, dist_comm (Φ₂ w)]
          linarith [h w hw]
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu (ε / 2) (half_pos hε)] with Φ hΦ
  have hΦ' : ∀ w ∈ S, dist (Φ₀ w) (Φ w) < ε / 2 := hΦ
  have h1 := key Φ Φ₀ fun w hw => by rw [dist_comm]; exact hΦ' w hw
  have h2 := key Φ₀ Φ hΦ'
  show dist (infDist z (Φ '' S)) (infDist z (Φ₀ '' S)) < ε
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### The signed distance of the window -/

/-- The curves whose window `(a, u, b)` has an inverse chart at the curve point. -/
def windowChartCurves (a u b : ℝ) : Set C(ℝ, ℂ) :=
  {η | ∃ ψ, IsInverseChart (windowDomain η a u b) (η u) ψ}

theorem measurableSet_windowChartCurves (a u b : ℝ) : MeasurableSet (windowChartCurves a u b) :=
  measurableSet_setOf_exists_isInverseChart a u b

/-- A joint-limit sample with curve `η` (its other coordinates play no role). -/
noncomputable def curveSample (η : C(ℝ, ℂ)) : JointSample :=
  ((((0 : LQGMetric.CoordJ → ℝ), MatedCRT.FirstPass.Derived.LQGData.encode 0), η),
    ContinuousMap.const ℂ (⟨Measure.dirac (ContinuousMap.const _ (0 : ℂ)), inferInstance⟩ :
      ProbabilityMeasure (ContinuousPath ℂ)))

theorem windowChartBG_eq_zero_of_not_mem {a u b : ℝ} {η : C(ℝ, ℂ)} (hη : η ∉ windowChartCurves a u b) :
    windowChartBG a u b η = 0 := by
  have h : windowChart a u b (curveSample η).1.2 = 0 := windowChart_eq_zero hη
  have h' : windowChart a u b η = 0 := h
  ext x
  rw [windowChartBG_apply, h']
  simp

open Classical in
/-- **The signed distance function of the window `(a, u, b)` of `η`**: `d(z, Uᶜ) - d(z, closure U)` for the window
`U` when it has an inverse chart, the constant `-1` otherwise. -/
noncomputable def windowGapBG (a u b : ℝ) (η : C(ℝ, ℂ)) : C(ℂ, ℝ) :=
  if η ∈ windowChartCurves a u b then signedGap (windowDomain η a u b) else ContinuousMap.const ℂ (-1)

theorem frontier_windowDomain_nonempty {a u b : ℝ} {η : C(ℝ, ℂ)} (hη : η ∈ windowChartCurves a u b) :
    (frontier (windowDomain η a u b)).Nonempty := by
  obtain ⟨ψ, hψ⟩ := id hη
  have hD := (isNormalizedDiscMap_windowDiscMap hψ).isDiscMap
  rw [← hD.image_sphere]
  exact ⟨_, mem_image_of_mem _ (mem_sphere_zero_iff_norm.2 norm_one)⟩

theorem gapDomain_windowGapBG_of_mem {a u b : ℝ} {η : C(ℝ, ℂ)} (hη : η ∈ windowChartCurves a u b) :
    gapDomain (windowGapBG a u b η) = windowDomain η a u b := by
  have hU := isOpen_windowDomain η a u b
  have hsub : frontier (windowDomain η a u b) ⊆ (windowDomain η a u b)ᶜ := by
    rw [hU.frontier_eq]
    exact fun w hw => hw.2
  rw [windowGapBG, ite_eq_left hη]
  exact gapDomain_signedGap hU ((frontier_windowDomain_nonempty hη).mono hsub)

theorem setOf_nonneg_windowGapBG_subset {a u b : ℝ} {η : C(ℝ, ℂ)} (hη : η ∈ windowChartCurves a u b) :
    {z | 0 ≤ windowGapBG a u b η z} ⊆ closure (windowDomain η a u b) := by
  obtain ⟨ψ, hψ⟩ := id hη
  rw [windowGapBG, ite_eq_left hη]
  exact setOf_nonneg_signedGap_subset ⟨η u, hψ.mem⟩

/-- Off the windows with an inverse chart, every path crosses: the signed distance is `-1`. -/
theorem crossing_windowGapBG_of_not_mem {a u b : ℝ} {η : C(ℝ, ℂ)} (hη : η ∉ windowChartCurves a u b)
    (x : ContinuousPath ℂ) :
    ContinuousPath.exitTime {z | 0 ≤ windowGapBG a u b η z} x ≤
      ContinuousPath.exitTime (gapDomain (windowGapBG a u b η)) x := by
  have hD : windowGapBG a u b η = ContinuousMap.const ℂ (-1) := by
    rw [windowGapBG, ite_eq_right hη]
  have h0 : x 0 ∉ {z | 0 ≤ windowGapBG a u b η z} := by
    intro h
    have h' : (0 : ℝ) ≤ windowGapBG a u b η (x 0) := h
    rw [hD, ContinuousMap.const_apply] at h'
    norm_num at h'
  calc ContinuousPath.exitTime {z | 0 ≤ windowGapBG a u b η z} x ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
        GapExit.pathExitTime_le_of_notMem h0
    _ ≤ _ := by simp

/-- **The chart law of the window for its signed distance is the chart law of the window.** -/
theorem chartLaw_gapDomain_windowGapBG (a u b : ℝ) (η : C(ℝ, ℂ)) (K : PathLawFamily) :
    chartLaw K (η u) (gapDomain (windowGapBG a u b η)) (windowChartBG a u b η) = windowLawBG a u b η K := by
  by_cases hη : η ∈ windowChartCurves a u b
  · rw [windowLawBG, gapDomain_windowGapBG_of_mem hη]
  · rw [windowLawBG, windowChartBG_eq_zero_of_not_mem hη]
    unfold chartLaw
    congr 1

open Classical in
theorem windowGapBG_apply_of_mem {a u b : ℝ} {η : C(ℝ, ℂ)} (hη : η ∈ windowChartCurves a u b) (z : ℂ) :
    windowGapBG a u b η z =
      (if infDist z (windowDiscMap a u b η '' closedBall 0 1) = 0 ∧ ‖windowChart a u b η z‖ < 1
        then infDist z (windowDiscMap a u b η '' sphere 0 1) else 0) -
        infDist z (windowDiscMap a u b η '' closedBall 0 1) := by
  obtain ⟨ψ, hψ⟩ := id hη
  have hD := (isNormalizedDiscMap_windowDiscMap hψ).isDiscMap
  have hU := isOpen_windowDomain η a u b
  have hUne : (windowDomain η a u b).Nonempty := ⟨η u, hψ.mem⟩
  have hq : curveSample η ∈ windowChartSet a u b := ⟨ψ, hψ⟩
  have hmemU : z ∈ windowDomain η a u b ↔
      z ∈ windowDiscMap a u b η '' closedBall 0 1 ∧ ‖windowChart a u b η z‖ < 1 :=
    mem_windowDomain_iff hq z
  rw [hD.image_closedBall] at hmemU
  have hmem : (infDist z (closure (windowDomain η a u b)) = 0 ∧ ‖windowChart a u b η z‖ < 1) ↔
      z ∈ windowDomain η a u b := by
    rw [infDist_closure, ← mem_closure_iff_infDist_zero hUne]
    exact hmemU.symm
  rw [windowGapBG, ite_eq_left hη, signedGap_apply, hD.image_closedBall, hD.image_sphere]
  congr 1
  by_cases hz : z ∈ windowDomain η a u b
  · rw [ite_eq_left (hmem.2 hz)]
    exact infDist_compl_eq_infDist_frontier hU (frontier_windowDomain_nonempty hη) hz
  · rw [ite_eq_right (fun h => hz (hmem.1 h))]
    exact infDist_zero_of_mem hz

/-- **The signed distance function of the window is a Borel function of the curve.** -/
theorem measurable_windowGapBG (a u b : ℝ) : Measurable (windowGapBG a u b) := by
  classical
  refine ContinuousMap.measurable_iff_eval.mpr fun z => ?_
  have hΦ := measurable_windowDiscMap a u b
  have hcb : Measurable fun η : C(ℝ, ℂ) => infDist z (windowDiscMap a u b η '' closedBall 0 1) :=
    (continuous_infDist_image (isCompact_closedBall 0 1) ⟨0, mem_closedBall_self zero_le_one⟩ z).measurable.comp hΦ
  have hsp : Measurable fun η : C(ℝ, ℂ) => infDist z (windowDiscMap a u b η '' sphere 0 1) :=
    (continuous_infDist_image (isCompact_sphere 0 1) ⟨1, mem_sphere_zero_iff_norm.2 norm_one⟩ z).measurable.comp hΦ
  have hψ : Measurable fun η : C(ℝ, ℂ) => ‖windowChart a u b η z‖ :=
    continuous_norm.measurable.comp ((continuous_eval_const z).measurable.comp (measurable_windowChart a u b))
  have hset : MeasurableSet {η : C(ℝ, ℂ) |
      infDist z (windowDiscMap a u b η '' closedBall 0 1) = 0 ∧ ‖windowChart a u b η z‖ < 1} :=
    (hcb (measurableSet_singleton 0)).inter (measurableSet_lt hψ measurable_const)
  have heq : (fun η => windowGapBG a u b η z) = fun η =>
      if η ∈ windowChartCurves a u b then
        (if infDist z (windowDiscMap a u b η '' closedBall 0 1) = 0 ∧ ‖windowChart a u b η z‖ < 1
          then infDist z (windowDiscMap a u b η '' sphere 0 1) else 0) -
          infDist z (windowDiscMap a u b η '' closedBall 0 1)
      else -1 := by
    funext η
    by_cases hη : η ∈ windowChartCurves a u b
    · rw [ite_eq_left hη, windowGapBG_apply_of_mem hη]
    · rw [ite_eq_right hη, windowGapBG, ite_eq_right hη, ContinuousMap.const_apply]
  rw [heq]
  exact Measurable.ite (measurableSet_windowChartCurves a u b)
    ((Measurable.ite hset hsp measurable_const).sub hcb) measurable_const

/-! ### Crossing for time-changed paths -/

theorem GapExit.pathExitTime_mono {α : Type*} {U V : Set α} (h : U ⊆ V) (f : ℝ≥0 → α) :
    pathExitTime U f ≤ pathExitTime V f := by
  unfold pathExitTime
  refine sInf_le_sInf ?_
  intro s hs
  obtain ⟨t, hst, ht⟩ := hs
  exact ⟨t, hst, fun hU => ht (h hU)⟩

/-- A continuous strictly increasing time change preserves the equality of two exit times. -/
theorem pathExitTime_comp_clockInverse_congr {α : Type*} {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f)
    {O₁ O₂ : Set α} {g : ℝ≥0 → α} (h : pathExitTime O₁ g = pathExitTime O₂ g) :
    pathExitTime O₁ (fun t => g (_root_.HarmonicBalls.clockInverse f t)) =
      pathExitTime O₂ (fun t => g (_root_.HarmonicBalls.clockInverse f t)) := by
  by_cases hτ : pathExitTime O₁ g = ⊤
  · rw [pathExitTime_comp_clockInverse_eq_top f O₁ g hτ,
      pathExitTime_comp_clockInverse_eq_top f O₂ g (h.symm.trans hτ)]
  · obtain ⟨τ, hτ'⟩ : ∃ τ : ℝ≥0, pathExitTime O₁ g = τ := ⟨_, (ENNReal.coe_toNNReal hτ).symm⟩
    rw [pathExitTime_comp_clockInverse_eq_ofReal hf O₁ g hτ',
      pathExitTime_comp_clockInverse_eq_ofReal hf O₂ g (h.symm.trans hτ')]

/-- **Crossing of a time-changed Liouville Brownian path.** If the planar Brownian path `b` leaves `closure {D > 0}`
when it leaves `{D > 0}`, then the time-changed path `t ↦ b(F⁻¹(c t))` leaves `{D ≥ 0} ⊆ closure {D > 0}` no later
than `{D > 0}`. -/
theorem crossing_timeScalePath_lbm {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ}
    (hb : IsTimeChangeClock (F b)) {c : ℝ≥0} (hc : c ≠ 0) {D : C(ℂ, ℝ)}
    (hsub : {w | 0 ≤ D w} ⊆ closure (gapDomain D))
    (hbU : ContinuousPath.exitTime (closure (gapDomain D)) b = ContinuousPath.exitTime (gapDomain D) b) :
    ContinuousPath.exitTime {w | 0 ≤ D w}
        (LatticeProb.timeScalePath c ⟨liouvilleBrownianPath F b, continuous_liouvilleBrownianPath hb⟩) ≤
      ContinuousPath.exitTime (gapDomain D)
        (LatticeProb.timeScalePath c ⟨liouvilleBrownianPath F b, continuous_liouvilleBrownianPath hb⟩) := by
  set g : ContinuousPath ℂ := ⟨liouvilleBrownianPath F b, continuous_liouvilleBrownianPath hb⟩
  have hgU : ContinuousPath.exitTime (closure (gapDomain D)) g = ContinuousPath.exitTime (gapDomain D) g :=
    pathExitTime_comp_clockInverse_congr (O₁ := closure (gapDomain D)) (O₂ := gapDomain D) (g := ⇑b) hb hbU
  have hsc : ∀ V : Set ℂ, ContinuousPath.exitTime V (LatticeProb.timeScalePath c g) =
      ContinuousPath.exitTime V g / c := fun V => exitTime_timeScalePath V hc g
  rw [hsc, hsc, ← hgU]
  exact ENNReal.div_le_div_right (GapExit.pathExitTime_mono (f := ⇑g) hsub) _

/-- **Crossing for the rescaled Liouville Brownian law, quenched.** Almost surely, for every starting point `z` and
every continuous `D` whose open set `{D > 0}` is bounded, contains `z`, has every frontier point regular for its
exterior and contains `{D ≥ 0}` in its closure, almost every path under the rescaled Liouville Brownian law from `z`
leaves `{D ≥ 0}` no later than `{D > 0}`. -/
theorem ae_forall_ae_lbmPathLawField_crossing {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ (z : ℂ) (D : C(ℂ, ℝ)), Bornology.IsBounded (gapDomain D) → z ∈ gapDomain D →
      (∀ y ∈ frontier (gapDomain D), ∀ᵐ b ∂planarBrownianMotion y,
        ContinuousPath.exitTime (closure (gapDomain D)) b = 0) →
      {w | 0 ≤ D w} ⊆ closure (gapDomain D) →
      ∀ᵐ f ∂(lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) z : Measure (ContinuousPath ℂ)),
        ContinuousPath.exitTime {w | 0 ≤ D w} f ≤ ContinuousPath.exitTime (gapDomain D) f := by
  have hm0 : 0 < S.m₀ := hS.m₀_pos hγ hγ2
  have hΛ := hS.ae_lbmLawFieldSelection_eq hH hrep (FirstPass.Derived.lbmLawContinuity_of_isValid γ hγ hγ2 Ω S hS)
  have hm : S.m₀ = lbmExitMedian γ := by
    rw [hS.m₀_eq_lawFieldExitMedian hH (measurable_lbmLawFieldSelection_coordCircleGood γ)
      (hΛ.mono fun ω h => h 0), hS.map_pairJ_eq_quantumConeCoordLaw hH hrep, lbmExitMedian]
  set c : ℝ≥0 := (lbmExitMedian γ).toNNReal with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, ← hm]
    exact (Real.toNNReal_pos.2 hm0).ne'
  have hmeas : Measurable (LatticeProb.timeScalePath (E := ℂ) c) :=
    (LatticeProb.continuous_timeScalePath _).measurable
  filter_upwards [hΛ, hS.isLQGClock] with ω hω hclock
  intro z D hDb hzD hreg hsub
  obtain ⟨hg, hK⟩ := hω z
  have h1 : ((lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) z : ProbabilityMeasure (ContinuousPath ℂ)) :
      Measure (ContinuousPath ℂ)) =
      (((lbmLawFieldSelection γ coordCircleGood (LQGMetric.pairJ ⊤ (H ω)) z :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ))).map
        (LatticeProb.timeScalePath c) := by
    rw [lbmPathLawField, rescaledLBMLawField_apply]
    exact ProbabilityMeasure.toMeasure_map _
  have hP : ((lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) z : ProbabilityMeasure (ContinuousPath ℂ)) :
      Measure (ContinuousPath ℂ)) =
      (planarBrownianMotion z).map (fun b => LatticeProb.timeScalePath c (lbmContinuousPath (S.clock ω) b)) := by
    rw [h1, hK]
    exact AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable hg
  have hsetm : MeasurableSet {f : ContinuousPath ℂ |
      ContinuousPath.exitTime {w | 0 ≤ D w} f ≤ ContinuousPath.exitTime (gapDomain D) f} :=
    measurableSet_le (measurable_exitTime_setOf_nonneg.comp (measurable_const.prodMk measurable_id))
      (measurable_exitTime_gapDomain.comp (measurable_const.prodMk measurable_id))
  rw [hP]
  refine (ae_map_iff (hmeas.comp_aemeasurable hg) hsetm).2 ?_
  filter_upwards [(hclock z).2, HarmonicBalls.Section6.ae_exitTime_closure_eq_of_boundary_instant_exit
    (isOpen_gapDomain D) hDb hzD hreg] with b hb hbU
  simp only [Function.comp_apply]
  rw [lbmContinuousPath_of_isTimeChangeClock hb]
  exact crossing_timeScalePath_lbm hb hc hsub hbU

/-- **Crossing of the window on the joint limit, for the Liouville Brownian law.** For `ν''`-almost every sample `q`,
almost every path under the rescaled Liouville Brownian law of the field of `q` from `η(u)` leaves
`{windowGapBG ≥ 0}` no later than the window `{windowGapBG > 0}`. -/
theorem ae_jointLimit_windowGap_crossing {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {E : Ω → LQGData} (hE : Measurable E) {Z : ℕ → Ω → PathLawFamily}
    {ν'' : Measure JointSample} [IsProbabilityMeasure ν'']
    (hconv : ∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
        (𝓝 (∫ q, f q ∂ν'')))
    (hJ : JordanDomainExteriorRegularity) (a u b : ℝ) :
    ∀ᵐ q ∂ν'', ∀ᵐ f ∂(lbmPathLawField γ q.1.1.1 (q.1.2 u) : Measure (ContinuousPath ℂ)),
      ContinuousPath.exitTime {w | 0 ≤ windowGapBG a u b q.1.2 w} f ≤
        ContinuousPath.exitTime (gapDomain (windowGapBG a u b q.1.2)) f := by
  have := hS.isProbabilityMeasure
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  let Data := ((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)
  have hD : Measurable fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    ((measurable_pairJ_top.comp hH).prodMk hE).prodMk hη'
  have hmarg : ν''.map Prod.fst = S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data) :=
    FirstPass.Derived.map_fst_eq_map_of_tendsto_integral hD hconv
  have hκP : Measurable fun x : Data => (lbmPathLawField γ x.1.1 (x.2 u) : ProbabilityMeasure (ContinuousPath ℂ)) :=
    continuous_eval.measurable.comp (((measurable_lbmPathLawField γ).comp (measurable_fst.comp measurable_fst)).prodMk
      ((continuous_eval_const u).measurable.comp measurable_snd))
  let κ : Kernel Data (ContinuousPath ℂ) :=
    ⟨fun x => (lbmPathLawField γ x.1.1 (x.2 u) : Measure (ContinuousPath ℂ)), measurable_subtype_coe.comp hκP⟩
  have : IsMarkovKernel κ := ⟨fun x => by
    show IsProbabilityMeasure (lbmPathLawField γ x.1.1 (x.2 u) : Measure (ContinuousPath ℂ))
    infer_instance⟩
  have hG : Measurable fun p : Data × ContinuousPath ℂ => windowGapBG a u b p.1.2 :=
    (measurable_windowGapBG a u b).comp (measurable_snd.comp measurable_fst)
  have hT : MeasurableSet {p : Data × ContinuousPath ℂ | ¬ (ContinuousPath.exitTime
      {w | 0 ≤ windowGapBG a u b p.1.2 w} p.2 ≤ ContinuousPath.exitTime (gapDomain (windowGapBG a u b p.1.2)) p.2)} :=
    (measurableSet_le (measurable_exitTime_setOf_nonneg.comp (hG.prodMk measurable_snd))
      (measurable_exitTime_gapDomain.comp (hG.prodMk measurable_snd))).compl
  have hQ : MeasurableSet {x : Data | κ x (Prod.mk x ⁻¹' {p : Data × ContinuousPath ℂ | ¬ (ContinuousPath.exitTime
      {w | 0 ≤ windowGapBG a u b p.1.2 w} p.2 ≤
        ContinuousPath.exitTime (gapDomain (windowGapBG a u b p.1.2)) p.2)}) = 0} :=
    (Kernel.measurable_kernel_prodMk_left hT) (measurableSet_singleton 0)
  have hsrc : ∀ᵐ x ∂(S.P.map fun ω => (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω) : Data)),
      κ x (Prod.mk x ⁻¹' {p : Data × ContinuousPath ℂ | ¬ (ContinuousPath.exitTime
        {w | 0 ≤ windowGapBG a u b p.1.2 w} p.2 ≤
          ContinuousPath.exitTime (gapDomain (windowGapBG a u b p.1.2)) p.2)}) = 0 := by
    refine (ae_map_iff hD.aemeasurable hQ).2 ?_
    filter_upwards [ae_forall_ae_lbmPathLawField_crossing hγ hγ2 hS hH hrep] with ω hω
    have hcr : ∀ᵐ f ∂(lbmPathLawField γ (LQGMetric.pairJ ⊤ (H ω)) (η' ω u) : Measure (ContinuousPath ℂ)),
        ContinuousPath.exitTime {w | 0 ≤ windowGapBG a u b (η' ω) w} f ≤
          ContinuousPath.exitTime (gapDomain (windowGapBG a u b (η' ω))) f := by
      by_cases hη : η' ω ∈ windowChartCurves a u b
      · obtain ⟨ψ, hψ⟩ := id hη
        have hU := gapDomain_windowGapBG_of_mem hη
        have hb := isBounded_windowDomain (η' ω) a u b
        have hb' : Bornology.IsBounded (gapDomain (windowGapBG a u b (η' ω))) := by
          rw [hU]
          exact hb
        have hz' : η' ω u ∈ gapDomain (windowGapBG a u b (η' ω)) := by
          rw [hU]
          exact hψ.mem
        have hreg : ∀ y ∈ frontier (gapDomain (windowGapBG a u b (η' ω))), ∀ᵐ β ∂planarBrownianMotion y,
            ContinuousPath.exitTime (closure (gapDomain (windowGapBG a u b (η' ω)))) β = 0 := by
          rw [hU]
          exact hJ _ _ ψ hb hψ
        have hsub : {w | 0 ≤ windowGapBG a u b (η' ω) w} ⊆ closure (gapDomain (windowGapBG a u b (η' ω))) := by
          rw [hU]
          exact setOf_nonneg_windowGapBG_subset hη
        exact hω (η' ω u) (windowGapBG a u b (η' ω)) hb' hz' hreg hsub
      · exact ae_of_all _ fun f => crossing_windowGapBG_of_not_mem hη f
    exact ae_iff.1 hcr
  rw [← hmarg] at hsrc
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hsrc] with q hq
  exact ae_iff.2 hq

/-- **Almost every limiting path from `η(u)` crosses the window.** If moreover the joint limit is almost surely a
linear time change of the Liouville Brownian law field, then for `ν''`-almost every sample `q`, almost every path under
the limiting law `q.2 (η(u))` leaves `{windowGapBG ≥ 0}` no later than the window. -/
theorem ae_jointLimit_crossing_of_speed {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η') {H : Ω → LQGMetric.DistC} (hH : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    {E : Ω → LQGData} (hE : Measurable E) {Z : ℕ → Ω → PathLawFamily}
    {ν'' : Measure JointSample} [IsProbabilityMeasure ν'']
    (hconv : ∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω), Z n ω) ∂S.P) atTop
        (𝓝 (∫ q, f q ∂ν'')))
    (hspeed : ∀ᵐ q ∂ν'', ∃ c : ℝ≥0, c ≠ 0 ∧
      ∀ z, q.2 z = LatticeProb.timeScalePathKernel c (lbmPathLawField γ q.1.1.1) z)
    (hJ : JordanDomainExteriorRegularity) (a u b : ℝ) :
    ∀ᵐ q ∂ν'', ∀ᵐ f ∂(q.2 (q.1.2 u) : Measure (ContinuousPath ℂ)),
      ContinuousPath.exitTime {w | 0 ≤ windowGapBG a u b q.1.2 w} f ≤
        ContinuousPath.exitTime (gapDomain (windowGapBG a u b q.1.2)) f := by
  filter_upwards [hspeed, ae_jointLimit_windowGap_crossing hγ hγ2 hS hη' hH hrep hE hconv hJ a u b]
    with q hq hcr
  obtain ⟨c, hc, hqc⟩ := hq
  have hlaw : (q.2 (q.1.2 u) : Measure (ContinuousPath ℂ)) =
      (lbmPathLawField γ q.1.1.1 (q.1.2 u) : Measure (ContinuousPath ℂ)).map (LatticeProb.timeScalePath c) := by
    rw [hqc]
    rfl
  have hmeas : Measurable (LatticeProb.timeScalePath (E := ℂ) c) :=
    (LatticeProb.continuous_timeScalePath _).measurable
  have hsetm : MeasurableSet {f : ContinuousPath ℂ |
      ContinuousPath.exitTime {w | 0 ≤ windowGapBG a u b q.1.2 w} f ≤
        ContinuousPath.exitTime (gapDomain (windowGapBG a u b q.1.2)) f} :=
    measurableSet_le (measurable_exitTime_setOf_nonneg.comp (measurable_const.prodMk measurable_id))
      (measurable_exitTime_gapDomain.comp (measurable_const.prodMk measurable_id))
  rw [hlaw]
  refine (ae_map_iff hmeas.aemeasurable hsetm).2 ?_
  filter_upwards [hcr] with f hf
  have hts : ∀ V : Set ℂ, ContinuousPath.exitTime V (LatticeProb.timeScalePath c f) =
      ContinuousPath.exitTime V f / c := fun V => exitTime_timeScalePath V hc f
  rw [hts, hts]
  exact ENNReal.div_le_div_right hf _

/-! ### The chart-law coordinates -/

/-- The integrals of a bounded continuous path functional under the chart laws of `{D > 0}` depend continuously on
(law family, starting point, inverse chart, `D`) at every point at which almost every path crosses. -/
theorem continuousAt_integral_chartLaw_gapDomain {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {Kf : P → PathLawFamily} {zf : P → ℂ} {ψf : P → C(ℂ, ℂ)} {Df : P → C(ℂ, ℝ)} {p₀ : P}
    (hK : ContinuousAt Kf p₀) (hz : ContinuousAt zf p₀) (hψ : ContinuousAt ψf p₀) (hD : ContinuousAt Df p₀)
    (hcross : ∀ᵐ x ∂(Kf p₀ (zf p₀) : Measure (ContinuousPath ℂ)),
      ContinuousPath.exitTime {w | 0 ≤ Df p₀ w} x ≤ ContinuousPath.exitTime (gapDomain (Df p₀)) x)
    (g : ContinuousPath ℂ →ᵇ ℝ) :
    ContinuousAt (fun p => ∫ x, g x ∂chartLaw (Kf p) (zf p) (gapDomain (Df p)) (ψf p)) p₀ := by
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro s hs
  exact tendsto_integral_chartLaw_gapDomain (hK.tendsto.comp hs) (hz.tendsto.comp hs) (hψ.tendsto.comp hs)
    (hD.tendsto.comp hs) hcross g

/-- The integrals of a bounded continuous path functional under the chart laws of `{D > 0}` are Borel functions of
(law family, starting point, inverse chart, `D`). -/
theorem measurable_integral_chartLaw_gapDomain {P : Type*} [MeasurableSpace P]
    {Kf : P → PathLawFamily} {zf : P → ℂ} {ψf : P → C(ℂ, ℂ)} {Df : P → C(ℂ, ℝ)}
    (hK : Measurable Kf) (hz : Measurable zf) (hψ : Measurable ψf) (hD : Measurable Df)
    (g : ContinuousPath ℂ →ᵇ ℝ) :
    Measurable fun p => ∫ x, g x ∂chartLaw (Kf p) (zf p) (gapDomain (Df p)) (ψf p) := by
  have hκP : Measurable fun p => (Kf p (zf p) : ProbabilityMeasure (ContinuousPath ℂ)) :=
    continuous_eval.measurable.comp (hK.prodMk hz)
  let κ : Kernel P (ContinuousPath ℂ) :=
    ⟨fun p => (Kf p (zf p) : Measure (ContinuousPath ℂ)), measurable_subtype_coe.comp hκP⟩
  have : IsMarkovKernel κ := ⟨fun p => by
    show IsProbabilityMeasure (Kf p (zf p) : Measure (ContinuousPath ℂ))
    infer_instance⟩
  have hG : Measurable fun q : P × ContinuousPath ℂ => g (chartStopPath (gapDomain (Df q.1)) (ψf q.1) q.2) :=
    g.continuous.measurable.comp (measurable_chartStopPath_gapDomain.comp
      (((hD.comp measurable_fst).prodMk (hψ.comp measurable_fst)).prodMk measurable_snd))
  have hint : ∀ p, ∫ x, g x ∂chartLaw (Kf p) (zf p) (gapDomain (Df p)) (ψf p) =
      ∫ x, g (chartStopPath (gapDomain (Df p)) (ψf p) x) ∂(κ p) := fun p =>
    integral_map (measurable_chartStopPath _ (isOpen_gapDomain (Df p)) _).aemeasurable
      g.continuous.measurable.aestronglyMeasurable
  simp only [hint]
  exact (hG.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

/-! ### The adjoined window coordinates -/

/-- (field coordinates, `E`, curve): the first marginal of the joint samples. -/
abbrev JointSampleData : Type := ((LQGMetric.CoordJ → ℝ) × LQGData) × C(ℝ, ℂ)

/-- The coordinates adjoined for a window: chart field coordinates in `A`, inverse chart, signed distance. -/
abbrev WindowData (A : Finset 𝓓(unitDiscOpens, ℝ)) : Type := (A → ℝ) × (C(ℂ, ℂ) × C(ℂ, ℝ))

/-- The adjoined coordinates of the window `(a, u, b)`, read off (field coordinates, `E`, curve). -/
noncomputable def windowData (γ a u b : ℝ) (A : Finset 𝓓(unitDiscOpens, ℝ)) (x : JointSampleData) :
    WindowData A :=
  (fun i => windowFieldBG γ a u b (LQGMetric.pairJInv ⊤ x.1.1, x.2) i,
    (windowChartBG a u b x.2, windowGapBG a u b x.2))

theorem measurable_windowData (γ a u b : ℝ) (A : Finset 𝓓(unitDiscOpens, ℝ)) :
    Measurable (windowData γ a u b A) := by
  have hf : Measurable fun x : JointSampleData => windowFieldBG γ a u b (LQGMetric.pairJInv ⊤ x.1.1, x.2) :=
    (measurable_windowFieldBG γ a u b).comp
      (((LQGMetric.measurable_pairJInv ⊤).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  exact (Measurable.of_eval fun (i : A) => (measurable_pi_apply (i : 𝓓(unitDiscOpens, ℝ))).comp hf).prodMk
    (((measurable_windowChartBG a u b).comp measurable_snd).prodMk
      ((measurable_windowGapBG a u b).comp measurable_snd))

/-- The integrals of the test functions `g ∈ B` under the chart law of `{D > 0}` for the inverse chart `ψ` and the law
`K z`, where `w = (ψ, D)`. -/
noncomputable def gapLawCoords (B : Finset (ContinuousPath ℂ →ᵇ ℝ)) (K : PathLawFamily) (z : ℂ)
    (w : C(ℂ, ℂ) × C(ℂ, ℝ)) : B → ℝ :=
  fun g => ∫ x, g.1 x ∂chartLaw K z (gapDomain w.2) w.1

/-- The finite coordinates of the window at the curve time `u`, read off the sample `q` and the adjoined
coordinates `y`. -/
noncomputable def windowCoordsAdj {A : Finset 𝓓(unitDiscOpens, ℝ)} (u : ℝ) (B : Finset (ContinuousPath ℂ →ᵇ ℝ))
    (q : JointSample) (y : WindowData A) : (A → ℝ) × (B → ℝ) :=
  (y.1, gapLawCoords B q.2 (q.1.2 u) y.2)

theorem windowCoordsAdj_windowData (γ a u b : ℝ) (A : Finset 𝓓(unitDiscOpens, ℝ))
    (B : Finset (ContinuousPath ℂ →ᵇ ℝ)) (q : JointSample) :
    windowCoordsAdj u B q (windowData γ a u b A q.1) =
      finCoords A B (windowChartField γ a u b (windowChartBG a u b q.1.2) q, windowPLawBG a u b q.1.2 q.2) := by
  refine Prod.ext rfl (funext fun g => ?_)
  show ∫ x, g.1 x ∂chartLaw q.2 (q.1.2 u) (gapDomain (windowGapBG a u b q.1.2)) (windowChartBG a u b q.1.2) =
    ∫ x, g.1 x ∂windowLawBG a u b q.1.2 q.2
  rw [chartLaw_gapDomain_windowGapBG]

/-! ### Berestycki–Gwynne (2020), (7.36): the joint convergence -/

/-- **`BG20WindowJointConvergenceInput` from the crossing property of Jordan domains.** The finite coordinates of the
two windows (chart field, chart law of the window for the interpolated walk law at level `ε n`) converge jointly in law
to those of the joint limit. The window coordinates are Borel functions of (field coordinates, `E`, curve), whose law
is the same at every level, so they may be adjoined to the joint convergence; the chart laws are continuous at
almost every limiting sample since almost every limiting path crosses each window. -/
theorem bg20WindowJointConvergenceInput {𝒮 : SpaceFillingSLEModel} (hJ : JordanDomainExteriorRegularity) :
    BG20WindowJointConvergenceInput 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS η' hη' hae H hH hrep E hE ε hε0 _ ν'' hν'' hconv hspeed a u b a' u' b'
    _ _ _ _ _ A A' B B' Φ
  classical
  have hPP := hS.isProbabilityMeasure
  have hνν := hν''
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  have : PolishSpace C(ℂ, ℂ) := LatticeProb.polishSpace_continuousMap ℂ ℂ
  have : PolishSpace C(ℂ, ℝ) := LatticeProb.polishSpace_continuousMap ℂ ℝ
  have : PolishSpace PathLawFamily :=
    LatticeProb.polishSpace_continuousMap ℂ (ProbabilityMeasure (ContinuousPath ℂ))
  -- the first marginal and the joint samples at level `ε n`
  let data : Ω → JointSampleData := fun ω => ((LQGMetric.pairJ ⊤ (H ω), E ω), η' ω)
  have hdata : Measurable data := ((measurable_pairJ_top.comp hH).prodMk hE).prodMk hη'
  let Zn : ℕ → Ω → JointSample := fun n ω => (data ω, interpWalkLaw S η' (ε n) ω)
  have hZ : ∀ n, AEMeasurable (Zn n) S.P := fun n =>
    hdata.aemeasurable.prodMk (aemeasurable_interpWalkLaw hS hη' hae (hε0 n))
  have hνP : ∀ n, IsProbabilityMeasure (S.P.map (Zn n)) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hZ n)).2 inferInstance
  have hmarg : ν''.map Prod.fst = S.P.map data :=
    FirstPass.Derived.map_fst_eq_map_of_tendsto_integral hdata hconv
  have hνμ : ∀ n, (S.P.map (Zn n)).map Prod.fst = S.P.map data := fun n => by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hZ n)]
    rfl
  have hconv' : ∀ f : JointSample →ᵇ ℝ,
      Tendsto (fun n => ∫ q, f q ∂(S.P.map (Zn n))) atTop (𝓝 (∫ q, f q ∂ν'')) := fun f => by
    have heq : ∀ n, ∫ q, f q ∂(S.P.map (Zn n)) = ∫ ω, f (Zn n ω) ∂S.P := fun n =>
      integral_map (hZ n) f.continuous.aestronglyMeasurable
    simp only [heq]
    exact hconv f
  -- the adjoined window coordinates and the functional of the joint samples
  let F : JointSampleData → WindowData A × WindowData A' := fun x =>
    (windowData γ a u b A x, windowData γ a' u' b' A' x)
  have hF : Measurable F := (measurable_windowData γ a u b A).prodMk (measurable_windowData γ a' u' b' A')
  let Γ : JointSample × (WindowData A × WindowData A') → ℝ := fun p =>
    Φ (windowCoordsAdj u B p.1 p.2.1, windowCoordsAdj u' B' p.1 p.2.2)
  have hKm : Measurable fun p : JointSample × (WindowData A × WindowData A') => p.1.2 :=
    measurable_snd.comp measurable_fst
  have hzm : ∀ t : ℝ, Measurable fun p : JointSample × (WindowData A × WindowData A') => p.1.1.2 t := fun t =>
    (continuous_eval_const t).measurable.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hΓm : Measurable Γ := by
    refine Φ.continuous.measurable.comp ?_
    show Measurable fun p : JointSample × (WindowData A × WindowData A') =>
      ((p.2.1.1, gapLawCoords B p.1.2 (p.1.1.2 u) p.2.1.2), (p.2.2.1, gapLawCoords B' p.1.2 (p.1.1.2 u') p.2.2.2))
    refine Measurable.prodMk (Measurable.prodMk ?_ ?_) (Measurable.prodMk ?_ ?_)
    · exact measurable_fst.comp (measurable_fst.comp measurable_snd)
    · exact Measurable.of_eval fun g => measurable_integral_chartLaw_gapDomain hKm (hzm u)
        (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_snd)))
        (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))) g.1
    · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
    · exact Measurable.of_eval fun g => measurable_integral_chartLaw_gapDomain hKm (hzm u')
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))) g.1
  have hΓb : ∃ C, ∀ p, |Γ p| ≤ C := ⟨‖Φ‖, fun p => by
    rw [← Real.norm_eq_abs]
    exact Φ.norm_coe_le_norm _⟩
  -- almost every limiting path crosses both windows
  have hcr1 := ae_jointLimit_crossing_of_speed hγ hγ2 hS hη' hH hrep hE hconv hspeed hJ a u b
  have hcr2 := ae_jointLimit_crossing_of_speed hγ hγ2 hS hη' hH hrep hE hconv hspeed hJ a' u' b'
  have hΓc : ∀ᵐ q ∂ν'', ContinuousAt Γ (q, F q.1) := by
    filter_upwards [hcr1, hcr2] with q h1 h2
    have hK : ContinuousAt (fun p : JointSample × (WindowData A × WindowData A') => p.1.2) (q, F q.1) :=
      (continuous_snd.comp continuous_fst).continuousAt
    have hz : ∀ t : ℝ, ContinuousAt (fun p : JointSample × (WindowData A × WindowData A') => p.1.1.2 t)
        (q, F q.1) := fun t =>
      ((continuous_eval_const t).comp (continuous_snd.comp (continuous_fst.comp continuous_fst))).continuousAt
    refine Φ.continuous.continuousAt.comp (f := fun p : JointSample × (WindowData A × WindowData A') =>
      ((p.2.1.1, gapLawCoords B p.1.2 (p.1.1.2 u) p.2.1.2),
        (p.2.2.1, gapLawCoords B' p.1.2 (p.1.1.2 u') p.2.2.2))) ?_
    refine ContinuousAt.prodMk (ContinuousAt.prodMk ?_ ?_) (ContinuousAt.prodMk ?_ ?_)
    · exact (continuous_fst.comp (continuous_fst.comp continuous_snd)).continuousAt
    · exact continuousAt_pi.2 fun g => continuousAt_integral_chartLaw_gapDomain hK (hz u)
        (continuous_fst.comp (continuous_snd.comp (continuous_fst.comp continuous_snd))).continuousAt
        (continuous_snd.comp (continuous_snd.comp (continuous_fst.comp continuous_snd))).continuousAt h1 g.1
    · exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousAt
    · exact continuousAt_pi.2 fun g => continuousAt_integral_chartLaw_gapDomain hK (hz u')
        (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).continuousAt
        (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).continuousAt h2 g.1
  have hmain := tendsto_integral_comp_prodMk_of_ae_continuousAt (X := JointSampleData) (K := PathLawFamily)
    (Y := WindowData A × WindowData A') (ν := fun n => S.P.map (Zn n)) (ν₀ := ν'') (μ := S.P.map data)
    hνμ hmarg hconv' hF hΓm hΓb hΓc
  -- identification of the two sides
  have hpt : ∀ q : JointSample, Γ (q, F q.1) =
      Φ (finCoords A B (windowChartField γ a u b (windowChartBG a u b q.1.2) q, windowPLawBG a u b q.1.2 q.2),
        finCoords A' B' (windowChartField γ a' u' b' (windowChartBG a' u' b' q.1.2) q,
          windowPLawBG a' u' b' q.1.2 q.2)) := fun q => by
    show Φ (windowCoordsAdj u B q (windowData γ a u b A q.1),
      windowCoordsAdj u' B' q (windowData γ a' u' b' A' q.1)) = _
    rw [windowCoordsAdj_windowData, windowCoordsAdj_windowData]
  have hptZ : ∀ n ω, Γ (Zn n ω, F (Zn n ω).1) =
      Φ (finCoords A B (windowFieldBG γ a u b (H ω, η' ω),
          windowPLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)),
        finCoords A' B' (windowFieldBG γ a' u' b' (H ω, η' ω),
          windowPLawBG a' u' b' (η' ω) (interpWalkLaw S η' (ε n) ω))) := fun n ω => by
    rw [hpt]
    show Φ (finCoords A B (windowFieldBG γ a u b (LQGMetric.pairJInv ⊤ (LQGMetric.pairJ ⊤ (H ω)), η' ω),
          windowPLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)),
        finCoords A' B' (windowFieldBG γ a' u' b' (LQGMetric.pairJInv ⊤ (LQGMetric.pairJ ⊤ (H ω)), η' ω),
          windowPLawBG a' u' b' (η' ω) (interpWalkLaw S η' (ε n) ω))) = _
    rw [LQGMetric.pairJInv_pairJ]
  have hΓF : Measurable fun q : JointSample => Γ (q, F q.1) :=
    hΓm.comp (measurable_id.prodMk (hF.comp measurable_fst))
  have hlhs : ∀ n, ∫ q, Γ (q, F q.1) ∂(S.P.map (Zn n)) =
      ∫ ω, Φ (finCoords A B (windowFieldBG γ a u b (H ω, η' ω),
          windowPLawBG a u b (η' ω) (interpWalkLaw S η' (ε n) ω)),
        finCoords A' B' (windowFieldBG γ a' u' b' (H ω, η' ω),
          windowPLawBG a' u' b' (η' ω) (interpWalkLaw S η' (ε n) ω))) ∂S.P := fun n => by
    rw [integral_map (hZ n) hΓF.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ (hptZ n))
  have hrhs : ∫ q, Γ (q, F q.1) ∂ν'' =
      ∫ q, Φ (finCoords A B (windowChartField γ a u b (windowChartBG a u b q.1.2) q, windowPLawBG a u b q.1.2 q.2),
        finCoords A' B' (windowChartField γ a' u' b' (windowChartBG a' u' b' q.1.2) q,
          windowPLawBG a' u' b' q.1.2 q.2)) ∂ν'' :=
    integral_congr_ae (ae_of_all _ hpt)
  have h2 := hmain.congr' (Eventually.of_forall hlhs)
  rw [hrhs] at h2
  exact h2

end MatedCRT
