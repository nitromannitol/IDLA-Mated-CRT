import MatedCRT.FirstPass.Derived.StopAtExitCmpQuantitative

/-!
# A measurable event on which the stopping map has an explicit modulus of continuity

`MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_le_of_modulus` bounds `cmpEDist (stopAtExit U g) (stopAtExit U f)` by
`2 ε` for every `g` within curve distance `min ε d` of `f`, under three conditions on `f`: a modulus of continuity on
`[0, T]`, an exit witness `s ∈ (τ, τ + η)` whose `d`-ball lies outside `U`, and the `d`-tube of `f` before
`τ - η / 2` inside `U`. Here these conditions are replaced by conditions at rational times,

* an exit witness at a rational time `s ≤ T`,
* oscillation at most `ε` between rational times of `[0, T + 1]` at distance less than `2 η`,
* the `d`-balls about `f q` inside `U` at rational times `q` with `q + η / 4 < τ`,

which make up the event `GoodStop U T η d ε f`. For a continuous path the rational conditions imply the real ones,
so the bound holds on `GoodStop`; and for every family of paths whose coordinates and exit time from `U` are
measurable, `GoodStop` is a measurable event. This is the step that lets the almost sure continuity of the stopping
map at Brownian paths be made uniform in the starting point, for the uniform-start invariance principle
`MatedCRT.GMS21UniformStartInput`.

## Main statements

* `MatedCRT.StopAtExitCmp.GoodStop`: the event.
* `MatedCRT.StopAtExitCmp.cmpEDist_stopAtExit_le_of_goodStop`: the quantitative continuity on the event.
* `MatedCRT.StopAtExitCmp.measurable_goodStop`, `measurableSet_goodStop_continuousPath`: measurability.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- The rational time `q` as a point of `[0, ∞)` (negative rationals are sent to `0`). -/
noncomputable def ratTime (q : ℚ) : ℝ≥0 := Real.toNNReal q

/-- A continuous path is approximated at every time `t` by its values at rational times slightly after `t`. -/
theorem exists_ratTime_near {f : ℝ≥0 → ℂ} (hf : Continuous f) (t : ℝ≥0) {r δ : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) :
    ∃ q : ℚ, t < ratTime q ∧ (ratTime q : ℝ) < t + δ ∧ dist (f (ratTime q)) (f t) < r := by
  obtain ⟨δ', hδ', hδ'f⟩ := Metric.continuousAt_iff.1 hf.continuousAt r hr
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (t : ℝ) (lt_min hδ hδ'))
  have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg t).trans hq1.le
  have hcoe : ((ratTime q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, hcoe]
    exact hq1
  · rw [hcoe]
    have := min_le_left δ δ'
    linarith
  · apply hδ'f
    rw [NNReal.dist_eq, hcoe, abs_of_pos (sub_pos.2 hq1)]
    have := min_le_right δ δ'
    linarith

/-- The set of points whose open `r`-ball lies in `V` is closed. -/
theorem isClosed_setOf_forall_dist_lt_imp_mem (V : Set ℂ) (r : ℝ) :
    IsClosed {x : ℂ | ∀ w, dist w x < r → w ∈ V} := by
  have h : {x : ℂ | ∀ w, dist w x < r → w ∈ V} = ⋂ w ∈ Vᶜ, {x : ℂ | dist w x < r}ᶜ := by
    ext x
    constructor
    · intro hx
      refine mem_iInter₂.2 fun w hw => ?_
      intro hlt
      exact hw (hx w hlt)
    · intro hx w hlt
      by_contra hw
      exact mem_iInter₂.1 hx w hw hlt
  rw [h]
  exact isClosed_biInter fun w _ =>
    (isOpen_lt (continuous_const.dist continuous_id) continuous_const :
      IsOpen {x : ℂ | dist w x < r}).isClosed_compl

/-- **The good event of the stopping map.** For a path `f`, an open set `U`, a horizon `T`, a time scale `η` and
radii `d`, `ε`: an exit witness at a rational time `s ≤ T` in `(τ, τ + η)` whose `d`-ball lies outside `U`
(`τ = pathExitTime U f`); oscillation at most `ε` between rational times of `[0, T + 1]` at distance less than
`2 η`; and the `d`-balls about `f q` inside `U` at the rational times `q` with `q + η / 4 < τ`. -/
def GoodStop (U : Set ℂ) (T η : ℝ≥0) (d ε : ℝ) (f : ℝ≥0 → ℂ) : Prop :=
  (∃ q : ℚ, pathExitTime U f < ratTime q ∧ (ratTime q : ℝ≥0∞) < pathExitTime U f + η ∧
      ratTime q ≤ T ∧ ∀ w, dist w (f (ratTime q)) < d → w ∉ U) ∧
    (∀ q q' : ℚ, ratTime q ≤ T + 1 → ratTime q' ≤ T + 1 → dist (ratTime q) (ratTime q') < 2 * (η : ℝ) →
      dist (f (ratTime q)) (f (ratTime q')) ≤ ε) ∧
    ∀ q : ℚ, ((ratTime q + η / 4 : ℝ≥0) : ℝ≥0∞) < pathExitTime U f →
      ∀ w, dist w (f (ratTime q)) < d → w ∈ U

/-- The rational modulus of `GoodStop` gives the modulus of continuity on `[0, T]` at scale `η`. -/
theorem modulus_of_ratTime {f : ℝ≥0 → ℂ} (hf : Continuous f) {T η : ℝ≥0} {ε : ℝ} (hη : 0 < η)
    (hmod : ∀ q q' : ℚ, ratTime q ≤ T + 1 → ratTime q' ≤ T + 1 →
      dist (ratTime q) (ratTime q') < 2 * (η : ℝ) → dist (f (ratTime q)) (f (ratTime q')) ≤ ε) :
    ∀ t ≤ T, ∀ t' ≤ T, dist t t' < η → dist (f t) (f t') ≤ ε := by
  intro t ht t' ht' htt'
  have hη' : (0 : ℝ) < η := NNReal.coe_pos.2 hη
  refine le_of_forall_pos_lt_add fun r hr => ?_
  have hδ : (0 : ℝ) < min 1 (η : ℝ) := lt_min one_pos hη'
  obtain ⟨q, hq1, hq2, hq3⟩ := exists_ratTime_near hf t (half_pos hr) hδ
  obtain ⟨q', hq1', hq2', hq3'⟩ := exists_ratTime_near hf t' (half_pos hr) hδ
  have hle : ∀ {s u : ℝ≥0}, u ≤ T → (s : ℝ) < u + min 1 (η : ℝ) → s ≤ T + 1 := by
    intro s u hu hs
    rw [← NNReal.coe_le_coe]
    push_cast
    have := NNReal.coe_le_coe.2 hu
    have := min_le_left (1 : ℝ) η
    linarith
  have hd : dist (ratTime q) (ratTime q') < 2 * (η : ℝ) := by
    rw [NNReal.dist_eq] at htt' ⊢
    have h1 := NNReal.coe_lt_coe.2 hq1
    have h2 := NNReal.coe_lt_coe.2 hq1'
    rw [abs_sub_lt_iff] at htt' ⊢
    have := min_le_right (1 : ℝ) η
    constructor <;> linarith [htt'.1, htt'.2]
  have hmain := hmod q q' (hle ht hq2) (hle ht' hq2') hd
  have htri := dist_triangle4 (f t) (f (ratTime q)) (f (ratTime q')) (f t')
  rw [dist_comm (f t) (f (ratTime q))] at htri
  linarith

/-- The rational tube condition of `GoodStop` gives the `d`-tube of `f` inside `U` before `τ - η / 2`. -/
theorem tube_of_ratTime {U : Set ℂ} {f : ℝ≥0 → ℂ} (hf : Continuous f) {η τ : ℝ≥0} {d : ℝ} (hη : 0 < η)
    (hτ : pathExitTime U f = τ)
    (htube : ∀ q : ℚ, ((ratTime q + η / 4 : ℝ≥0) : ℝ≥0∞) < pathExitTime U f →
      ∀ w, dist w (f (ratTime q)) < d → w ∈ U) :
    ∀ t, t + η / 2 ≤ τ → ∀ w, dist w (f t) < d → w ∈ U := by
  intro t ht w hw
  have hη' : (0 : ℝ) < η := NNReal.coe_pos.2 hη
  obtain ⟨q, hq1, hq2, hq3⟩ :=
    exists_ratTime_near hf t (sub_pos.2 hw) (div_pos hη' (by norm_num : (0 : ℝ) < 4))
  have hlt : ratTime q + η / 4 < τ := by
    rw [← NNReal.coe_lt_coe]
    have := NNReal.coe_le_coe.2 ht
    push_cast at this ⊢
    linarith
  refine htube q (by rw [hτ]; exact ENNReal.coe_lt_coe.2 hlt) w ?_
  have htri := dist_triangle w (f t) (f (ratTime q))
  rw [dist_comm (f t) (f (ratTime q))] at htri
  linarith

/-- **Quantitative continuity of the stopping map on the good event.** If the continuous path `f` lies in
`GoodStop U T η d ε` with `η > 0`, then every path `g` within curve distance `min ε d` of `f` has, once stopped at
its exit time from `U`, curve distance at most `2 ε` from `f` stopped at its exit time. -/
theorem cmpEDist_stopAtExit_le_of_goodStop {U : Set ℂ} {T η : ℝ≥0} {d ε : ℝ} {f : ℝ≥0 → ℂ}
    (hf : Continuous f) (hη : 0 < η) (hgood : GoodStop U T η d ε f) {g : ℝ≥0 → ℂ}
    (hg : cmpEDist g f < ENNReal.ofReal (min ε d)) :
    cmpEDist (stopAtExit U g) (stopAtExit U f) ≤ ENNReal.ofReal (2 * ε) := by
  obtain ⟨⟨q, hq1, hq2, hqT, hout⟩, hmod, htube⟩ := hgood
  have hfin : pathExitTime U f ≠ ⊤ := ne_top_of_lt hq1
  have hτ : pathExitTime U f = ((pathExitTime U f).toNNReal : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal hfin).symm
  have hs : ratTime q ∈ Ioo (pathExitTime U f).toNNReal ((pathExitTime U f).toNNReal + η) := by
    rw [hτ] at hq1 hq2
    refine ⟨ENNReal.coe_lt_coe.1 hq1, ?_⟩
    rw [← ENNReal.coe_add] at hq2
    exact ENNReal.coe_lt_coe.1 hq2
  exact cmpEDist_stopAtExit_le_of_modulus hτ hη (modulus_of_ratTime hf hη hmod) hs hqT hout
    (tube_of_ratTime hf hη hτ htube) hg

/-- **Measurability of the good event.** For a family of paths `F ω` whose coordinates `F ω t` and exit time from
`U` are measurable functions of `ω`, the event `GoodStop U T η d ε (F ω)` is measurable. -/
theorem measurable_goodStop {Ω : Type*} [MeasurableSpace Ω] {U : Set ℂ} (T η : ℝ≥0) (d ε : ℝ)
    {F : Ω → ℝ≥0 → ℂ} (hF : ∀ t, Measurable fun ω => F ω t)
    (hτ : Measurable fun ω => pathExitTime U (F ω)) :
    Measurable fun ω => GoodStop U T η d ε (F ω) := by
  have hball : ∀ (V : Set ℂ) (c : ℝ≥0) (r : ℝ), Measurable fun ω => ∀ w, dist w (F ω c) < r → w ∈ V :=
    fun V c r => measurableSet_setOfPred.1 (hF c (isClosed_setOf_forall_dist_lt_imp_mem V r).measurableSet)
  unfold GoodStop
  refine Measurable.and ?_ (Measurable.and ?_ ?_)
  · refine Measurable.exists fun q => ?_
    exact (measurableSet_setOfPred.1 (measurableSet_lt hτ measurable_const)).and
      ((measurableSet_setOfPred.1 (measurableSet_lt measurable_const (hτ.add_const _))).and
        (measurable_const.and (hball Uᶜ _ d)))
  · refine Measurable.forall fun q => Measurable.forall fun q' => ?_
    exact measurable_const.imp (measurable_const.imp (measurable_const.imp
      (measurableSet_setOfPred.1 (measurableSet_le ((hF _).dist (hF _)) measurable_const))))
  · refine Measurable.forall fun q => ?_
    exact (measurableSet_setOfPred.1 (measurableSet_lt measurable_const hτ)).imp (hball U _ d)

/-- The good event is a Borel set of continuous paths for every open set `U`. -/
theorem measurableSet_goodStop_continuousPath {U : Set ℂ} (hU : IsOpen U) (T η : ℝ≥0) (d ε : ℝ) :
    MeasurableSet {ω : MarkovProcess.ContinuousPath ℂ | GoodStop U T η d ε ⇑ω} :=
  measurableSet_setOfPred.2 (measurable_goodStop T η d ε
    (fun t => (MarkovProcess.ContinuousPath.continuous_eval t).measurable)
    (MarkovProcess.ContinuousPath.measurable_exitTime U hU))

end MatedCRT.StopAtExitCmp
