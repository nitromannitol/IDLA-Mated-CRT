import MatedCRT.FirstPass.Derived.StopAtExitLocalUniform

/-!
# Almost every radius is a regular exit radius for a fixed law of paths

For a continuous planar path `X` and `r > 0` say that `X` exits `B_r(0)` irregularly when it leaves the disc at
a finite time `τ` but stays in the closed disc on an interval `(τ, τ + ε)`
(`¬ MatedCRT.TruncatedLaws.RegularExit (ball 0 r) X`). Then `r` is the running maximum `max_{u ≤ s} |X u|` at a
rational (more precisely: dense-set) time `s` where the running maximum is flat on `[s, s']`. So the exceptional
radii of one path form a countable set, and for every Borel law `μ` of paths the exceptional set
`{(X, r) | r ∈ (exceptional radii of X)}` is a measurable set of Lebesgue-null sections: for Lebesgue-almost
every `r`, `μ`-almost every path exits `B_r(0)` regularly (possibly never).

## Main statements

* `MatedCRT.RegularRadius.notMem_at_exitTime`: a continuous path is outside the open set `U` at its exit time.
* `MatedCRT.RegularRadius.exists_runMax_flat_of_not_regularExit`: an irregular exit radius is the value of the
  running maximum at a time of a dense set `D` where it is flat up to a later time of `D`.
* `MatedCRT.RegularRadius.ae_ae_regularExit_ball`: for every s-finite law `μ` of continuous planar paths,
  for Lebesgue-almost every `r`, `μ`-almost every path exits `ball 0 r` regularly.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.RegularRadius

open MatedCRT.StopAtExitCmp MatedCRT.TruncatedLaws

/-- A continuous path with a finite exit time from an open set is outside the set at that time. -/
theorem notMem_at_exitTime {U : Set ℂ} (hU : IsOpen U) {f : ℝ≥0 → ℂ} (hf : Continuous f)
    (hfin : pathExitTime U f ≠ ⊤) : f (pathExitTime U f).toNNReal ∉ U := by
  intro hmem
  set τ : ℝ≥0 := (pathExitTime U f).toNNReal with hτ
  have hτe : pathExitTime U f = τ := (ENNReal.coe_toNNReal hfin).symm
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hf) τ hmem
  set e : ℝ≥0 := (η / 2).toNNReal with he
  have he0 : (e : ℝ) = η / 2 := Real.coe_toNNReal _ (by positivity)
  have hepos : 0 < e := by
    rw [← NNReal.coe_pos, he0]
    positivity
  have hall : ∀ t ≤ τ + e, f t ∈ U := by
    intro t ht
    by_cases hlt : t < τ
    · exact mem_of_lt_exitTime (by rw [hτe]; exact_mod_cast hlt)
    · apply hball
      rw [mem_ball, NNReal.dist_eq, abs_of_nonneg (by
        have : (τ : ℝ) ≤ t := by exact_mod_cast not_lt.mp hlt
        linarith)]
      have : (t : ℝ) ≤ τ + e := by exact_mod_cast ht
      linarith
  have h := le_exitTime_of_forall_le_mem hall
  rw [hτe] at h
  have h' : τ + e ≤ τ := by exact_mod_cast h
  exact absurd h' (not_le.mpr (lt_add_of_pos_right _ hepos))

/-- The running maximum `max_{u ≤ s} |X u|` of a continuous planar path. -/
noncomputable def runMax (s : ℝ≥0) (X : ContinuousPath ℂ) : ℝ :=
  ‖X.restrict (Icc (0 : ℝ≥0) s)‖

theorem continuous_runMax (s : ℝ≥0) : Continuous (runMax s) :=
  continuous_norm.comp (ContinuousMap.continuous_restrict _)

theorem norm_le_runMax {X : ContinuousPath ℂ} {s t : ℝ≥0} (ht : t ≤ s) : ‖X t‖ ≤ runMax s X :=
  ContinuousMap.norm_coe_le_norm (X.restrict (Icc (0 : ℝ≥0) s)) ⟨t, bot_le, ht⟩

theorem runMax_le {X : ContinuousPath ℂ} {s : ℝ≥0} {C : ℝ} (hC : 0 ≤ C) (h : ∀ t ≤ s, ‖X t‖ ≤ C) :
    runMax s X ≤ C :=
  (ContinuousMap.norm_le _ hC).2 fun x => h x.1 x.2.2

/-- **Irregular exit radii are flat values of the running maximum.** If `X` exits `ball 0 r` irregularly,
then for a dense set `D` of times there are `s < s'` in `D` with `r = max_{u ≤ s} |X u|` and
`max_{u ≤ s'} |X u| ≤ r`. -/
theorem exists_runMax_flat_of_not_regularExit {D : Set ℝ≥0} (hD : Dense D) {X : ContinuousPath ℂ} {r : ℝ}
    (hreg : ¬ RegularExit (ball (0 : ℂ) r) ⇑X) :
    ∃ s ∈ D, ∃ s' ∈ D, s < s' ∧ r = runMax s X ∧ runMax s' X ≤ r := by
  unfold RegularExit at hreg
  push Not at hreg
  obtain ⟨hfin, hev⟩ := hreg
  set τ : ℝ≥0 := (pathExitTime (ball (0 : ℂ) r) ⇑X).toNNReal with hτ
  have hτe : pathExitTime (ball (0 : ℂ) r) ⇑X = τ := (ENNReal.coe_toNNReal hfin).symm
  have hr : 0 < r := by
    by_contra hr
    have hempty : ball (0 : ℂ) r = ∅ := ball_eq_empty.2 (not_lt.mp hr)
    obtain ⟨t, ht⟩ := hev.exists
    rw [hempty, closure_empty] at ht
    exact ht
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hτu : τ < u := hu
  have hcl : ∀ t ∈ Ioo τ u, ‖X t‖ ≤ r := fun t ht => by
    have := closure_ball_subset_closedBall (hsub ht)
    simpa using this
  have hclosed : IsClosed {t : ℝ≥0 | ‖X t‖ ≤ r} := isClosed_le (continuous_norm.comp X.continuous) continuous_const
  have hτle : ‖X τ‖ ≤ r := by
    have h1 : closure (Ioo τ u) ⊆ {t : ℝ≥0 | ‖X t‖ ≤ r} := closure_minimal hcl hclosed
    rw [closure_Ioo hτu.ne] at h1
    exact h1 ⟨le_rfl, hτu.le⟩
  have hτge : r ≤ ‖X τ‖ := by
    have := notMem_at_exitTime isOpen_ball X.continuous hfin
    simpa using this
  obtain ⟨s, hsD, hs⟩ := hD.exists_between hτu
  obtain ⟨s', hs'D, hs'⟩ := hD.exists_between hs.2
  have hall : ∀ t ≤ s', ‖X t‖ ≤ r := by
    intro t ht
    by_cases hlt : t < τ
    · have hmem : X t ∈ ball (0 : ℂ) r :=
        mem_of_lt_exitTime (by rw [hτe]; exact_mod_cast hlt)
      exact (mem_ball_zero_iff.1 hmem).le
    · by_cases heq : t = τ
      · rw [heq]; exact hτle
      · exact hcl t ⟨lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm heq), lt_of_le_of_lt ht hs'.2⟩
  refine ⟨s, hsD, s', hs'D, hs'.1, le_antisymm ?_ ?_, runMax_le hr.le hall⟩
  · exact hτge.trans (norm_le_runMax hs.1.le)
  · exact runMax_le hr.le fun t ht => hall t (ht.trans hs'.1.le)

/-- The set of pairs `(X, r)` such that `r` is a flat value of the running maximum of `X` at times of `D`. -/
def flatValueSet (D : Set ℝ≥0) : Set (ContinuousPath ℂ × ℝ) :=
  ⋃ s ∈ D, ⋃ s' ∈ D, {p | s < s' ∧ p.2 = runMax s p.1 ∧ runMax s' p.1 ≤ p.2}

theorem measurableSet_flatValueSet {D : Set ℝ≥0} (hD : D.Countable) : MeasurableSet (flatValueSet D) := by
  refine MeasurableSet.biUnion hD fun s _ => MeasurableSet.biUnion hD fun s' _ => ?_
  have h1 : MeasurableSet {p : ContinuousPath ℂ × ℝ | p.2 = runMax s p.1} :=
    measurableSet_eq_fun measurable_snd ((continuous_runMax s).measurable.comp measurable_fst)
  have h2 : MeasurableSet {p : ContinuousPath ℂ × ℝ | runMax s' p.1 ≤ p.2} :=
    measurableSet_le ((continuous_runMax s').measurable.comp measurable_fst) measurable_snd
  exact (MeasurableSet.const (s < s')).inter (h1.inter h2)

/-- For every path the flat values of the running maximum at times of a countable set form a countable set. -/
theorem countable_section_flatValueSet {D : Set ℝ≥0} (hD : D.Countable) (X : ContinuousPath ℂ) :
    {r : ℝ | (X, r) ∈ flatValueSet D}.Countable := by
  refine (hD.image fun s => runMax s X).mono ?_
  intro r hr
  simp only [flatValueSet, mem_iUnion] at hr
  obtain ⟨s, hs, s', hs', _, hr1, _⟩ := hr
  exact ⟨s, hs, hr1.symm⟩

/-- **Almost every radius is a regular exit radius.** For every s-finite law `μ` of continuous planar paths and
Lebesgue-almost every `r`, `μ`-almost every path exits `ball 0 r` regularly (it never exits, or it is outside the
closure at times arbitrarily close to its exit time from above). -/
theorem ae_ae_regularExit_ball (μ : Measure (ContinuousPath ℂ)) [SFinite μ] :
    ∀ᵐ r ∂(volume : Measure ℝ), ∀ᵐ (X : ContinuousPath ℂ) ∂μ, RegularExit (ball (0 : ℂ) r) ⇑X := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have h1 : ∀ᵐ X ∂μ, ∀ᵐ r ∂(volume : Measure ℝ), (X, r) ∉ flatValueSet D :=
    Filter.Eventually.of_forall fun X => (countable_section_flatValueSet hDc X).ae_notMem volume
  have hm : MeasurableSet {z : ContinuousPath ℂ × ℝ | (z.1, z.2) ∉ flatValueSet D} :=
    (measurableSet_flatValueSet hDc).compl
  have h2 := (Measure.ae_ae_comm (μ := μ) (ν := volume)
    (p := fun X r => (X, r) ∉ flatValueSet D) hm).1 h1
  filter_upwards [h2] with r hr
  filter_upwards [hr] with X hX
  by_contra hreg
  obtain ⟨s, hs, s', hs', hss, h1', h2'⟩ := exists_runMax_flat_of_not_regularExit hDd hreg
  exact hX (mem_biUnion hs (mem_biUnion hs' ⟨hss, h1', h2'⟩))

end MatedCRT.RegularRadius
