import MatedCRT.FirstPass.Derived.StopAtExitGoodEventBM
import MatedCRT.FirstPass.Derived.UniformStartStoppedBM

/-!
# The oscillation clause of the good stopping event, uniformly in the starting point

`MatedCRT.StopAtExitCmp.GoodStop U T η d ε f` asks, besides two clauses involving the exit time from `U`, that `f`
oscillates by at most `ε` between rational times of `[0, T + 1]` at distance less than `2 η`. This clause only
involves differences of values of `f`, so it is invariant under translation of the path, and the probability that
it fails for planar Brownian motion does not depend on the starting point. By uniform continuity on `[0, T + 1]`
it tends to `0` as `η → 0`. Hence, for every `θ > 0` there is one `η > 0` such that the oscillation clause fails
with probability less than `θ` for planar Brownian motion started at every point `z : ℂ`.

* `MatedCRT.StopAtExitCmp.oscillationBad`: the set of paths violating the oscillation clause.
* `MatedCRT.StopAtExitCmp.measurableSet_oscillationBad`: measurability.
* `MatedCRT.StopAtExitCmp.exists_forall_planarBrownianMotion_oscillationBad_lt`: the bound, uniform in the start.
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- The paths violating the oscillation clause of `GoodStop`: for some rational times of `[0, T + 1]` at distance
less than `2 η` the values differ by more than `ε`. -/
def oscillationBad (T η : ℝ≥0) (ε : ℝ) : Set (ContinuousPath ℂ) :=
  {b | ¬ ∀ q q' : ℚ, ratTime q ≤ T + 1 → ratTime q' ≤ T + 1 →
    dist (ratTime q) (ratTime q') < 2 * (η : ℝ) → dist (b (ratTime q)) (b (ratTime q')) ≤ ε}

/-- The set of paths violating the oscillation clause is measurable. -/
theorem measurableSet_oscillationBad (T η : ℝ≥0) (ε : ℝ) : MeasurableSet (oscillationBad T η ε) := by
  have hF : ∀ t : ℝ≥0, Measurable fun b : ContinuousPath ℂ => b t := fun t =>
    (ContinuousPath.continuous_eval t).measurable
  refine MeasurableSet.compl (measurableSet_setOfPred.2 ?_)
  refine Measurable.forall fun q => Measurable.forall fun q' => ?_
  exact measurable_const.imp (measurable_const.imp (measurable_const.imp
    (measurableSet_setOfPred.1 (measurableSet_le ((hF _).dist (hF _)) measurable_const))))

/-- The oscillation clause only involves differences of values, so its violation set is translation invariant. -/
theorem translatePath_preimage_oscillationBad (z : ℂ) (T η : ℝ≥0) (ε : ℝ) :
    translatePath z ⁻¹' oscillationBad T η ε = oscillationBad T η ε := by
  ext b
  simp only [oscillationBad, mem_preimage, mem_ofPred_eq, translatePath_apply, dist_add_right]

/-- The violation sets decrease as `η` decreases. -/
theorem oscillationBad_anti {T η η' : ℝ≥0} (ε : ℝ) (h : η' ≤ η) :
    oscillationBad T η' ε ⊆ oscillationBad T η ε := by
  intro b hb hgood
  refine hb fun q q' hq hq' hd => hgood q q' hq hq' (hd.trans_le ?_)
  have : (η' : ℝ) ≤ η := by exact_mod_cast h
  linarith

/-- **The oscillation clause, uniformly in the starting point.** For every horizon `T`, `ε > 0` and `θ > 0` there is
`η > 0` such that for planar Brownian motion started at every `z : ℂ` the probability of the paths violating the
oscillation clause of `GoodStop` is less than `θ`. -/
theorem exists_forall_planarBrownianMotion_oscillationBad_lt (T : ℝ≥0) {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ z : ℂ, planarBrownianMotion z (oscillationBad T η ε) < ENNReal.ofReal θ := by
  obtain ⟨η, hη⟩ : ∃ η : ℕ → ℝ≥0, ∀ m, η m = Real.toNNReal (1 / ((m : ℝ) + 1)) := ⟨_, fun _ => rfl⟩
  have hηr : ∀ m : ℕ, (η m : ℝ) = 1 / ((m : ℝ) + 1) := fun m => by
    rw [hη m]; exact Real.coe_toNNReal _ (by positivity)
  have hη0 : ∀ m, 0 < η m := fun m => by
    rw [hη m]; exact Real.toNNReal_pos.2 (by positivity)
  have hηanti : Antitone η := fun m m' hmm' => by
    rw [hη m, hη m']
    refine Real.toNNReal_le_toNNReal ?_
    gcongr
  have hanti : Antitone fun m => oscillationBad T (η m) ε := fun m m' hmm' =>
    oscillationBad_anti ε (hηanti hmm')
  have hempty : (⋂ m, oscillationBad T (η m) ε) = ∅ := by
    refine eq_empty_of_forall_notMem fun b hb => ?_
    obtain ⟨δ, hδ, hbδ⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc (a := (0 : ℝ≥0)) (b := T + 1)).uniformContinuousOn_of_continuous
        b.continuous.continuousOn) ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < δ / 2 by positivity)
    refine mem_iInter.1 hb m fun q q' hq hq' hd => ?_
    have hd' : dist (ratTime q) (ratTime q') < δ := by
      have := hηr m
      linarith
    exact (hbδ _ ⟨zero_le, hq⟩ _ ⟨zero_le, hq'⟩ hd').le
  have hμ : Tendsto (fun m => planarBrownianMotion 0 (oscillationBad T (η m) ε)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := planarBrownianMotion 0)
      (fun m => (measurableSet_oscillationBad T (η m) ε).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rwa [hempty, measure_empty] at this
  obtain ⟨m, hm⟩ := (hμ.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hθ))).exists
  refine ⟨η m, hη0 m, fun z => ?_⟩
  rw [planarBrownianMotion_apply_eq_translatePath z, translatePath_preimage_oscillationBad]
  exact hm

end MatedCRT.StopAtExitCmp
