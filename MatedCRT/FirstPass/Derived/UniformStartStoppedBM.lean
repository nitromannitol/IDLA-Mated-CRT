import MatedCRT.FirstPass.Derived.UniformStopAtExit
import MatedCRT.FirstPass.Derived.StopAtExitNested
import HarmonicBalls.Proofs.Sec6.BrownianScaling
import MarkovProcess.Path.RandomShiftMeasurability
import MarkovProcess.Path.ExitTimeShift

/-!
# Planar Brownian motion stopped at an exit time, for nearby start points

Planar Brownian motion started at `y` is the image of planar Brownian motion started at `0` under
the translation `b ↦ b + y` of continuous paths (`HarmonicBalls.Section6.planarBrownianMotion_map_add`).
On this common probability space we compare the paths started at `y` and at `z`, both stopped at
their exit time from an open set `U`, by the uniform distance

  `stoppedSupDist U y z b = sup_t edist ((b + z)(t ∧ τ_U(b + z)), (b + y)(t ∧ τ_U(b + y)))`.

* It satisfies the triangle inequality in the start points.
* It is a Borel function of the path `b`: a stopped continuous path is continuous, so the
  supremum over `t ≥ 0` equals the supremum over a countable dense set of times, and each time
  coordinate of a path stopped at a measurable random time is measurable.
* If `U` is a disc and `c ∈ U`, then for every sequence `u n → c`, almost surely
  `stoppedSupDist U c (u n) b → 0`: almost every Brownian path started at `c` leaves the disc at a
  finite time and exits regularly (`ae_regularExit_ball_planarBrownian`), and at such a path the
  stopped path depends continuously on uniform translations
  (`tendsto_iSup_edist_stopAtExit_add_const_of_regularExit`).

These are the hypotheses of the uniform-on-compacts convergence in measure used to move the start
point of the Brownian motion in the uniform-start invariance principle.

## Main statements

* `MatedCRT.StopAtExitCmp.planarBrownianMotion_apply_eq_translatePath`
* `MatedCRT.StopAtExitCmp.stoppedSupDist_le_add`
* `MatedCRT.StopAtExitCmp.measurable_stoppedSupDist`
* `MatedCRT.StopAtExitCmp.ae_tendsto_stoppedSupDist_ball`
-/

open Set Filter Topology Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StopAtExitCmp

/-- Translation of continuous planar paths by `y`: `b ↦ (s ↦ b s + y)`. -/
noncomputable def translatePath (y : ℂ) : ContinuousPath ℂ ≃ₜ ContinuousPath ℂ :=
  (Homeomorph.refl ℝ≥0).arrowCongr (Homeomorph.addRight y)

@[simp]
theorem translatePath_apply (y : ℂ) (b : ContinuousPath ℂ) (s : ℝ≥0) :
    translatePath y b s = b s + y :=
  rfl

/-- Planar Brownian motion started at `y` is the translate by `y` of planar Brownian motion started
at `0`. -/
theorem map_translatePath_planarBrownianMotion (y : ℂ) :
    (planarBrownianMotion 0).map (translatePath y) = planarBrownianMotion y :=
  HarmonicBalls.Section6.planarBrownianMotion_map_add y

/-- The translation identity for the (outer) measure of an arbitrary set of paths. -/
theorem planarBrownianMotion_apply_eq_translatePath (y : ℂ) (S : Set (ContinuousPath ℂ)) :
    planarBrownianMotion y S = planarBrownianMotion 0 (translatePath y ⁻¹' S) := by
  rw [← map_translatePath_planarBrownianMotion y]
  exact (translatePath y).toMeasurableEquiv.map_apply S

/-- The uniform distance between the translates by `z` and by `y` of the path `b`, each stopped at
its exit time from `U`. -/
noncomputable def stoppedSupDist (U : Set ℂ) (y z : ℂ) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ⨆ t, edist (stopAtExit U ⇑(translatePath z b) t) (stopAtExit U ⇑(translatePath y b) t)

/-- Triangle inequality of `stoppedSupDist` in the start points. -/
theorem stoppedSupDist_le_add (U : Set ℂ) (c y z : ℂ) (b : ContinuousPath ℂ) :
    stoppedSupDist U y z b ≤ stoppedSupDist U c y b + stoppedSupDist U c z b := by
  unfold stoppedSupDist
  refine iSup_le fun t => (edist_triangle_right _ _
    (stopAtExit U ⇑(translatePath c b) t)).trans ?_
  rw [add_comm]
  exact add_le_add (le_iSup_of_le t le_rfl) (le_iSup_of_le t le_rfl)

/-- For continuous paths the supremum of the pointwise distance over all times equals the
supremum over a dense set of times. -/
theorem iSup_edist_eq_iSup_dense {s : Set ℝ≥0} (hs : Dense s) {g h : ℝ≥0 → ℂ}
    (hg : Continuous g) (hh : Continuous h) :
    ⨆ t, edist (g t) (h t) = ⨆ t : s, edist (g t) (h t) := by
  refine le_antisymm (iSup_le fun t => ?_)
    (iSup_le fun t => le_iSup (fun t => edist (g t) (h t)) (t : ℝ≥0))
  have hcl : IsClosed {t | edist (g t) (h t) ≤ ⨆ t : s, edist (g t) (h t)} :=
    isClosed_le (hg.edist hh) continuous_const
  have hsub : s ⊆ {t | edist (g t) (h t) ≤ ⨆ t : s, edist (g t) (h t)} := fun t ht =>
    le_iSup (fun t : s => edist (g t) (h t)) ⟨t, ht⟩
  exact (hcl.closure_subset_iff.2 hsub) (hs t)

/-- A fixed time coordinate of the path stopped at its exit time from an open set is a Borel
function of the path. -/
theorem measurable_stopAtExit_apply {U : Set ℂ} (hU : IsOpen U) (t : ℝ≥0) :
    Measurable fun ω : ContinuousPath ℂ => stopAtExit U ⇑ω t := by
  have hτ : Measurable fun ω : ContinuousPath ℂ => pathExitTime U ⇑ω :=
    MarkovProcess.ContinuousPath.measurable_exitTime U hU
  have hT : Measurable fun ω : ContinuousPath ℂ =>
      if pathExitTime U ⇑ω = ⊤ then t else min t (pathExitTime U ⇑ω).toNNReal :=
    Measurable.ite (hτ (measurableSet_singleton ⊤)) measurable_const
      (measurable_const.min (ENNReal.measurable_toNNReal.comp hτ))
  exact MarkovProcess.ContinuousPath.measurable_eval_of_measurable _ hT

/-- `stoppedSupDist U y z` is a Borel function of the path for every open set `U`. -/
theorem measurable_stoppedSupDist {U : Set ℂ} (hU : IsOpen U) (y z : ℂ) :
    Measurable (stoppedSupDist U y z) := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable s := hsc.to_subtype
  have heq : stoppedSupDist U y z = fun b => ⨆ t : s,
      edist (stopAtExit U ⇑(translatePath z b) t) (stopAtExit U ⇑(translatePath y b) t) := by
    funext b
    exact iSup_edist_eq_iSup_dense hsd (continuous_stopAtExit (translatePath z b).continuous)
      (continuous_stopAtExit (translatePath y b).continuous)
  rw [heq]
  exact Measurable.iSup fun t =>
    ((measurable_stopAtExit_apply hU t).comp (translatePath z).measurable).edist
      ((measurable_stopAtExit_apply hU t).comp (translatePath y).measurable)

/-- **Almost sure continuity in the start point.** Let `c` lie in the disc `ball x r`. For every
sequence of start points `u n → c`, almost surely under planar Brownian motion started at `0`, the
uniform distance between the translates by `u n` and by `c`, each stopped at its exit time from
the disc, tends to `0`. -/
theorem ae_tendsto_stoppedSupDist_ball {x c : ℂ} {r : ℝ} (hc : c ∈ ball x r) {u : ℕ → ℂ}
    (hu : Tendsto u atTop (𝓝 c)) :
    ∀ᵐ b ∂planarBrownianMotion 0,
      Tendsto (fun n => stoppedSupDist (ball x r) c (u n) b) atTop (𝓝 0) := by
  have h := ae_regularExit_ball_planarBrownian (z := x) (r := r) hc
  rw [← map_translatePath_planarBrownianMotion c] at h
  have h0 := ae_of_ae_map (translatePath c).measurable.aemeasurable h
  filter_upwards [h0] with b hb
  have hv : Tendsto (fun n => u n - c) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.2 hu
  have hfun : ∀ n, ⇑(translatePath (u n) b) = fun s => ⇑(translatePath c b) s + (u n - c) := by
    intro n
    funext s
    simp only [translatePath_apply]
    ring
  have key := tendsto_iSup_edist_stopAtExit_add_const_of_regularExit isOpen_ball
    (translatePath c b).continuous hb hv
  refine key.congr fun n => ?_
  simp only [stoppedSupDist, hfun n]

end MatedCRT.StopAtExitCmp
