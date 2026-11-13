import MatedCRT.FirstPass.Derived.MatedCRTGraphBridge
import MatedCRT.FirstPass.Derived.SrwLawMeasurable
import MatedCRT.FirstPass.Derived.SrwChainBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateVertex
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasureIsProbability
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Walk

/-!
# One step of the edge-end walk and of `srwKernel`

The simple random walk of the statements is the Markov chain `srwKernel m` on `ℤ` with edge multiplicity
`m = bmEdgeCount ε L R` (Definition 1.1). In Bonanno's development the walk is the *edge-end walk* of the locally
finite multigraph `MatedCRT.graph ε ω h`: its states are `V ⊕ Dart`, a step from the vertex `x` picks one of the
`deg x` darts leaving `x` uniformly (`stepMeasure x`), and the vertex of a state is `stateVertex`.

* `stepMeasure_map_stateVertex_singleton`: for every locally finite multigraph on `ℤ`, the image of the one-step
  measure under `stateVertex` gives the vertex `y` the mass `#{darts x → y} / deg x`;
* `srwKernel_bmEdgeCount_eq`: for `ε ≥ 0` and the mated-CRT multigraph, `srwKernel (bmEdgeCount ε L R) x` is
  that image measure, for every vertex `x`.

This is the one-step identity behind the lumping of the edge-end walk onto the vertex chain.
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

section Step

variable {E : Type*} (G : MatedCRTHarmonic.LFMultigraph ℤ E)

/-- The vertex image of the one-step measure of the edge-end walk: the probability of moving from `x` to `y` is the
number of darts from `x` to `y` over the degree of `x`. -/
theorem stepMeasure_map_stateVertex_singleton (x y : ℤ) :
    ((G.stepMeasure x).map G.stateVertex) {y} =
      (G.deg x : ℝ≥0∞)⁻¹ * (((G.outDarts x).filter fun d => G.dtgt d = y).card : ℝ≥0∞) := by
  classical
  rw [Measure.map_apply measurable_from_top (measurableSet_singleton y), MatedCRTHarmonic.LFMultigraph.stepMeasure,
    Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  have hd : ∀ d ∈ G.outDarts x,
      (Measure.dirac (show G.State from Sum.inr d)) (G.stateVertex ⁻¹' {y}) = if G.dtgt d = y then 1 else 0 := by
    intro d _
    rw [Measure.dirac_apply' _ MeasurableSpace.measurableSet_top, Set.indicator_apply]
    exact if_congr Iff.rfl rfl rfl
  rw [Finset.sum_congr rfl hd, Finset.sum_boole]

end Step

section Mated

variable {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2} (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω)
include h

/-- The total edge multiplicity at `x`, in `ℝ≥0∞`, is the degree of `x` in Bonanno's multigraph. -/
theorem tsum_bmEdgeCount_eq_deg (hε : 0 ≤ ε) (x : ℤ) :
    (∑' y, (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y : ℝ≥0∞)) =
      ((MatedCRTHarmonic.MatedCRT.graph ε ω h).deg x : ℝ≥0∞) := by
  classical
  set G := MatedCRTHarmonic.MatedCRT.graph ε ω h with hG
  have hsupp : (Function.support fun y => bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) x y) ⊆
      ↑((G.outDarts x).image G.dtgt) := fun y hy => bmEdgeCount_ne_zero_mem_image h hε hy
  rw [deg_graph_eq h hε x, mdeg, finsum_eq_sum_of_support_subset _ hsupp, Nat.cast_sum]
  refine tsum_eq_sum fun y hy => ?_
  by_contra hne
  exact hy (by simpa using hsupp (Nat.cast_ne_zero.mp hne))

/-- **One step of simple random walk on the mated-CRT map.** For `ε ≥ 0`, `srwKernel (bmEdgeCount ε L R) x` is the
image, under `stateVertex`, of the one-step measure of the edge-end walk of Bonanno's multigraph. -/
theorem srwKernel_bmEdgeCount_eq (hε : 0 ≤ ε) (x : ℤ) :
    srwKernel (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) x =
      ((MatedCRTHarmonic.MatedCRT.graph ε ω h).stepMeasure x).map
        (MatedCRTHarmonic.MatedCRT.graph ε ω h).stateVertex := by
  classical
  refine Measure.ext_of_singleton fun y => ?_
  have hdeg0 : (MatedCRTHarmonic.MatedCRT.graph ε ω h).deg x ≠ 0 :=
    MatedCRTHarmonic.Harmonic.deg_ne_zero (MatedCRTHarmonic.MatedCRT.graph ε ω h) x
  have hs := tsum_bmEdgeCount_eq_deg h hε x
  have hc : (((MatedCRTHarmonic.MatedCRT.graph ε ω h).deg x : ℝ≥0∞) ≠ 0 ∧
      ((MatedCRTHarmonic.MatedCRT.graph ε ω h).deg x : ℝ≥0∞) ≠ ⊤) :=
    ⟨by exact_mod_cast hdeg0, ENNReal.natCast_ne_top _⟩
  rw [srwKernel_apply, srwStep_singleton, stepMeasure_map_stateVertex_singleton, card_filter_outDarts_graph h hε,
    hs]
  simp only [ne_eq, hc.1, hc.2, not_false_eq_true, and_self, ↓reduceIte]

end Mated

end MatedCRT
