import MatedCRT.FirstPass.LPBridge.PlanarBrownianSpace
import MatedCRT.Defs.QuantumCone
import LatticeProb.Prob.UpcrossStay
import LatticeProb.Prob.BrownianRestartPath
import LatticeProb.Prob.CauchyPointPolar

/-! # The canonical real Brownian path law -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal BoundedContinuousFunction

namespace MatedCRT

/-- A continuous standard Brownian process has the canonical Brownian path law. -/
theorem map_pathMap_eq_brownianMotion_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) :
    P.map (LatticeProb.pathMap B hc) = MarkovProcess.brownianMotion 0 := by
  let X : ℝ≥0 → MarkovProcess.ContinuousPath ℝ → ℝ := fun t w => w t
  have hX : IsBrownianReal X (MarkovProcess.brownianMotion 0) := by
    simpa only [X, sub_zero] using
      (PlanarBrownianSpace.isBrownianReal_brownianMotion_sub 0)
  have hXm : ∀ t, Measurable (X t) := fun t =>
    MarkovProcess.ContinuousPath.measurable_coordinateProcess t
  have hXc : ∀ w, Continuous fun t => X t w := fun w => w.continuous
  have h := LatticeProb.map_pathMap_eq_of_isBrownianReal hB hm hc hX hXm hXc
  have hid : LatticeProb.pathMap X hXc = id := by
    funext w
    ext t
    rfl
  simpa only [hid, Measure.map_id] using h

/-- The paper's stay-above event is the pullback of the drifted path event. -/
theorem stayAboveEvent_eq_preimage (d δ : ℝ) :
    stayAboveEvent d δ = LatticeProb.driftMap d ⁻¹' LatticeProb.staySet δ := rfl

/-- The paper's weak-limit hypothesis uses the same conditioned path laws as
an arbitrary continuous standard Brownian realization. -/
theorem isBMConditionedPositive_pathMap
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) {d : ℝ}
    {ν : Measure (MarkovProcess.ContinuousPath ℝ)}
    (hν : IsBMConditionedPositive d ν) :
    IsProbabilityMeasure ν ∧ ∀ f : MarkovProcess.ContinuousPath ℝ →ᵇ ℝ,
      Tendsto (fun δ : ℝ => ∫ w, f w ∂((P.map (LatticeProb.pathMap B hc))[|LatticeProb.driftMap d ⁻¹' LatticeProb.staySet δ]))
        (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν)) := by
  rw [map_pathMap_eq_brownianMotion_zero hB hm hc]
  simpa only [IsBMConditionedPositive, ← stayAboveEvent_eq_preimage] using hν

end MatedCRT
