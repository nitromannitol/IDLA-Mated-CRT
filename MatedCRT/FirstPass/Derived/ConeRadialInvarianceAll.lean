import MatedCRT.FirstPass.Derived.ConeConditionedPositive
import MatedCRT.FirstPass.Derived.ConeRadialRescaleDet0
import MatedCRT.FirstPass.Derived.ConeRadialRescaleInverse

/-!
# Invariance of the radial law of the quantum cone under every rescaling

For `γ⁻¹ log b < 0` the radial law of the cone is invariant under `radialRescale γ b`
(`map_radialRescale_quantumConeRadialLaw_of_neg`).  For `γ⁻¹ log b = 0` the rescaling is the identity
on the cone pairs `coneE γ (y, z)` with `z > 0` on `(0, ∞)`, and for `γ⁻¹ log b = a > 0` it is the
inverse of the rescaling to the level `-a`, so it also preserves the law.

* `ae_cone_pair`: the almost sure properties of the pair `(y, z)` used by the deterministic computations.
* `map_radialRescale_quantumConeRadialLaw`: the invariance for every real `b`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

/-- Almost sure properties of the pair `(y, z)` under `driftLaw(-μ) ⊗ ν'`: `y` starts at `0` and hits
`-a`; `z` starts at `0`, is nonnegative and is strictly positive on `(0, ∞)`. -/
lemma ae_cone_pair {γ a : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (ha : 0 ≤ a)
    {ν : Measure (ContinuousPath ℝ)} (hν : IsBMConditionedPositive (lqgQ γ - γ) ν) :
    ∀ᵐ q ∂(((brownianMotion 0).map (LatticeProb.driftMap (-(lqgQ γ - γ)))).prod
        (ν.map (LatticeProb.driftMap (lqgQ γ - γ)))),
      (q.1 0 = 0 ∧ LatticeProb.hitFrom (-a) 0 (q.1 : ℝ≥0 → ℝ) ≠ ⊤) ∧
        (q.2 0 = 0 ∧ (∀ s, 0 ≤ q.2 s) ∧ ∀ s : ℝ≥0, 0 < s → 0 < q.2 s) := by
  have hμ := lqgQ_sub_pos' hγ0 hγ2
  have : IsProbabilityMeasure ν := hν.1
  have hpre : ProbabilityTheory.IsPreBrownianReal (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t)
      (brownianMotion 0) := by
    simpa using MatedCRT.ExitRestart.brownianMotion_isPreBrownianReal 0
  have hB : ProbabilityTheory.IsBrownianReal (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t)
      (brownianMotion 0) := ⟨hpre, Filter.Eventually.of_forall fun ω => ω.continuous⟩
  have hm : ∀ t : ℝ≥0, Measurable fun ω : ContinuousPath ℝ => ω t := fun t =>
    ContinuousPath.measurable_coordinateProcess t
  have hcont : ∀ ω : ContinuousPath ℝ, Continuous fun s : ℝ≥0 => ω s := fun ω => ω.continuous
  have hid : LatticeProb.pathMap (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t) hcont = id :=
    funext fun ω => ContinuousMap.ext fun t => rfl
  have hdl : ∀ m : ℝ, LatticeProb.driftLaw (brownianMotion 0)
      (fun (t : ℝ≥0) (ω : ContinuousPath ℝ) => ω t) hcont m =
        (brownianMotion 0).map (LatticeProb.driftMap m) := by
    intro m
    simp only [LatticeProb.driftLaw, hid, Measure.map_id]
  have h1 := LatticeProb.ae_hitFrom_neg_ne_top_driftLaw_neg hB hm hcont hμ ha
  rw [hdl] at h1
  have hmeas0 : MeasurableSet {z : ContinuousPath ℝ | z 0 = 0} :=
    measurableSet_eq_fun (ContinuousPath.measurable_coordinateProcess 0) measurable_const
  have hmeasNN : MeasurableSet {z : ContinuousPath ℝ | ∀ s : ℝ≥0, 0 ≤ z s} := by
    have : {z : ContinuousPath ℝ | ∀ s : ℝ≥0, 0 ≤ z s} = ⋂ s : ℝ≥0, {z | 0 ≤ z s} := by
      ext z
      simp
    rw [this]
    exact (isClosed_iInter fun s => isClosed_le continuous_const
      (continuous_eval_const s)).measurableSet
  have h2 : ∀ᵐ z ∂(ν.map (LatticeProb.driftMap (lqgQ γ - γ))), z 0 = 0 := by
    refine (ae_map_iff (LatticeProb.measurable_driftMap _).aemeasurable hmeas0).2 ?_
    filter_upwards [isBMConditionedPositive_ae_eval_zero hν] with w hw
    simp [hw]
  have h3 : ∀ᵐ z ∂(ν.map (LatticeProb.driftMap (lqgQ γ - γ))), ∀ s : ℝ≥0, 0 ≤ z s := by
    refine (ae_map_iff (LatticeProb.measurable_driftMap _).aemeasurable hmeasNN).2 ?_
    filter_upwards [ConeConditionedNonneg.ae_forall_nonneg_of_isBMConditionedPositive hν] with w hw s
    simpa using hw s
  have h4 := ae_forall_pos_driftMap_of_isBMConditionedPositive hγ0 hγ2 hν
  have : IsProbabilityMeasure (ν.map (LatticeProb.driftMap (lqgQ γ - γ))) :=
    (Measure.isProbabilityMeasure_map_iff (μ := ν)
      (LatticeProb.measurable_driftMap (lqgQ γ - γ)).aemeasurable).2 inferInstance
  have h5 : ∀ᵐ q ∂(((brownianMotion 0).map (LatticeProb.driftMap (-(lqgQ γ - γ)))).prod
        (ν.map (LatticeProb.driftMap (lqgQ γ - γ)))), q.1 0 = 0 ∧
        LatticeProb.hitFrom (-a) 0 (q.1 : ℝ≥0 → ℝ) ≠ ⊤ :=
    Measure.quasiMeasurePreserving_fst.ae h1
  have h6 : ∀ᵐ q ∂(((brownianMotion 0).map (LatticeProb.driftMap (-(lqgQ γ - γ)))).prod
        (ν.map (LatticeProb.driftMap (lqgQ γ - γ)))), q.2 0 = 0 ∧ (∀ s, 0 ≤ q.2 s) ∧
        ∀ s : ℝ≥0, 0 < s → 0 < q.2 s :=
    Measure.quasiMeasurePreserving_snd.ae (h2.and (h3.and h4))
  exact h5.and h6

/-- **The radial law of a `γ`-quantum cone is invariant under every rescaling `radialRescale γ b`.** -/
theorem map_radialRescale_quantumConeRadialLaw {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {ν : Measure (ContinuousPath ℝ)} (hν : IsBMConditionedPositive (lqgQ γ - γ) ν) (b : ℝ) :
    (quantumConeRadialLaw γ ν).map (radialRescale γ b) = quantumConeRadialLaw γ ν := by
  have : IsProbabilityMeasure ν := hν.1
  have hLw := quantumConeRadialLaw_eq_map_coneE γ ν
  have hE := measurable_coneE γ
  rcases lt_trichotomy (γ⁻¹ * Real.log b) 0 with h | h | h
  · exact map_radialRescale_quantumConeRadialLaw_of_neg hγ0 hγ2 (neg_pos.2 h)
      (neg_neg (γ⁻¹ * Real.log b)).symm hν
  · conv_lhs => rw [hLw]
    rw [Measure.map_map (measurable_radialRescale γ b) hE]
    refine (Measure.map_congr ?_).trans hLw.symm
    filter_upwards [ae_cone_pair hγ0 hγ2 le_rfl hν] with q hq
    exact radialRescale_coneE_of_zero h hq.1.1 hq.2.1 hq.2.2.2
  · set a := γ⁻¹ * Real.log b with ha
    have hb' : γ⁻¹ * Real.log (Real.exp (-(γ * a))) = -a := by
      rw [Real.log_exp]
      field_simp
    have hneg := map_radialRescale_quantumConeRadialLaw_of_neg hγ0 hγ2 h hb' hν
    have h3 : (quantumConeRadialLaw γ ν).map
        (radialRescale γ b ∘ radialRescale γ (Real.exp (-(γ * a)))) =
        quantumConeRadialLaw γ ν := by
      conv_lhs => rw [hLw]
      rw [Measure.map_map ((measurable_radialRescale γ b).comp
        (measurable_radialRescale γ (Real.exp (-(γ * a))))) hE]
      refine (Measure.map_congr ?_).trans hLw.symm
      filter_upwards [ae_cone_pair hγ0 hγ2 h.le hν] with q hq
      simp only [Function.comp_apply]
      rw [radialRescale_coneE_of_neg h hb' hq.1.1 hq.2.1 hq.2.2.1 hq.1.2]
      exact radialRescale_coneE_inverse h rfl hq.1.1 hq.2.1 hq.2.2.2 hq.1.2
    calc (quantumConeRadialLaw γ ν).map (radialRescale γ b)
        = ((quantumConeRadialLaw γ ν).map (radialRescale γ (Real.exp (-(γ * a))))).map
            (radialRescale γ b) := by rw [hneg]
      _ = _ := Measure.map_map (measurable_radialRescale γ b)
            (measurable_radialRescale γ (Real.exp (-(γ * a))))
      _ = quantumConeRadialLaw γ ν := h3

end MatedCRT.FirstPass.Derived
