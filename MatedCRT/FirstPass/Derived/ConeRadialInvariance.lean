import MatedCRT.FirstPass.Derived.ConeRadialRescaleDet
import MatedCRT.FirstPass.Derived.ConeConditionedNonneg
import MatedCRT.FirstPass.Derived.ConeReferenceLaw
import MatedCRT.FirstPass.Derived.ConeRadialLevelLimits
import MatedCRT.FirstPass.LPBridge.ExitRestartCanonical
import LatticeProb.Prob.UpcrossShiftGlueInvariance
import LatticeProb.Prob.UpcrossPieceFdd

/-!
# Invariance of the radial law of the quantum cone under rescaling to a lower level

The radial pair of a `γ`-quantum cone has the law `quantumConeRadialLaw γ ν`, the image under
`coneE γ (y, z) = (y t + Q t, z s - Q s)` of the product `driftLaw(-μ) ⊗ ν'`, where `μ = Q - γ`,
`ν' = ν.map (driftMap μ)`. By the deterministic computation `radialRescale_coneE_of_neg` the rescaling to a level
`γ⁻¹ log b = -a < 0` acts on `(y, z)` by `(restartAt τ y, glueC a y z)`, which preserves `driftLaw(-μ) ⊗ ν'`
(Williams gluing, `LatticeProb.map_shiftGlue_prod_eq`).

* `map_radialRescale_coneE_prod_of_neg`: the invariance, for any `ν'` satisfying the hypotheses of the gluing.
* `map_radialRescale_quantumConeRadialLaw_of_neg`: for the law of the cone.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

lemma measurable_coneE (γ : ℝ) :
    Measurable fun q : ContinuousPath ℝ × ContinuousPath ℝ => coneE γ q.1 q.2 := by
  refine Measurable.prodMk (Measurable.of_eval fun t => ?_) (Measurable.of_eval fun s => ?_)
  · exact ((ContinuousPath.measurable_coordinateProcess t).comp measurable_fst).add_const _
  · exact ((ContinuousPath.measurable_coordinateProcess s).comp measurable_snd).sub_const _

/-- **Invariance of `driftLaw(-μ) ⊗ ν'` under the rescaling to a level `-a < 0`.** -/
theorem map_radialRescale_coneE_prod_of_neg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : ProbabilityTheory.IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {μ : ℝ} (hμ : 0 < μ)
    {γ b a : ℝ} (ha : 0 < a) (hab : γ⁻¹ * Real.log b = -a)
    {ν' : Measure (ContinuousPath ℝ)} [IsProbabilityMeasure ν'] (hν0 : ∀ᵐ z ∂ν', z 0 = 0)
    (hz : ∀ᵐ z ∂ν', ∀ s, 0 ≤ z s)
    (hpiece : ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))),
      (LatticeProb.driftLaw P B hcont μ).map
          (fun w : C(ℝ≥0, ℝ) => LatticeProb.firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
        ν'.map (fun z : C(ℝ≥0, ℝ) =>
          (LatticeProb.stopAt (LatticeProb.hitFrom c 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ))) :
    (((LatticeProb.driftLaw P B hcont (-μ)).prod ν').map
        (fun q : ContinuousPath ℝ × ContinuousPath ℝ => coneE γ q.1 q.2)).map (radialRescale γ b) =
      ((LatticeProb.driftLaw P B hcont (-μ)).prod ν').map
        (fun q : ContinuousPath ℝ × ContinuousPath ℝ => coneE γ q.1 q.2) := by
  set G := (LatticeProb.driftLaw P B hcont (-μ)).prod ν' with hG
  have hE := measurable_coneE γ
  have hΘ := LatticeProb.measurable_shiftGlue a
  rw [Measure.map_map (measurable_radialRescale γ b) hE]
  have hae : (radialRescale γ b ∘ fun q : ContinuousPath ℝ × ContinuousPath ℝ => coneE γ q.1 q.2)
      =ᵐ[G] ((fun q : ContinuousPath ℝ × ContinuousPath ℝ => coneE γ q.1 q.2) ∘
        fun q : ContinuousPath ℝ × ContinuousPath ℝ =>
          (LatticeProb.restartAt (LatticeProb.glueTime a (q.1 : ℝ≥0 → ℝ)) q.1,
            LatticeProb.glueC a q.1 q.2)) := by
    have h1 : ∀ᵐ q ∂G, q.1 0 = 0 ∧ LatticeProb.hitFrom (-a) 0 (q.1 : ℝ≥0 → ℝ) ≠ ⊤ :=
      Measure.quasiMeasurePreserving_fst.ae
        (LatticeProb.ae_hitFrom_neg_ne_top_driftLaw_neg hB hm hcont hμ ha.le)
    have h2 : ∀ᵐ q ∂G, q.2 0 = 0 ∧ ∀ s, 0 ≤ q.2 s :=
      Measure.quasiMeasurePreserving_snd.ae (hν0.and hz)
    filter_upwards [h1, h2] with q hq1 hq2
    exact radialRescale_coneE_of_neg ha hab hq1.1 hq2.1 hq2.2 hq1.2
  rw [Measure.map_congr hae, ← Measure.map_map hE hΘ,
    LatticeProb.map_shiftGlue_prod_eq hB hm hcont hμ ha hν0 hpiece]

/-- The radial law of the cone as the image of `driftLaw(-μ) ⊗ ν'` under `coneE`. -/
lemma quantumConeRadialLaw_eq_map_coneE (γ : ℝ) (ν : Measure (ContinuousPath ℝ))
    [IsProbabilityMeasure ν] :
    quantumConeRadialLaw γ ν =
      (((brownianMotion 0).map (LatticeProb.driftMap (-(lqgQ γ - γ)))).prod
        (ν.map (LatticeProb.driftMap (lqgQ γ - γ)))).map
        (fun q : ContinuousPath ℝ × ContinuousPath ℝ => coneE γ q.1 q.2) := by
  have h1 : Measurable (fun (y : ContinuousPath ℝ) (t : ℝ≥0) => y t + lqgQ γ * (t : ℝ)) :=
    Measurable.of_eval fun t => (ContinuousPath.measurable_coordinateProcess t).add_const _
  have h2 : Measurable (fun (z : ContinuousPath ℝ) (s : ℝ≥0) => z s - lqgQ γ * (s : ℝ)) :=
    Measurable.of_eval fun s => (ContinuousPath.measurable_coordinateProcess s).sub_const _
  have e1 : (brownianMotion 0).map (fun (w : ContinuousPath ℝ) (t : ℝ≥0) => w t + γ * (t : ℝ)) =
      ((brownianMotion 0).map (LatticeProb.driftMap (-(lqgQ γ - γ)))).map
        (fun (y : ContinuousPath ℝ) (t : ℝ≥0) => y t + lqgQ γ * (t : ℝ)) := by
    rw [Measure.map_map h1 (LatticeProb.measurable_driftMap _)]
    congr 1
    funext w t
    simp only [Function.comp, LatticeProb.driftMap_apply]
    ring
  have e2 : ν.map (fun (w : ContinuousPath ℝ) (s : ℝ≥0) => w s - γ * (s : ℝ)) =
      (ν.map (LatticeProb.driftMap (lqgQ γ - γ))).map
        (fun (z : ContinuousPath ℝ) (s : ℝ≥0) => z s - lqgQ γ * (s : ℝ)) := by
    rw [Measure.map_map h2 (LatticeProb.measurable_driftMap _)]
    congr 1
    funext w t
    simp only [Function.comp, LatticeProb.driftMap_apply]
    ring
  unfold quantumConeRadialLaw
  rw [e1, e2, Measure.map_prod_map _ _ h1 h2]
  rfl

/-- **The radial law of a `γ`-quantum cone is invariant under the rescaling `radialRescale γ b` to a level
`γ⁻¹ log b < 0`.** -/
theorem map_radialRescale_quantumConeRadialLaw_of_neg {γ b a : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (ha : 0 < a) (hab : γ⁻¹ * Real.log b = -a) {ν : Measure (ContinuousPath ℝ)}
    (hν : IsBMConditionedPositive (lqgQ γ - γ) ν) :
    (quantumConeRadialLaw γ ν).map (radialRescale γ b) = quantumConeRadialLaw γ ν := by
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
  have : IsProbabilityMeasure (ν.map (LatticeProb.driftMap (lqgQ γ - γ))) :=
    (Measure.isProbabilityMeasure_map_iff (μ := ν)
      (LatticeProb.measurable_driftMap (lqgQ γ - γ)).aemeasurable).2 inferInstance
  rw [quantumConeRadialLaw_eq_map_coneE γ ν, ← hdl (-(lqgQ γ - γ))]
  refine map_radialRescale_coneE_prod_of_neg hB hm hcont hμ ha hab ?_ ?_ ?_
  · have hmeas : MeasurableSet {z : ContinuousPath ℝ | z 0 = 0} :=
      measurableSet_eq_fun (ContinuousPath.measurable_coordinateProcess 0) measurable_const
    refine (ae_map_iff (LatticeProb.measurable_driftMap _).aemeasurable hmeas).2 ?_
    filter_upwards [isBMConditionedPositive_ae_eval_zero hν] with w hw
    simp [hw]
  · have hmeas : MeasurableSet {z : ContinuousPath ℝ | ∀ s : ℝ≥0, 0 ≤ z s} := by
      have : {z : ContinuousPath ℝ | ∀ s : ℝ≥0, 0 ≤ z s} = ⋂ s : ℝ≥0, {z | 0 ≤ z s} := by
        ext z
        simp
      rw [this]
      exact (isClosed_iInter fun s => isClosed_le continuous_const
        (continuous_eval_const s)).measurableSet
    refine (ae_map_iff (LatticeProb.measurable_driftMap _).aemeasurable hmeas).2 ?_
    filter_upwards [ConeConditionedNonneg.ae_forall_nonneg_of_isBMConditionedPositive hν] with w hw s
    simpa using hw s
  · refine LatticeProb.ae_map_piece_eq hB hm hcont hμ (ν := ν) fun f => ?_
    have hset : ∀ δ : ℝ, LatticeProb.driftMap (lqgQ γ - γ) ⁻¹' LatticeProb.staySet δ =
        stayAboveEvent (lqgQ γ - γ) δ := by
      intro δ
      ext w
      simp [LatticeProb.staySet, stayAboveEvent]
    simp only [hid, Measure.map_id, hset]
    exact hν.2 f

end MatedCRT.FirstPass.Derived
