import MatedCRT.FirstPass.Derived.LQGMeasureChartInvariance
import MatedCRT.FirstPass.Derived.LQGMeasureChartSheffieldWang
import MatedCRT.FirstPass.Derived.LQGMeasureChartOpenPatch
import MatedCRT.FirstPass.Derived.LQGMeasureChartCone
import MatedCRT.FirstPass.Derived.LQGMeasureChartPole
import MatedCRT.FirstPass.Derived.LQGMeasureChartBorel
import MatedCRT.FirstPass.Derived.ConeMeasureSingularWeight
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P0
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate

/-!
# The coordinate change of the LQG measure through the cone point

The field `h` of a valid environment is, almost surely, a normalized whole-plane GFF `G` minus `γ log |·|` plus a
continuous function (`MatedCRTEnv.IsValid.exists_hC_eq_normalizedWPGFF_sub_log_add`). This file transports the
coordinate change of the LQG measure on open sets (`OpenChartProp`) from the whole-plane GFF to `h`, including the
open sets containing the cone point `0`, following the rooting argument of Duplantier–Sheffield, *Liouville quantum
gravity and KPZ* (arXiv:0808.1560v2), §3.3 and the paragraph after Proposition 3.4:

* the property `OpenChartPropNoAtom γ f g`: `g` has the coordinate change on open sets with a measure without atoms;
  it is invariant under adding constants and continuous functions and under translations
  (`OpenChartProp.addConst`, `OpenChartProp.addFun`, `OpenChartProp.affineComp`);
* rooting (`ae_measure_add_covDist_mem`): if the property holds for the normalized whole-plane GFF, it holds for the
  field shifted by `γ` times its covariance with the value at a point `x` sampled from Lebesgue measure on the unit
  disc; moving the root to `0` (`measure_affineComp_add_covDist_mem`, translation invariance of the GFF modulo
  constants) and removing the continuous part of the covariance gives the property for `G − γ log |·|`
  (`ae_openChartPropNoAtom_sub_log`);
* adding the continuous remainder gives the property for `h`, and the measure is the LQG measure of the environment:
  away from `0` by the coordinate change on discs avoiding the cone point (`MatedCRTEnv.IsValid.ae_chartProp`, with
  `ψ = id`) and uniqueness of vague limits, at `0` because neither measure has an atom there
  (`ae_coneMeasure_singleton_zero`).

The input for the whole-plane GFF itself (the coordinate change on open sets with an atomless measure, almost surely)
is the hypothesis `hGFF` of `MatedCRTEnv.IsValid.ae_openChartProp_of_wholePlane` (any mollifier `f`) and of
`MatedCRTEnv.IsValid.ae_openChartProp` (the mollifier `stdMollifier`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT

namespace LQGMeasureChart

/-- **The coordinate change on open sets with an atomless measure**: `g` has the property `OpenChartProp γ f g μ`
for some measure `μ` without atoms. -/
def OpenChartPropNoAtom (γ : ℝ) (f : ℂ → ℝ) (g : LQGMetric.DistC) : Prop :=
  ∃ μ : Measure ℂ, OpenChartProp γ f g μ ∧ ∀ x : ℂ, μ {x} = 0

namespace ConePoint

open Invariance

variable {γ : ℝ} {f : ℂ → ℝ}

/-! ### Invariances of the property -/

theorem noAtom_addFun (hf : IsMollifier f) {g : LQGMetric.DistC} (hg : OpenChartPropNoAtom γ f g)
    (v : C(ℂ, ℝ)) : OpenChartPropNoAtom γ f (LQGMetric.addFun g v) := by
  obtain ⟨μ, hμ, h0⟩ := hg
  exact ⟨_, hμ.addFun hf v, fun x => withDensity_absolutelyContinuous μ _ (h0 x)⟩

theorem noAtom_addConst (hf : IsMollifier f) {g : LQGMetric.DistC} (hg : OpenChartPropNoAtom γ f g) (c : ℝ) :
    OpenChartPropNoAtom γ f (LQGMetric.addConst g c) := by
  obtain ⟨μ, hμ, h0⟩ := hg
  exact ⟨_, hμ.addConst hf c, fun x => by rw [Measure.smul_apply, h0 x, smul_zero]⟩

theorem noAtom_affineComp (hf : IsMollifier f) {g : LQGMetric.DistC} (hg : OpenChartPropNoAtom γ f g) (z : ℂ) :
    OpenChartPropNoAtom γ f (LQGMetric.affineComp 1 z g) := by
  obtain ⟨μ, hμ, h0⟩ := hg
  refine ⟨_, hμ.affineComp hf z, fun x => ?_⟩
  have e : (fun y : ℂ => y - z) ⁻¹' {x} = {x + z} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      rw [← h]
      ring
    · intro h
      rw [h]
      ring
  rw [(measurableEmbedding_sub z).map_apply, e, h0]

/-! ### Distribution identities -/

theorem addConst_addConst (g : LQGMetric.DistC) (a b : ℝ) :
    LQGMetric.addConst (LQGMetric.addConst g a) b = LQGMetric.addConst g (a + b) := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [LQGMetric.GFFInv.addConst_apply, LQGMetric.GFFInv.addConst_apply, LQGMetric.GFFInv.addConst_apply]
  ring

theorem addConst_zero (g : LQGMetric.DistC) : LQGMetric.addConst g 0 = g := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [LQGMetric.GFFInv.addConst_apply, mul_zero, add_zero]

theorem affineComp_one_zero (g : LQGMetric.DistC) : LQGMetric.affineComp 1 0 g = g := by
  refine DFunLike.ext _ _ fun φ => ?_
  have e : LQGMetric.testAffinePull 1 0 φ = φ := by
    ext y
    rw [LQGMetric.testAffinePull_apply 1 0 one_ne_zero, sub_zero, Complex.ofReal_one, div_one]
  rw [LQGMetric.GFFInv.affineComp_apply, e, one_pow, inv_one, one_mul]

theorem ofCont_smul (c : ℝ) (v : C(ℂ, ℝ)) : LQGMetric.ofCont (c • v) = c • LQGMetric.ofCont v := by
  refine DFunLike.ext _ _ fun φ => ?_
  show LQGMetric.ofCont (c • v) φ = c * LQGMetric.ofCont v φ
  rw [LQGMetric.ofCont_apply, LQGMetric.ofCont_apply, ← integral_const_mul]
  congr 1
  funext y
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem addFun_addFun_neg (g : LQGMetric.DistC) (v : C(ℂ, ℝ)) :
    LQGMetric.addFun (LQGMetric.addFun g v) (-v) = g := by
  refine DFunLike.ext _ _ fun φ => ?_
  show g φ + LQGMetric.ofCont v φ + LQGMetric.ofCont (-v) φ = g φ
  rw [LQGMetric.ofCont_apply, LQGMetric.ofCont_apply]
  have e : ∫ y, φ y * (-v) y = -∫ y, φ y * v y := by
    rw [← integral_neg]
    congr 1
    funext y
    simp only [ContinuousMap.neg_apply]
    ring
  rw [e]
  ring

/-- The continuous part `w ↦ log⁺|w + x| + log⁺|x|` of the covariance kernel seen from `x`. -/
def covRemainder (x : ℂ) : C(ℂ, ℝ) :=
  ⟨fun w => LatticeProb.Gauss.wholePlaneNormalization (w + x) + LatticeProb.Gauss.wholePlaneNormalization x,
    continuous_wholePlaneCov_add_self_remainder x⟩

/-- For `|x| < 1`, the covariance kernel seen from `x` is `−log |·|` plus the continuous remainder, as
distributions. -/
theorem distOfFun_wholePlaneCov_add_self {x : ℂ} (hx : ‖x‖ < 1) :
    distOfFun (fun w => LatticeProb.Gauss.wholePlaneCov (w + x) x) =
      (-1 : ℝ) • MatedCRTHarmonic.MatedCRT.ofFunC (fun z => Real.log ‖z‖) + LQGMetric.ofCont (covRemainder x) := by
  refine ofFunC_eq_neg_smul_log_add 1 (covRemainder x) fun z => ?_
  show LatticeProb.Gauss.wholePlaneCov (z + x) x = -1 * Real.log ‖z‖ +
    (LatticeProb.Gauss.wholePlaneNormalization (z + x) + LatticeProb.Gauss.wholePlaneNormalization x)
  by_cases hz : z = 0
  · subst hz
    have hN : LatticeProb.Gauss.wholePlaneNormalization x = 0 := by
      rw [LatticeProb.Gauss.wholePlaneNormalization, max_eq_right hx.le, Real.log_one]
    rw [zero_add, hN, LatticeProb.Gauss.wholePlaneCov, sub_self, norm_zero, div_zero, Real.log_zero]
    ring
  · rw [wholePlaneCov_add_self_eq hz]
    ring

theorem add_smul_distOfFun_eq {x : ℂ} (hx : ‖x‖ < 1) (h : LQGMetric.DistC) :
    h + γ • distOfFun (fun w => LatticeProb.Gauss.wholePlaneCov (w + x) x) =
      LQGMetric.addFun (h - γ • MatedCRTHarmonic.MatedCRT.ofFunC (fun z => Real.log ‖z‖)) (γ • covRemainder x) := by
  rw [distOfFun_wholePlaneCov_add_self hx]
  show _ = (h - γ • MatedCRTHarmonic.MatedCRT.ofFunC (fun z => Real.log ‖z‖)) +
    LQGMetric.ofCont (γ • covRemainder x)
  rw [ofCont_smul]
  module

/-! ### Rooting -/

/-- The field normalized by its unit circle average, `g ↦ g - g_1(0)`. -/
def unitNormalize (g : LQGMetric.DistC) : LQGMetric.DistC :=
  LQGMetric.addConst g (-LQGMetric.circleAvg g 1 0)

theorem measurable_unitNormalize : Measurable unitNormalize :=
  LQGMetric.measurable_distOn_iff.2 fun ψ => by
    simp only [unitNormalize, LQGMetric.GFFInv.addConst_apply]
    exact (LQGMetric.measurable_distOn_apply ψ).add
      (measurable_const.mul (LQGMetric.measurable_circleAvg_left 1 0).neg)

/-- The set of distributions whose mollified unit circle averages at the origin converge. -/
def unitLimitSet : Set LQGMetric.DistC :=
  {g | ∃ a, Tendsto (fun n => LQGMetric.CircleAvg.mollAvg g n 0 1) atTop (𝓝 a)}

theorem measurableSet_unitLimitSet : MeasurableSet unitLimitSet := by
  have hmoll : ∀ n : ℕ, Measurable fun g : LQGMetric.DistC => LQGMetric.CircleAvg.mollAvg g n 0 1 := fun n => by
    have e : (fun g : LQGMetric.DistC => LQGMetric.CircleAvg.mollAvg g n 0 1) =
        fun g => g (LQGMetric.CircleAvg.circBump n 0 1) :=
      funext fun g => LQGMetric.CircleAvg.mollAvg_eq g n 0 1
    rw [e]
    exact LQGMetric.measurable_distOn_apply _
  exact measurableSet_exists_tendsto hmoll

theorem addConst_mem_unitLimitSet {g : LQGMetric.DistC} (hg : g ∈ unitLimitSet) (c : ℝ) :
    LQGMetric.addConst g c ∈ unitLimitSet := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨a + c, ?_⟩
  simp_rw [LQGMetric.CircleAvg.mollAvg_addConst]
  exact ha.add_const c

theorem unitNormalize_addConst {g : LQGMetric.DistC} (hg : g ∈ unitLimitSet) (c : ℝ) :
    unitNormalize (LQGMetric.addConst g c) = unitNormalize g := by
  obtain ⟨a, ha⟩ := hg
  rw [unitNormalize, unitNormalize, LQGMetric.CircleAvg.circleAvg_addConst_of_tendsto ha c, addConst_addConst,
    show c + -(LQGMetric.circleAvg g 1 0 + c) = -LQGMetric.circleAvg g 1 0 by ring]

theorem noAtom_of_unitNormalize (hf : IsMollifier f) {g : LQGMetric.DistC}
    (hg : OpenChartPropNoAtom γ f (unitNormalize g)) : OpenChartPropNoAtom γ f g := by
  have h1 := noAtom_addConst hf hg (LQGMetric.circleAvg g 1 0)
  rwa [unitNormalize, addConst_addConst, neg_add_cancel, addConst_zero] at h1

theorem addConst_mem_unitNormalize_preimage {E : Set LQGMetric.DistC} {g : LQGMetric.DistC}
    (hg : g ∈ unitLimitSet ∩ unitNormalize ⁻¹' E) (c : ℝ) :
    LQGMetric.addConst g c ∈ unitLimitSet ∩ unitNormalize ⁻¹' E := by
  obtain ⟨hl, hE⟩ := hg
  refine ⟨addConst_mem_unitLimitSet hl c, ?_⟩
  rw [mem_preimage, unitNormalize_addConst hl c]
  exact hE

theorem ae_mem_unitLimitSet {ν : Measure LQGMetric.DistC} (hν : LQGMetric.IsNormalizedWPGFF id ν) :
    ∀ᵐ g ∂ν, g ∈ unitLimitSet :=
  LQGMetric.CircleAvg.ae_tendsto_mollAvg hν.1 0 one_pos

theorem ae_unitNormalize_eq {ν : Measure LQGMetric.DistC} (hν : LQGMetric.IsNormalizedWPGFF id ν) :
    ∀ᵐ g ∂ν, unitNormalize g = g := by
  filter_upwards [hν.2] with g h0
  rw [unitNormalize, show LQGMetric.circleAvg g 1 0 = 0 from h0, neg_zero, addConst_zero]

theorem measure_unitLimitSet_inter_eq_one {ν : Measure LQGMetric.DistC} [IsProbabilityMeasure ν]
    (hν : LQGMetric.IsNormalizedWPGFF id ν) {E : Set LQGMetric.DistC} (hEm : MeasurableSet E) (hE1 : ν E = 1) :
    ν (unitLimitSet ∩ unitNormalize ⁻¹' E) = 1 := by
  have hEae : ∀ᵐ g ∂ν, g ∈ E := (ae_iff_measure_eq hEm.nullMeasurableSet).2 (by rw [measure_univ]; exact hE1)
  have hae : ∀ᵐ g ∂ν, g ∈ unitLimitSet ∩ unitNormalize ⁻¹' E := by
    filter_upwards [ae_mem_unitLimitSet hν, ae_unitNormalize_eq hν, hEae] with g hl h0 hgE
    refine ⟨hl, ?_⟩
    rw [mem_preimage, h0]
    exact hgE
  have h1 := (ae_iff_measure_eq
    (measurableSet_unitLimitSet.inter (measurable_unitNormalize hEm)).nullMeasurableSet).1 hae
  rwa [measure_univ] at h1

/-- A measurable set of full measure inside the property, closed under adding constants: the field normalized by
its unit circle average `g_1(0)` lies in a measurable full-measure subset of the property. -/
theorem exists_measurableSet_addConst_mem (hf : IsMollifier f) {ν : Measure LQGMetric.DistC}
    [IsProbabilityMeasure ν] (hν : LQGMetric.IsNormalizedWPGFF id ν) (hGFF : ∀ᵐ g ∂ν, OpenChartPropNoAtom γ f g) :
    ∃ E' : Set LQGMetric.DistC, MeasurableSet E' ∧ (∀ g ∈ E', OpenChartPropNoAtom γ f g) ∧
      (∀ g (c : ℝ), g ∈ E' → LQGMetric.addConst g c ∈ E') ∧ ν E' = 1 := by
  obtain ⟨E, hEm, hES, hE1⟩ :=
    exists_measurableSet_subset_measure_eq_one (S := {g | OpenChartPropNoAtom γ f g}) hGFF
  exact ⟨unitLimitSet ∩ unitNormalize ⁻¹' E, measurableSet_unitLimitSet.inter (measurable_unitNormalize hEm),
    fun g hg => noAtom_of_unitNormalize hf (hES hg.2), fun g c hg => addConst_mem_unitNormalize_preimage hg c,
    measure_unitLimitSet_inter_eq_one hν hEm hE1⟩

/-- The deterministic end of the rooting argument: the property for the rooted field recentred at the origin gives
the property for the field minus `γ log |·|`. -/
theorem noAtom_sub_log_of_affineComp (hf : IsMollifier f) {x : ℂ} (hx : ‖x‖ < 1) {h : LQGMetric.DistC}
    (hh : OpenChartPropNoAtom γ f (LQGMetric.affineComp 1 (-x) h + γ • covDist x)) :
    OpenChartPropNoAtom γ f (h - γ • MatedCRTHarmonic.MatedCRT.ofFunC fun z => Real.log ‖z‖) := by
  rw [affineComp_neg_add_covDist] at hh
  have h2 := noAtom_affineComp hf hh x
  rw [LQGMetric.GM.affineComp_one_comp, add_neg_cancel, affineComp_one_zero, add_smul_distOfFun_eq hx] at h2
  have h3 := noAtom_addFun hf h2 (-(γ • covRemainder x))
  rwa [addFun_addFun_neg] at h3

/-- **The property for `G − γ log |·|`** from the property for the normalized whole-plane GFF, on the space of
distributions with the law `ν` of the normalized whole-plane GFF. -/
theorem ae_openChartPropNoAtom_sub_log (hγ0 : 0 < γ) (hγ2 : γ < 2) (hf : IsMollifier f)
    {ν : Measure LQGMetric.DistC} [IsProbabilityMeasure ν] (hν : LQGMetric.IsNormalizedWPGFF id ν)
    (hGFF : ∀ᵐ g ∂ν, OpenChartPropNoAtom γ f g) :
    ∀ᵐ g ∂ν, OpenChartPropNoAtom γ f (g - γ • MatedCRTHarmonic.MatedCRT.ofFunC fun z => Real.log ‖z‖) := by
  obtain ⟨E', hE'm, hE'S, hE'c, hE'1⟩ := exists_measurableSet_addConst_mem hf hν hGFF
  -- rooting at a point `x` of the unit disc, and moving the root to the origin
  have hroot := ae_measure_add_covDist_mem hν hγ0 hγ2 hE'm hE'1
  have : (ae (volume.restrict (ball (0 : ℂ) 1))).NeBot :=
    ae_restrict_neBot.2 (measure_ball_pos volume (0 : ℂ) one_pos).ne'
  obtain ⟨x, hx, hxb⟩ := (hroot.and (ae_restrict_mem measurableSet_ball)).exists
  have hxn : ‖x‖ < 1 := mem_ball_zero_iff.1 hxb
  have hpole := measure_affineComp_add_covDist_mem hν hE'm hE'c hx
  have hΘm : Measurable fun h : LQGMetric.DistC => LQGMetric.affineComp 1 (-x) h + γ • covDist x :=
    LQGMetric.measurable_distOn_iff.2 fun ψ => by
      show Measurable fun h : LQGMetric.DistC => LQGMetric.affineComp 1 (-x) h ψ + (γ • covDist x) ψ
      exact ((LQGMetric.measurable_distOn_apply (LQGMetric.testAffinePull 1 (-x) ψ)).const_mul _).add
        measurable_const
  have hae2 : ∀ᵐ h ∂ν, LQGMetric.affineComp 1 (-x) h + γ • covDist x ∈ E' :=
    (ae_iff_measure_eq (hΘm hE'm).nullMeasurableSet).2 (by rw [measure_univ]; exact hpole)
  filter_upwards [hae2] with h hh
  exact noAtom_sub_log_of_affineComp hf hxn (hE'S _ hh)

/-! ### Identification of the measure -/

/-- Every point other than `0` lies in a disc with rational centre and radius whose closure avoids `0`. -/
theorem exists_rat_disc {x : ℂ} (hx0 : x ≠ 0) :
    ∃ a b r : ℚ, 0 < r ∧ (0 : ℂ) ∉ closedBall ((a : ℂ) + (b : ℂ) * Complex.I) r ∧
      x ∈ ball ((a : ℂ) + (b : ℂ) * Complex.I) r := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hm : 0 < ‖x‖ / 3 := by positivity
  obtain ⟨ρ, hρ0, hρm⟩ := exists_rat_btwn hm
  have hρq : (0 : ℚ) < ρ := by exact_mod_cast hρ0
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x.re - ρ / 2 < x.re + ρ / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x.im - ρ / 2 < x.im + ρ / 2 by linarith)
  have hcx : ‖((a : ℂ) + (b : ℂ) * Complex.I) - x‖ < ρ := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    have hre : (((a : ℂ) + (b : ℂ) * Complex.I) - x).re = (a : ℝ) - x.re := by simp
    have him : (((a : ℂ) + (b : ℂ) * Complex.I) - x).im = (b : ℝ) - x.im := by simp
    rw [hre, him]
    have h3 : |(a : ℝ) - x.re| < ρ / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    have h4 : |(b : ℝ) - x.im| < ρ / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    linarith
  refine ⟨a, b, ρ, hρq, ?_, ?_⟩
  · intro h0
    rw [mem_closedBall, dist_zero_left] at h0
    have := norm_sub_norm_le x ((a : ℂ) + (b : ℂ) * Complex.I)
    rw [norm_sub_rev] at this
    linarith
  · rw [mem_ball, dist_eq_norm, norm_sub_rev]
    exact hcx

/-- **Identification of the measure.** If `h` has the coordinate change on open sets with a measure `μ`, the chart
property on every rational disc avoiding `0` with a measure `m`, and neither measure has an atom at `0`, then
`μ = m`: on each such disc both are the vague limit of the smooth approximations of `h` (`ψ = id`). -/
theorem measure_eq_of_openChartProp (hf : IsMollifier f) {h : LQGMetric.DistC} {μ m : Measure ℂ}
    (hμ : OpenChartProp γ f h μ) (hμ0 : μ {0} = 0) (hm0 : m {0} = 0)
    (hm : ∀ a b r : ℚ, 0 < r → (0 : ℂ) ∉ closedBall ((a : ℂ) + (b : ℂ) * Complex.I) r →
      ChartProp γ f ((a : ℂ) + (b : ℂ) * Complex.I) r h m) :
    μ = m := by
  have hloc : ∀ (c : ℂ) (r : ℝ), ChartProp γ f c r h m → μ.restrict (ball c r) = m.restrict (ball c r) := by
    intro c r hcp
    have hbdd : Bornology.IsBounded (id '' ball c r) := by
      rw [image_id]
      exact isBounded_ball
    have hWo : IsOpen (id '' ball c r) := by
      rw [image_id]
      exact isOpen_ball
    obtain ⟨ν₁, h₁, hA₁⟩ := hcp id (injOn_id _) differentiableOn_id hbdd
    obtain ⟨ν₂, h₂, hA₂⟩ := hμ (ball c r) isOpen_ball id (injOn_id _) differentiableOn_id hbdd
    have hseq : ∀ k, smoothApprox γ f (id '' ball c r) (pullbackPairing γ (LQGMetric.restrictTo (disc c r) h) id)
        (HarmonicBalls.dyadicScale k) =
        smoothApprox γ f (id '' ball c r) (pullbackPairingOn γ h (ball c r) id) (HarmonicBalls.dyadicScale k) := by
      intro k
      unfold smoothApprox
      congr 1
      funext z
      split_ifs with hz
      · unfold smoothExponent
        rw [pullbackPairing_eq_pullbackPairingOn hf h (injOn_id _) differentiableOn_id subset_rfl hWo
          (HarmonicBalls.dyadicScale_pos k) hz]
      · rfl
    simp only [hseq] at h₁
    have hν : ν₁ = ν₂ := QuantumZipper.isVagueLimitOn_unique hWo h₁ h₂
    ext A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    have hAB : A ∩ ball c r ⊆ id '' ball c r := by
      rw [image_id]
      exact inter_subset_right
    have e1 := hA₁ _ (hA.inter measurableSet_ball) hAB
    have e2 := hA₂ _ (hA.inter measurableSet_ball) hAB
    have hset : ball c r ∩ id ⁻¹' (A ∩ ball c r) = A ∩ ball c r := by
      rw [preimage_id, ← inter_assoc, inter_comm (ball c r) A, inter_assoc, inter_self]
    rw [hset] at e1 e2
    rw [← e2, ← hν, e1]
  -- the rational discs avoiding `0` cover the complement of `0`
  let I := {p : ℚ × ℚ × ℚ // 0 < p.2.2 ∧
    (0 : ℂ) ∉ closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) p.2.2}
  have hcover : (⋃ i : I, ball (((i.1.1 : ℚ) : ℂ) + ((i.1.2.1 : ℚ) : ℂ) * Complex.I) (i.1.2.2 : ℝ)) =
      ({0} : Set ℂ)ᶜ := by
    ext y
    simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩ rfl
      exact i.2.2 (ball_subset_closedBall hi)
    · intro hy
      obtain ⟨a, b, r, hr, h0, hyB⟩ := exists_rat_disc hy
      exact ⟨⟨(a, b, r), hr, h0⟩, hyB⟩
  have hres : μ.restrict ({0} : Set ℂ)ᶜ = m.restrict ({0} : Set ℂ)ᶜ := by
    rw [← hcover]
    exact Measure.restrict_iUnion_congr.2 fun i => hloc _ _ (hm _ _ _ i.2.1 i.2.2)
  rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_singleton (0 : ℂ)),
    ← Measure.restrict_add_restrict_compl (μ := m) (measurableSet_singleton (0 : ℂ)),
    Measure.restrict_eq_zero.2 hμ0, Measure.restrict_eq_zero.2 hm0, hres]

end ConePoint

end LQGMeasureChart

open LQGMeasureChart LQGMeasureChart.ConePoint

/-- **The coordinate change of the LQG measure on open sets through the cone point**, from the property for the
whole-plane GFF. Given the two cited inputs (`SheffieldWangEnvelope`, `ZeroBoundaryGFFLocalRegularity`),
`0 < γ < 2`, a bump function `f`, and the hypothesis `hGFF` that a normalized whole-plane GFF almost surely has the
coordinate change on open sets with an atomless measure: for a valid environment and a measurable version `H` of its
field, almost surely `H` has the coordinate change on every open set with the LQG measure `S.μ` of the environment,
including the open sets containing the cone point `0` (Duplantier–Sheffield (2011), §3.3; Sheffield–Wang (2016),
Theorem 1.4). -/
theorem MatedCRTEnv.IsValid.ae_openChartProp_of_wholePlane (hE : SheffieldWangEnvelope)
    (hR : ZeroBoundaryGFFLocalRegularity) {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (h0 : 0 < γ) (h2 : γ < 2) {f : ℂ → ℝ}
    (hf : IsMollifier f) {H : Ω → LQGMetric.DistC}
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hGFF : ∀ (ν : Measure LQGMetric.DistC) [IsProbabilityMeasure ν], LQGMetric.IsNormalizedWPGFF id ν →
      ∀ᵐ g ∂ν, OpenChartPropNoAtom γ f g) :
    ∀ᵐ ω ∂S.P, OpenChartProp γ f (H ω) (S.μ ω) := by
  have hSW := sheffieldWangDiscConformal_of_inputs hE hR
  have hP : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  obtain ⟨G, v, hGm, hG, -, -, hGae⟩ := hS.exists_hC_eq_normalizedWPGFF_sub_log_add h0 h2
  have : IsProbabilityMeasure (S.P.map G) := (Measure.isProbabilityMeasure_map_iff hGm.aemeasurable).2 hP
  have hν : LQGMetric.IsNormalizedWPGFF id (S.P.map G) :=
    LQGMetric.DFGPS.T12.isNormalizedWPGFF_of_map_eq measurable_id hG (by rw [Measure.map_id])
  have hcan := ae_openChartPropNoAtom_sub_log h0 h2 hf hν (hGFF _ hν)
  have hΩ : ∀ᵐ ω ∂S.P, OpenChartPropNoAtom γ f
      (G ω - γ • MatedCRTHarmonic.MatedCRT.ofFunC fun z => Real.log ‖z‖) :=
    ae_of_ae_map hGm.aemeasurable hcan
  have hdiscs : ∀ᵐ ω ∂S.P, ∀ a b r : ℚ, 0 < r → (0 : ℂ) ∉ closedBall ((a : ℂ) + (b : ℂ) * Complex.I) r →
      ChartProp γ f ((a : ℂ) + (b : ℂ) * Complex.I) r (H ω) (S.μ ω) := by
    refine ae_all_iff.2 fun a => ae_all_iff.2 fun b => ae_all_iff.2 fun r => ?_
    by_cases hr : 0 < r
    · by_cases hc : (0 : ℂ) ∉ closedBall ((a : ℂ) + (b : ℂ) * Complex.I) r
      · filter_upwards [hS.ae_chartProp hSW h0 h2 hf hH _ (by exact_mod_cast hr : (0 : ℝ) < r) hc] with ω hω
        exact fun _ _ => hω
      · exact Eventually.of_forall fun _ _ h => absurd h hc
    · exact Eventually.of_forall fun _ h => absurd h hr
  have hatom : ∀ᵐ ω ∂S.P, S.μ ω {0} = 0 :=
    FirstPass.Derived.ae_coneMeasure_singleton_zero h0 h2 ⟨hS.isProbabilityMeasure, hS.isQuantumCone,
      hS.isLQGMeasure⟩
  filter_upwards [hΩ, hGae, hH, hdiscs, hatom] with ω hω hGω hHω hdω h0ω
  have hHeq : H ω = LQGMetric.addFun (G ω - γ • MatedCRTHarmonic.MatedCRT.ofFunC fun z => Real.log ‖z‖) (v ω) :=
    DFunLike.ext _ _ fun φ => by
      rw [← hHω φ, hGω φ]
      rfl
  obtain ⟨μ', hμ', hμ'0⟩ := noAtom_addFun hf hω (v ω)
  rw [← hHeq] at hμ'
  have heq : μ' = S.μ ω := measure_eq_of_openChartProp hf hμ' (hμ'0 0) h0ω hdω
  rw [← heq]
  exact hμ'

/-- **The coordinate change of the LQG measure on open sets, through the cone point**, for the mollifier
`stdMollifier`, given the property for the normalized whole-plane GFF. -/
theorem MatedCRTEnv.IsValid.ae_openChartProp (hE : SheffieldWangEnvelope) (hR : ZeroBoundaryGFFLocalRegularity)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (h0 : 0 < γ) (h2 : γ < 2) {H : Ω → LQGMetric.DistC} (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ)
    (hGFF : ∀ (ν : Measure LQGMetric.DistC) [IsProbabilityMeasure ν], LQGMetric.IsNormalizedWPGFF id ν →
      ∀ᵐ g ∂ν, OpenChartPropNoAtom γ stdMollifier g) :
    ∀ᵐ ω ∂S.P, OpenChartProp γ stdMollifier (H ω) (S.μ ω) :=
  hS.ae_openChartProp_of_wholePlane hE hR h0 h2 isMollifier_stdMollifier hH hGFF

end MatedCRT
