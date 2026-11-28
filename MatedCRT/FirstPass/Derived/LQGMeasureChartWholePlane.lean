import MatedCRT.FirstPass.Derived.LQGMeasureChartOpenPatch
import MatedCRT.FirstPass.Derived.LQGMeasureChartSheffieldWang
import HarmonicBalls.Proofs.GFF.CoordinateModification
import HarmonicBalls.FirstPass.LPBridge.M1
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPArea
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.LQG.GMCDyadicLimit
import LatticeProb.LQG.WholePlaneProfileLaw
import LatticeProb.LQG.ConeAreaSpatialAE
import LatticeProb.LQG.LQGMeasureNonatomicUpper

/-!
# The coordinate change of the LQG measure of the whole-plane GFF on open sets

For the normalized whole-plane GFF `g` and `0 < γ < 2`, almost surely the γ-LQG area measure `lqgArea γ g` (the
dyadic vague limit of `2^{-kγ²/2} e^{γ g_{2^{-k}}(z)} dz`) has the coordinate change on every open set
(`OpenChartProp`) and has no atoms:

* the area measure exists almost surely (`MatedCRTHarmonic.LQGCoord.ae_exists_isVagueLimitC_wp`), so its restriction
  to a disc is the vague limit in the disc of the circle approximations; the coordinate change on discs
  (`ae_chartProp_wholePlane`, Sheffield–Wang, *Field-measure correspondence in Liouville quantum gravity almost
  surely commutes with all conformal maps simultaneously* (arXiv:1605.06171v2), Theorems 1.1, 1.2 and 1.4) on the
  countably many rational discs patches to open sets (`openChartProp_of_chartProp`);
* no atoms: the area measure is almost surely the LQG measure of the circle-average process of the field
  (`LatticeProb.LQG.ae_lqgArea_eq_of_isLQGMeasure_ae`, the circle averages agreeing for Lebesgue-almost every
  centre at every dyadic radius), which has no atoms
  (`LatticeProb.LQG.LQGMeasureNonatomicUpper.ae_singleton_eq_zero_of_isWholePlaneGFF`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace MatedCRT

namespace LQGMeasureChart

namespace WholePlane

/-- A dyadic vague limit on `ℂ` of the area approximations of `g` is a dyadic LQG limit of the circle averages
of `g`. -/
theorem isLQGLimit_of_isVagueLimitC {γ : ℝ} {g : LQGMetric.DistC} {m : Measure ℂ}
    (hm : MatedCRTHarmonic.CellScaling.IsVagueLimitC (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ g) m) :
    HarmonicBalls.IsLQGLimit γ (LQGMetric.circleAvg g) m := by
  have hs : ∀ k : ℕ, MatedCRTHarmonic.CellScaling.dyadicScale k = HarmonicBalls.dyadicScale k := fun k => by
    rw [MatedCRTHarmonic.CellScaling.dyadicScale, HarmonicBalls.dyadicScale, zpow_neg, zpow_natCast, inv_pow]
  have ha : ∀ k : ℕ, MatedCRTHarmonic.CellScaling.lqgAreaApprox γ g k =
      HarmonicBalls.lqgApprox γ (LQGMetric.circleAvg g) (HarmonicBalls.dyadicScale k) := fun k => by
    rw [MatedCRTHarmonic.CellScaling.lqgAreaApprox, HarmonicBalls.lqgApprox, hs]
  have : IsFiniteMeasureOnCompacts m := ⟨fun K hK => hm.1 K hK⟩
  refine ⟨inferInstance, fun φ hφ hφc => ?_⟩
  have h := hm.2 φ hφ hφc
  simp only [ha] at h
  exact h

/-- For the normalized whole-plane GFF, almost surely the area measure is the dyadic vague limit on `ℂ` of the
area approximations. -/
theorem ae_isVagueLimitC_lqgArea {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ν : Measure LQGMetric.DistC}
    [IsProbabilityMeasure ν] (hν : LQGMetric.IsNormalizedWPGFF id ν) :
    ∀ᵐ g ∂ν, MatedCRTHarmonic.CellScaling.IsVagueLimitC (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ g)
      (MatedCRTHarmonic.CellScaling.lqgArea γ g) := by
  filter_upwards [MatedCRTHarmonic.LQGCoord.ae_exists_isVagueLimitC_wp hν.1 hγ0 hγ2] with g hg
  obtain ⟨m, hm⟩ := hg
  have hm' : MatedCRTHarmonic.CellScaling.IsVagueLimitC (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ g) m := hm
  rw [MatedCRTHarmonic.LQGCoord.lqgArea_eq_of_isVagueLimitC hm']
  exact hm'

theorem measurable_profile_eval (F : LQGMetric.DistC → C(LatticeProb.Gauss.CircleParameter, ℝ)) (hF : Measurable F)
    (r : Set.Ioi (0 : ℝ)) : Measurable fun x : ℂ × LQGMetric.DistC => F x.2 (r, x.1) :=
  measurable_uncurry_of_continuous_of_measurable (u := fun z g => F g (r, z))
    (fun g => (F g).continuous.comp (continuous_const.prodMk continuous_id))
    (fun _ => (continuous_eval_const _).measurable.comp hF)

theorem measurable_circleAvg_swap (r : ℝ) :
    Measurable fun x : ℂ × LQGMetric.DistC => LQGMetric.circleAvg x.2 r x.1 :=
  LQGMetric.measurable_circleAvg.comp (f := fun x : ℂ × LQGMetric.DistC => (x.2, r, x.1))
    (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))

theorem ae_hcirc_eq_circleAvg_of_cInc {ν : Measure LQGMetric.DistC} (hν : LQGMetric.IsNormalizedWPGFF id ν)
    {hcirc : LQGMetric.DistC → ℝ → ℂ → ℝ}
    (hc : ∀ r, 0 < r → ∀ z, (fun g => hcirc g r z) =ᵐ[ν]
      LQGMetric.CircleAvg.cInc (id : LQGMetric.DistC → LQGMetric.DistC) r z 1 0)
    {r : ℝ} (hr : 0 < r) (z : ℂ) : ∀ᵐ g ∂ν, hcirc g r z = LQGMetric.circleAvg g r z := by
  filter_upwards [hc r hr z, hν.2] with g h1 h2
  have h1' : hcirc g r z = LQGMetric.circleAvg g r z - LQGMetric.circleAvg g 1 0 := h1
  have h2' : LQGMetric.circleAvg g 1 0 = 0 := h2
  rw [h1', h2', sub_zero]

theorem ae_ae_profile_eq {ν : Measure LQGMetric.DistC} [IsProbabilityMeasure ν]
    (hν : LQGMetric.IsNormalizedWPGFF id ν) {hcirc : LQGMetric.DistC → ℝ → ℂ → ℝ}
    (hc : ∀ r, 0 < r → ∀ z, (fun g => hcirc g r z) =ᵐ[ν]
      LQGMetric.CircleAvg.cInc (id : LQGMetric.DistC → LQGMetric.DistC) r z 1 0)
    (F : LQGMetric.DistC → C(LatticeProb.Gauss.CircleParameter, ℝ)) (hF : Measurable F)
    (hFc : ∀ᵐ g ∂ν, ∀ p : LatticeProb.Gauss.CircleParameter, F g p = hcirc g p.1 p.2) (r : Set.Ioi (0 : ℝ)) :
    ∀ᵐ g ∂ν, ∀ᵐ z ∂(volume : Measure ℂ), F g (r, z) = LQGMetric.circleAvg g r z := by
  have hmeas : MeasurableSet {x : ℂ × LQGMetric.DistC | F x.2 (r, x.1) = LQGMetric.circleAvg x.2 r x.1} :=
    measurableSet_eq_fun (measurable_profile_eval F hF r) (measurable_circleAvg_swap r)
  refine (Measure.ae_ae_comm hmeas).1 (Eventually.of_forall fun z => ?_)
  filter_upwards [hFc, ae_hcirc_eq_circleAvg_of_cInc hν hc r.2 z] with g h1 h2
  rw [h1]
  exact h2

/-- **Circle averages of the coordinates.** For circle averages `hcirc` agreeing, at each radius and centre, almost
surely with those of the normalized field, almost surely at every dyadic radius they agree for Lebesgue-almost
every centre (Fubini, through a jointly measurable continuous version of `hcirc`). -/
theorem ae_hcirc_eq_circleAvg {ν : Measure LQGMetric.DistC} [IsProbabilityMeasure ν]
    (hν : LQGMetric.IsNormalizedWPGFF id ν) {hC : LQGMetric.DistC → (ℂ → ℝ) → ℝ}
    {hcirc : LQGMetric.DistC → ℝ → ℂ → ℝ} (hgff : LatticeProb.Gauss.IsWholePlaneGFF ν hC hcirc)
    (hc : ∀ r, 0 < r → ∀ z, (fun g => hcirc g r z) =ᵐ[ν]
      LQGMetric.CircleAvg.cInc (id : LQGMetric.DistC → LQGMetric.DistC) r z 1 0) :
    ∀ᵐ g ∂ν, ∀ k : ℕ, ∀ᵐ z ∂(volume : Measure ℂ),
      hcirc g (LatticeProb.LQG.dyadicScale k) z = LQGMetric.circleAvg (id g) (LatticeProb.LQG.dyadicScale k) z := by
  have hpos : ∀ k : ℕ, 0 < LatticeProb.LQG.dyadicScale k := fun k => by
    unfold LatticeProb.LQG.dyadicScale
    positivity
  obtain ⟨F, hF, hFc⟩ := LatticeProb.LQG.exists_measurable_profile hgff
  have hk : ∀ k : ℕ, ∀ᵐ g ∂ν, ∀ᵐ z ∂(volume : Measure ℂ),
      F g (⟨LatticeProb.LQG.dyadicScale k, hpos k⟩, z) = LQGMetric.circleAvg g (LatticeProb.LQG.dyadicScale k) z :=
    fun k => ae_ae_profile_eq hν hc F hF hFc ⟨LatticeProb.LQG.dyadicScale k, hpos k⟩
  filter_upwards [ae_all_iff.2 hk, hFc] with g hg hFg k
  filter_upwards [hg k] with z hz
  exact (hFg (⟨LatticeProb.LQG.dyadicScale k, hpos k⟩, z)).symm.trans hz

end WholePlane

open WholePlane

/-- **No atoms.** For the normalized whole-plane GFF and `0 < γ < 2`, almost surely the γ-LQG area measure has no
atoms. -/
theorem ae_lqgArea_singleton_eq_zero {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {ν : Measure LQGMetric.DistC}
    [IsProbabilityMeasure ν] (hν : LQGMetric.IsNormalizedWPGFF id ν) :
    ∀ᵐ g ∂ν, ∀ x : ℂ, MatedCRTHarmonic.CellScaling.lqgArea γ g {x} = 0 := by
  obtain ⟨hC, hcirc, hg, -, hc⟩ := HarmonicBalls.normalizedGFF_exists_projectGFF hν
  have hgff := (HarmonicBalls.LPBridge.isWholePlaneGFF_iff ν hC hcirc).1 hg
  obtain ⟨μ₀, hμ₀⟩ := hgff.exists_isLQGMeasure hγ0 hγ2
  have hfield : LatticeProb.LQG.IsLQGMeasureOfField ν γ 0 hcirc μ₀ := by
    have e : (fun g => LatticeProb.Gauss.fieldCircleAverage 0 (hcirc g)) = hcirc := by
      funext g r z
      simp [LatticeProb.Gauss.fieldCircleAverage]
    rw [LatticeProb.LQG.IsLQGMeasureOfField, e]
    exact hμ₀
  have hna :=
    LatticeProb.LQG.LQGMeasureNonatomicUpper.ae_singleton_eq_zero_of_isWholePlaneGFF hγ0 hγ2 hgff hfield
  have hid := LatticeProb.LQG.ae_lqgArea_eq_of_isLQGMeasure_ae (h := id) hμ₀ (ae_hcirc_eq_circleAvg hν hgff hc)
  filter_upwards [hna, hid] with g h0 he x
  have he' : MatedCRTHarmonic.CellScaling.lqgArea γ g = μ₀ g := he
  rw [he']
  exact h0 x

/-- **The coordinate change on open sets for the whole-plane GFF.** Given the inputs of
`sheffieldWangDiscConformal_of_inputs`, `0 < γ < 2` and a bump function `f`: for the normalized whole-plane GFF,
almost surely the field has the coordinate change on every open set with its γ-LQG area measure, and this measure
has no atoms. -/
theorem ae_openChartProp_lqgArea_wholePlane (hE : SheffieldWangEnvelope) (hR : ZeroBoundaryGFFLocalRegularity)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {f : ℂ → ℝ} (hf : IsMollifier f) {ν : Measure LQGMetric.DistC}
    [IsProbabilityMeasure ν] (hν : LQGMetric.IsNormalizedWPGFF id ν) :
    ∀ᵐ g ∂ν, OpenChartProp γ f g (MatedCRTHarmonic.CellScaling.lqgArea γ g) ∧
      ∀ x : ℂ, MatedCRTHarmonic.CellScaling.lqgArea γ g {x} = 0 := by
  have hSW := sheffieldWangDiscConformal_of_inputs hE hR
  have hV := ae_isVagueLimitC_lqgArea hγ0 hγ2 hν
  have hdisc : ∀ (c : ℂ) (r : ℝ), 0 < r →
      ∀ᵐ g ∂ν, ChartProp γ f c r g (MatedCRTHarmonic.CellScaling.lqgArea γ g) := fun c r hr => by
    have h := ae_chartProp_wholePlane hSW hγ0 hγ2 hf hν.1 c hr
      (μ := fun g => MatedCRTHarmonic.CellScaling.lqgArea γ g) (by
        filter_upwards [hV] with g hg
        exact isVagueLimitOn_restrict_of_isLQGLimit (isLQGLimit_of_isVagueLimitC hg) isOpen_ball)
    exact h
  have h1 : ∀ᵐ g ∂ν, ∀ a b r : ℚ, 0 < r → (0 : ℂ) ∉ closedBall ((a : ℂ) + (b : ℂ) * Complex.I) r →
      ChartProp γ f ((a : ℂ) + (b : ℂ) * Complex.I) r g (MatedCRTHarmonic.CellScaling.lqgArea γ g) := by
    refine ae_all_iff.2 fun a => ae_all_iff.2 fun b => ae_all_iff.2 fun r => ?_
    by_cases hr : 0 < r
    · filter_upwards [hdisc ((a : ℂ) + (b : ℂ) * Complex.I) r (by exact_mod_cast hr)] with g hg
      exact fun _ _ => hg
    · exact Eventually.of_forall fun _ h => absurd h hr
  have h2 : ∀ᵐ g ∂ν, ∀ r : ℚ, 0 < r → ChartProp γ f 0 r g (MatedCRTHarmonic.CellScaling.lqgArea γ g) := by
    refine ae_all_iff.2 fun r => ?_
    by_cases hr : 0 < r
    · filter_upwards [hdisc 0 r (by exact_mod_cast hr)] with g hg
      exact fun _ => hg
    · exact Eventually.of_forall fun _ h => absurd h hr
  filter_upwards [hV, h1, h2, ae_lqgArea_singleton_eq_zero hγ0 hγ2 hν] with g hVg h1g h2g h0g
  exact ⟨openChartProp_of_chartProp hf hVg.1 h1g h2g, h0g⟩

end LQGMeasureChart

end MatedCRT
