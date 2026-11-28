import MatedCRT.FirstPass.Derived.LQGMeasureChartRooting
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Moving the root to the origin: the field with a logarithmic singularity

The deterministic and law-theoretic steps around the rooting identity in the proof that the coordinate change of the
LQG measure holds through the cone point, on the space of distributions with the law `ν` of a normalized whole-plane
GFF (no transfer of a non-measurable event is needed).

* `exists_measurableSet_subset_measure_eq_one`: a property holding almost surely for the canonical field contains a
  measurable set of full measure.
* `wholePlaneCov_add_self_eq`: `Cov(h(w + x), h(x)) = -log |w| + log⁺|w + x| + log⁺|x|` for `w ≠ 0`, so the
  covariance seen from `x` is the logarithmic singularity `-log |·|` plus a continuous function.
* `affineComp_neg_add_covDist`: `g(· - x) + γ T_x = (g + γ Cov(h(· + x), h(x)))(· - x)`.
* `measure_affineComp_add_covDist_mem`: if `E` is measurable and closed under adding constants and
  `ν {g | g + γ T_x ∈ E} = 1`, then `ν {h | h(· - x) + γ T_x ∈ E} = 1`: the translated field `h(· + x)` minus its
  circle average `h_1(x)` is again a normalized whole-plane GFF (translation invariance of the whole-plane GFF modulo
  additive constants, `LQGMetric.CircleAvg.map_affine_sub_circleAvg`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

namespace LQGMeasureChart

/-- **A measurable witness of an almost sure property**: if `g ∈ S` for `ν`-almost every `g`, then some measurable
`E ⊆ S` has `ν E = 1`. -/
theorem exists_measurableSet_subset_measure_eq_one {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {S : Set α} (hS : ∀ᵐ g ∂ν, g ∈ S) :
    ∃ E, MeasurableSet E ∧ E ⊆ S ∧ ν E = 1 := by
  refine ⟨(toMeasurable ν Sᶜ)ᶜ, (measurableSet_toMeasurable ν _).compl, fun g hg => ?_, ?_⟩
  · by_contra h
    exact hg (subset_toMeasurable ν _ h)
  · rw [prob_compl_eq_one_iff (measurableSet_toMeasurable ν _), measure_toMeasurable]
    exact ae_iff.1 hS

/-- **The covariance kernel seen from `x`**: `wholePlaneCov (w + x) x = -log |w| + (log⁺|w + x| + log⁺|x|)` for
`w ≠ 0`. -/
theorem wholePlaneCov_add_self_eq {x w : ℂ} (hw : w ≠ 0) :
    LatticeProb.Gauss.wholePlaneCov (w + x) x = -Real.log ‖w‖ +
      (LatticeProb.Gauss.wholePlaneNormalization (w + x) + LatticeProb.Gauss.wholePlaneNormalization x) := by
  have hne : w + x ≠ x := fun h => hw (by simpa using h)
  rw [LatticeProb.Gauss.wholePlaneCov_eq_normalization_add hne,
    show x - (w + x) = -w by ring, norm_neg]
  ring

/-- The remainder `w ↦ log⁺|w + x| + log⁺|x|` of `wholePlaneCov_add_self_eq` is continuous. -/
theorem continuous_wholePlaneCov_add_self_remainder (x : ℂ) :
    Continuous fun w => LatticeProb.Gauss.wholePlaneNormalization (w + x) +
      LatticeProb.Gauss.wholePlaneNormalization x :=
  (LatticeProb.Gauss.continuous_wholePlaneNormalization.comp (continuous_id.add continuous_const)).add
    continuous_const

theorem locallyIntegrable_wholePlaneCov_add_self (x : ℂ) :
    LocallyIntegrable fun w => LatticeProb.Gauss.wholePlaneCov (w + x) x := by
  have h1 : LocallyIntegrable (fun y : ℂ => Real.log ‖y - 0‖) :=
    LatticeProb.LQG.AffineDerived.locallyIntegrable_comp_sub_of_integrableOn_ball
      (f := fun y : ℂ => Real.log ‖y‖) LatticeProb.LQG.AffineDerived.integrableOn_ball_log_norm 0
  simp only [sub_zero] at h1
  have h2 : LocallyIntegrable fun w => -Real.log ‖w‖ +
      (LatticeProb.Gauss.wholePlaneNormalization (w + x) + LatticeProb.Gauss.wholePlaneNormalization x) :=
    h1.neg.add (continuous_wholePlaneCov_add_self_remainder x).locallyIntegrable
  refine h2.congr ?_
  have hne : ∀ᵐ w ∂(volume : Measure ℂ), w ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with w hw
  rw [wholePlaneCov_add_self_eq hw]

private theorem testAffinePull_one_comp (x : ℂ) (φ : LQGMetric.TestC) :
    LQGMetric.testAffinePull 1 x (LQGMetric.testAffinePull 1 (-x) φ) = φ := by
  ext y
  rw [LQGMetric.testAffinePull_apply 1 x one_ne_zero, LQGMetric.testAffinePull_apply 1 (-x) one_ne_zero]
  congr 1
  simp

private theorem integral_testAffinePull_one (z : ℂ) (φ : LQGMetric.TestC) :
    ∫ y, LQGMetric.testAffinePull 1 z φ y = ∫ y, φ y := by
  simp_rw [LQGMetric.testAffinePull_apply 1 z one_ne_zero, Complex.ofReal_one, div_one]
  exact integral_sub_right_eq_self (fun y => φ y) z

private theorem affineComp_neg_addConst_affineComp (x : ℂ) (g : LQGMetric.DistC) (a : ℝ) :
    LQGMetric.affineComp 1 (-x) (LQGMetric.addConst (LQGMetric.affineComp 1 x g) a) =
      LQGMetric.addConst g a := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [LQGMetric.GFFInv.addConst_apply g a φ, LQGMetric.GFFInv.affineComp_apply 1 (-x) _ φ,
    LQGMetric.GFFInv.addConst_apply _ a, LQGMetric.GFFInv.affineComp_apply 1 x g, testAffinePull_one_comp,
    integral_testAffinePull_one]
  simp

private theorem addConst_add (g k : LQGMetric.DistC) (c : ℝ) :
    LQGMetric.addConst g c + k = LQGMetric.addConst (g + k) c := by
  simp only [LQGMetric.addConst, LQGMetric.addFun]
  abel

/-- **The shifted field seen from the root**: `g(· - x) + γ T_x = (g + γ wholePlaneCov(· + x, x))(· - x)`, where
`wholePlaneCov(w + x, x) = -log |w|` plus a continuous function (`wholePlaneCov_add_self_eq`). -/
theorem affineComp_neg_add_covDist (x : ℂ) (h : LQGMetric.DistC) (γ : ℝ) :
    LQGMetric.affineComp 1 (-x) h + γ • covDist x =
      LQGMetric.affineComp 1 (-x)
        (h + γ • distOfFun fun w => LatticeProb.Gauss.wholePlaneCov (w + x) x) := by
  refine DFunLike.ext _ _ fun φ => ?_
  show (1 ^ 2 : ℝ)⁻¹ * h (LQGMetric.testAffinePull 1 (-x) φ) + γ • covDist x φ =
    (1 ^ 2 : ℝ)⁻¹ * (h (LQGMetric.testAffinePull 1 (-x) φ) +
      γ • distOfFun (fun w => LatticeProb.Gauss.wholePlaneCov (w + x) x) (LQGMetric.testAffinePull 1 (-x) φ))
  rw [covDist_apply, distOfFun_apply (locallyIntegrable_wholePlaneCov_add_self x)]
  have hint : ∫ y, LQGMetric.testAffinePull 1 (-x) φ y * LatticeProb.Gauss.wholePlaneCov (y + x) x =
      ∫ y, φ y * LatticeProb.Gauss.wholePlaneCov y x := by
    simp_rw [LQGMetric.testAffinePull_apply 1 (-x) one_ne_zero, Complex.ofReal_one, div_one, sub_neg_eq_add]
    exact integral_add_right_eq_self (fun y => φ y * LatticeProb.Gauss.wholePlaneCov y x) x
  rw [hint]
  simp

/-- **Moving the root to the origin.** Let `ν` be the law of a normalized whole-plane GFF on the space of
distributions, `E` a measurable set of distributions closed under adding constants, and `x ∈ ℂ` with
`ν {g | g + γ T_x ∈ E} = 1`. Then `ν {h | h(· - x) + γ T_x ∈ E} = 1`, where (`affineComp_neg_add_covDist`)
`h(· - x) + γ T_x` is `h + γ wholePlaneCov(· + x, x)` translated back by `x`, i.e. the field `h` with the singularity
`-γ log |·|` plus a continuous function, recentred at `x`. The proof uses that `h(· + x) - h_1(x)` has the law `ν`. -/
theorem measure_affineComp_add_covDist_mem {ν : Measure LQGMetric.DistC} [IsProbabilityMeasure ν]
    (hν : LQGMetric.IsNormalizedWPGFF id ν) {γ : ℝ} {E : Set LQGMetric.DistC} (hE : MeasurableSet E)
    (hc : ∀ g (c : ℝ), g ∈ E → LQGMetric.addConst g c ∈ E) {x : ℂ}
    (hx : ν {g | g + γ • covDist x ∈ E} = 1) :
    ν {h | LQGMetric.affineComp 1 (-x) h + γ • covDist x ∈ E} = 1 := by
  set E' : Set LQGMetric.DistC := {g | g + γ • covDist x ∈ E} with hE'
  have hT : Measurable fun g : LQGMetric.DistC => g + γ • covDist x :=
    LQGMetric.measurable_distOn_iff.2 fun ψ => by
      show Measurable fun g : LQGMetric.DistC => g ψ + (γ • covDist x) ψ
      exact (LQGMetric.measurable_distOn_apply ψ).add measurable_const
  have hE'm : MeasurableSet E' := hT hE
  have hΘ : Measurable fun h : LQGMetric.DistC => LQGMetric.affineComp 1 (-x) h :=
    LQGMetric.measurable_distOn_iff.2 fun ψ =>
      (LQGMetric.measurable_distOn_apply (LQGMetric.testAffinePull 1 (-x) ψ)).const_mul _
  set Ψ : LQGMetric.DistC → LQGMetric.DistC := fun g =>
    LQGMetric.addConst (LQGMetric.affineComp 1 x g) (-LQGMetric.circleAvg g 1 x) with hΨdef
  have hΨ : Measurable Ψ := LQGMetric.measurable_distOn_iff.2 fun ψ => by
    simp only [hΨdef, LQGMetric.GFFInv.addConst_apply, LQGMetric.GFFInv.affineComp_apply]
    exact ((LQGMetric.measurable_distOn_apply _).const_mul _).add
      (measurable_const.mul (LQGMetric.measurable_circleAvg_left 1 x).neg)
  have hlaw : ν.map Ψ = ν := by
    have h := LQGMetric.CircleAvg.map_affine_sub_circleAvg hν one_pos x
    rw [Measure.map_id] at h
    exact h
  have hset : {h | LQGMetric.affineComp 1 (-x) h + γ • covDist x ∈ E} =
      (fun h => LQGMetric.affineComp 1 (-x) h) ⁻¹' E' := rfl
  rw [hset, ← hlaw, Measure.map_apply hΨ (hΘ hE'm)]
  refine le_antisymm prob_le_one ?_
  rw [← hx]
  refine measure_mono fun g hg => ?_
  show LQGMetric.affineComp 1 (-x)
    (LQGMetric.addConst (LQGMetric.affineComp 1 x g) (-LQGMetric.circleAvg g 1 x)) + γ • covDist x ∈ E
  rw [affineComp_neg_addConst_affineComp, addConst_add]
  exact hc _ _ hg

end LQGMeasureChart

end MatedCRT
