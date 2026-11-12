import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Lemma27

/-!
# Enlarging the sample space of a GMS19 cell model

A cell model `M` (Bonanno's `MatedCRTHarmonic.GMSLemma27.CellModel`: field, `γ`-LQG area measure and space-filling
curve parametrized by area, on a probability space `(Ω, P)`) can be read on the enlarged sample space `Ω × β` under
`P ⊗ ν`, for any probability measure `ν`, through the first coordinate (`prodRightCellModel`). Every event of the
enlarged model which is the preimage of an event of `M` has the same probability, for every set (the product measure
of a cylinder `A ×ˢ univ` is `P A`, without measurability). Hence:

* `segmentsContainBalls_prodRight`: GHM15 Proposition 3.4 + Remark 3.9 (`SegmentsContainBalls`) for `M` gives it for
  the enlarged model;
* `lemma27_segments_of_prodRight`: the conclusion of GMS19 Lemma 2.7 (`lemma27_segments`) for `M` holds as soon as
  the comparison with a whole-plane GFF on `B_1` (`AreaDominatesWholePlaneGFF`) holds for the enlarged model.

The point is that the comparison field, a whole-plane GFF which agrees with `h + γ log |·|` on `B_1`, needs a
Brownian motion independent of `h|_{B_1}` (its radial part outside `B_1`); on the enlarged space `Ω × C(ℝ≥0, ℝ)`
under `P ⊗ BM` the second coordinate is such a Brownian motion.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric
open MatedCRTHarmonic.GMSLemma27

variable {γ : ℝ}

/-- For a probability measure `ν`, the product measure `P ⊗ ν` of the preimage of any set `A` under the first
coordinate is `P A`. -/
theorem prod_measure_fst_preimage {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    (ν : Measure β) [IsProbabilityMeasure ν] (A : Set Ω) :
    (P.prod ν) (Prod.fst ⁻¹' A) = P A := by
  rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]

/-- The cell model `M` read on the enlarged sample space `M.Ω × β` under `M.P ⊗ ν`, through the first coordinate. -/
noncomputable def prodRightCellModel (M : CellModel γ) {β : Type} [MeasurableSpace β] (ν : Measure β)
    [IsProbabilityMeasure ν] : CellModel γ where
  Ω := M.Ω × β
  P := M.P.prod ν
  field := fun x => M.field x.1
  area := fun x => M.area x.1
  curve := fun x => M.curve x.1
  ae_continuous_curve := Measure.quasiMeasurePreserving_fst.ae M.ae_continuous_curve
  ae_curve_zero := Measure.quasiMeasurePreserving_fst.ae M.ae_curve_zero
  ae_area_curve := Measure.quasiMeasurePreserving_fst.ae M.ae_area_curve

section

variable (M : CellModel γ) {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]

theorem prodRightCellModel_P_fst_preimage (A : Set M.Ω) :
    (prodRightCellModel M ν).P (Prod.fst ⁻¹' A) = M.P A :=
  prod_measure_fst_preimage M.P ν A

theorem segmentBallEvent_prodRight (R r ε : ℝ) :
    segmentBallEvent (prodRightCellModel M ν) R r ε = Prod.fst ⁻¹' segmentBallEvent M R r ε :=
  rfl

theorem segmentDiamGood_prodRight (ε q ρ : ℝ) :
    segmentDiamGood (prodRightCellModel M ν) ε q ρ = Prod.fst ⁻¹' segmentDiamGood M ε q ρ :=
  rfl

/-- GHM15 Proposition 3.4 + Remark 3.9 for a cell model gives it for the enlarged model. -/
theorem segmentsContainBalls_prodRight (hSLE : SegmentsContainBalls M) :
    SegmentsContainBalls (prodRightCellModel M ν) := by
  intro r hr R hR s
  have h := hSLE r hr R hR s
  have hfun : (fun ε : ℝ => ((prodRightCellModel M ν).P (segmentBallEvent (prodRightCellModel M ν) R r ε)ᶜ).toReal) =
      fun ε : ℝ => (M.P (segmentBallEvent M R r ε)ᶜ).toReal := by
    funext ε
    exact congrArg ENNReal.toReal (prodRightCellModel_P_fst_preimage M ν (segmentBallEvent M R r ε)ᶜ)
  rw [hfun]
  exact h

/-- **GMS19 Lemma 2.7 through an enlarged sample space.** The conclusion of `lemma27_segments` for `M` holds when the
comparison with a whole-plane GFF on `B_1` holds for `M` read on `M.Ω × β` under `M.P ⊗ ν`. -/
theorem lemma27_segments_of_prodRight (hSLE : SegmentsContainBalls M) (hGMC : GMCLowerTail γ)
    (hdom : AreaDominatesWholePlaneGFF (prodRightCellModel M ν)) (hγ : 0 < γ) {q ρ α : ℝ} (hq : 0 < q)
    (hq' : q < 2 / (2 + γ) ^ 2) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα : α < lemma27Exponent q γ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1, M.P (segmentDiamGood M ε q ρ)ᶜ ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨C, hC⟩ := lemma27_segments (prodRightCellModel M ν) (segmentsContainBalls_prodRight M ν hSLE) hGMC hdom
    hγ hq hq' hρ0 hρ1 hα
  refine ⟨C, fun ε hε => ?_⟩
  rw [← prodRightCellModel_P_fst_preimage M ν (segmentDiamGood M ε q ρ)ᶜ]
  exact hC ε hε

end

end MatedCRT.FirstPass.Derived
