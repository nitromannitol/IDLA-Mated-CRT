import MatedCRT.FirstPass.S5S6S7
import MatedCRT.Steps.Sec6.ChanceOfBeingAbsorbed
import MatedCRT.Steps.Sec6.IterativeBound
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff

/-!
# FIRST PASS: Lemma 6.9 (lemma:chance-of-being-absorbed, line 2643) of arXiv:2211.04891 (corrected draft)

The printed Draft `ChanceOfBeingAbsorbedStmt` (Draft/Section6.lean:140) chooses the rate `s₃` before `s₀`. Its proof
supports only the rate chosen after `s₀` (`docs/campaign/GAPS-SEC2567A.md`). The two corrected forms
are proved here:
* `firstPass_6_9_corrected`: `ChanceOfBeingAbsorbedLocalRateStmt` (`s₃` after `s₀`), from the Draft Lemma 6.7;
* `firstPass_6_9_b_corrected`: `ChanceOfBeingAbsorbedLogLossStmt` (route (b) of E-A10, rates `∝ (1 + |log r|)⁻²`),
  from the Draft Lemmas 2.7, 2.8, 2.9, 2.16, 2.18 and the EXTERNAL whole-plane inputs of Lemma 6.4.
The printed Draft 6.9 is NOT proved here: its `s₃` is uniform in `s₀`, which needs an absorption probability bounded
below uniformly in `s₀`; the printed Lemma 6.7 gives `s₂ = s₂(s₀)` only (see the report).
-/

namespace MatedCRT

/-- **Lemma 6.9, local-rate form** (`firstPass_6_9_corrected`). Uses the Draft
Lemma 6.7 (`ConstantOrderLowerBoundStmt`); the Chernoff-type iteration (`Absorption.absorptionChernoffStep`) is proved. -/
theorem firstPass_6_9_corrected (𝒮 : SpaceFillingSLEModel) (h67 : ConstantOrderLowerBoundStmt 𝒮) :
    ChanceOfBeingAbsorbedLocalRateStmt 𝒮 :=
  chanceOfBeingAbsorbedLocalRate 𝒮 h67

/-- **Lemma 6.9, log-loss form, route (b)** (`firstPass_6_9_b_corrected`; E-A10 (b), with `s₃` chosen after `s₀`).
Uses the Draft Lemmas 2.16, 2.7, 2.8, 2.9, 2.18, the EXTERNAL whole-plane inputs `FP...` of Lemma 6.4 (the Weyl
comparison is the proved `AnnulusHitField.coneWholePlaneWeylComparison`), and the proved `circleAverageModConstStep`
and `lqgMeasureFieldMeasurableStep`. Lemma 6.8 (b) and Lemma 6.7 (b) are proved inside `chanceOfBeingAbsorbedLogLoss_final`. -/
theorem firstPass_6_9_b_corrected (𝒮 : SpaceFillingSLEModel) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h0 : FPWholePlaneLQGExistence)
    (h2 : FPWholePlaneLQGCoordinateChange) (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) :
    ChanceOfBeingAbsorbedLogLossStmt 𝒮 :=
  chanceOfBeingAbsorbedLogLoss_final 𝒮 h216 h27 h28 h29 h218 h0 AnnulusHitField.coneWholePlaneWeylComparison h2 hV hR
    Field.ConeCircle.circleAverageModConstStep (LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮)

end MatedCRT
