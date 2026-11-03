import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Statement

/-!
# Lemma 6.9 (lemma:chance-of-being-absorbed, line 2626), local-rate reading (ESCALATION E-c5-1)

From Lemma 6.8 and Lemmas 2.7, 2.8, 2.19, through Lemma 6.7.
-/

namespace MatedCRT

/-- **Lemma 6.9** (rate `s₃` chosen after `s₀`, E-c5-1) from Lemma 6.8 and Lemmas 2.7, 2.8, 2.19. -/
theorem chanceOfBeingAbsorbedLocalRate_of_div (𝒮 : SpaceFillingSLEModel) (h68 : ConstantOrderLowerBoundDivStmt 𝒮)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮) (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) :
    ChanceOfBeingAbsorbedLocalRateStmt 𝒮 :=
  chanceOfBeingAbsorbedLocalRate 𝒮 (constantOrderLowerBound 𝒮 h68 h27 h28 h219)

end MatedCRT
