import MatedCRT.FirstPass.S1S2S8SA
import MatedCRT.FirstPass.S2g.Assembly2456
import MatedCRT.FirstPass.SLERef.Certified

/-!
# Closed results, Section 2 (task fp-Closure-counted-results, fp-Closure-round3, worker z1)

Closed: 2.4 (`closed_2_4`), 2.5 (`closed_2_5`), 2.6 (`closed_2_6`), 2.17 (`closed_2_17`) are aliases: they quantify over
no SLE model. 2.13 (`closed_2_13`) takes only its per-model input `FrozenAdjacentCellsMeetAe 𝒮` (no SLE package needed).
2.19 (`closed_2_19`) is stated for a model `𝒮` with certified reference model `hC : CertifiedReferenceModel ν 𝒮` (chat 186);
its input `ExitTimeUpperBoundStmt 𝒮` is `hC.exitTimeUpperBound`.
Not closed here: 2.3 (gaps G1, G2 of the report).
-/

open MeasureTheory

namespace MatedCRT

/-- Lemma 2.4 (existence up to fixed time), closed in the S2g form. Conclusion
`ConeHarmonicBallsUpToFixedTimeCanonicalStmt`. -/
alias closed_2_4 := firstPass_2_4_corrected

/-- Lemma 2.5 (scale invariance up to fixed time), closed in the S2g canonical form. -/
alias closed_2_5 := firstPass_2_5_corrected

/-- Lemma 2.6 (scale invariance), closed. Conclusion `ConeScaleInvarianceStmt`. -/
alias closed_2_6 := firstPass_2_6_corrected

/-- Lemma 2.17 (bounded exit time), closed. Hypothesis: `VolumeGrowthStmt` (cited, Lemma 2.7). -/
alias closed_2_17 := firstPass_2_17

/-- Lemma 2.13 (maximum principle), closed. The remaining per-model input is `FrozenAdjacentCellsMeetAe 𝒮`. -/
theorem closed_2_13 {𝒮 : SpaceFillingSLEModel} (hcell : FrozenAdjacentCellsMeetAe 𝒮) :
    MaximumPrincipleStmt 𝒮 :=
  firstPass_2_13 (𝒮 := 𝒮) hcell

/-- Lemma 2.19 (expected exit time, explicit bound), closed for a model `𝒮` with certified reference model `hC`. The
paper-owned input `BoundedExitTimeRVStmt` (Lemma 2.17) is `closed_2_17 h27`; `ExitTimeUpperBoundStmt 𝒮` (Lemma 2.18) is
`hC.exitTimeUpperBound`. -/
theorem closed_2_19 {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode) (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt) : ExpectedExitTimeExplicitBoundStmt 𝒮 :=
  firstPass_2_19 (h17 := closed_2_17 h27) (h18 := hC.exitTimeUpperBound)

end MatedCRT
