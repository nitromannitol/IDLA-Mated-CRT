import MatedCRT.FirstPass.S3i.LensStep

/-!
# Corrected Lemma 3.6 through the BE/lens route, with the two pending inputs as named binders (fp-S3i-3-6-closed)

`firstPass_3_6_annealed_closed` (LensStep.lean:60) concludes `CorrectedHarmonicConvergenceStmt 𝒮 ∧
CorrectedHarmonicSameWalkAnnealedStmt 𝒮` from the frozen inputs `h211`, `h28`, `hm`, `hexc`, `h32`, `hBE` and the
Lemma 7 input `hQB : QuenchedBoundsOnGoodStmt` (LensStep.lean:29).

This file replaces `hQB` by the corrected Lemma 7 of z12 (`QuenchedBoundsCorrected.lean`, not yet committed), which
takes the a.s.-exit input `hexit` as its only binder. `hexit` is the statement of z10's corrected Lemma 1 conjunct
(`srwLaw_vExitTime_lt_top_fp36`, `ExitAlmostSure.lean`, not yet committed). Until they land, both appear as named
binders with the exact types below; swap them when the theorems are committed.

Terminology: quenched law `srwLaw` and exit time `vExitTime` (Armstrong-Kuusi-Mourrat); lens of the boundary cell
(Berestycki-Powell, boundary estimate of GMS (3.31)).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **A.s. exit of the finite walk domain (corrected plan Lemma 1, conjunct 1).** For a finite exit package `FiniteExitData m A`
and a start `a ∈ A`, the simple random walk `srwLaw m a` leaves `A` almost surely. Pending: `srwLaw_vExitTime_lt_top_fp36`
(z10, `S3i/ExitAlmostSure.lean`). -/
def FP36ExitAlmostSureStmt : Prop :=
  ∀ {m : ℤ → ℤ → ℕ} {A : Set ℤ}, FiniteExitData m A → ∀ a ∈ A, srwLaw m a {x | vExitTime A x < ⊤} = 1

/-- **Corrected Lemma 3.6 through the BE/lens route, closed up to the two pending inputs.** The conclusion is
`firstPass_3_6_annealed_closed`'s, that is `CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮`
(S3i/Statement.lean:39, the corrected numbered Lemma 3.6), not the Draft conjunction `CorrectedLemma36Stmt`
(Draft/Section3HarmonicCorrected.lean:96), whose second conjunct is the retired pointwise rate. The Lemma 7 input is
`hQBc hexit`, with `hQBc` the corrected Lemma 7 (z12) and `hexit` the a.s. exit (z10). -/
theorem firstPass_3_6_closed {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hBE : FrozenOneSidedBoundaryContinuity 𝒮)
    (hQBc : FP36ExitAlmostSureStmt → QuenchedBoundsOnGoodStmt) (hexit : FP36ExitAlmostSureStmt) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  firstPass_3_6_annealed_closed h211 h28 hm hexc h32 hBE (hQBc hexit)

#print axioms MatedCRT.FirstPass36.firstPass_3_6_closed

end FirstPass36
end MatedCRT
