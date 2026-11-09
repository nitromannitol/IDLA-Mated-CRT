import MatedCRT.Draft.Section1
import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section8
import MatedCRT.Draft.SectionA
import MatedCRT.Steps.Sec8.IDLAConstrainedConvergence
import MatedCRT.Steps.Sec2.MaximumPrinciple
import MatedCRT.Steps.Sec2.BoundedExitTimeRV
import MatedCRT.Steps.Sec2.ExpectedExitTimeExplicitBound
import MatedCRT.Proofs.SecA.DiscreteDivergence
import MatedCRT.Proofs.SecA.Statements
import MatedCRT.FirstPass.Frozen.S1S2S8SA

/-!
# First pass: paper-owned results of Sections 1, 2, 8 and Appendix A (q1)

Each `firstPass_<section>_<number>` has as hypotheses only Draft statements of numbered results used by the printed
proof and the frozen external inputs of `MatedCRT/FirstPass/Frozen/S1S2S8SA.lean`. Cited results (Sections 2.2, 2.7-2.11,
2.14-2.16, 2.18) get no theorem.
-/

namespace MatedCRT

/-- **Lemma A.1** (lemma:discrete-divergence-theorem, line 3347), first pass. Proved in `Proofs/SecA/DiscreteDivergence`. -/
theorem firstPass_A_1 : DiscreteDivergenceTheoremStmt :=
  discreteDivergenceTheorem

/-- **Lemma A.2** (lemma:discrete-basic-properties-general, line 3413), first pass. No inputs: proved in
`Proofs/SecA/Statements` (`discreteBasicPropertiesGeneral`). -/
theorem firstPass_A_2 : DiscreteBasicPropertiesGeneralStmt :=
  discreteBasicPropertiesGeneral

/-- **Lemma A.3** (lemma:discrete-laplacian-bound-general, line 3448), first pass. No inputs: proved in
`Proofs/SecA/Statements` (`discreteLaplacianBoundGeneral`). -/
theorem firstPass_A_3 : DiscreteLaplacianBoundGeneralStmt :=
  discreteLaplacianBoundGeneral

/-- **Lemma A.4** (lemma:discrete-conservation-of-mass-general, line 3528), first pass. No inputs: proved in
`Proofs/SecA/Statements` (`discreteConservationOfMassGeneral`). -/
theorem firstPass_A_4 : DiscreteConservationOfMassGeneralStmt :=
  discreteConservationOfMassGeneral

/-- **Lemma 2.13** (lemma:maximum-principle, line 825, as corrected [C2]: nonempty finite `A`), first pass. Uses the
frozen mating-of-trees input `FrozenAdjacentCellsMeetAe` for the local finiteness of `𝒢^ε`. -/
theorem firstPass_2_13 {𝒮 : SpaceFillingSLEModel} (hcell : FrozenAdjacentCellsMeetAe 𝒮) :
    MaximumPrincipleStmt 𝒮 :=
  maximumPrinciple_of_steps hcell

/-- **Lemma 2.17** (lemma:bounded-exit-time, first pass). Uses the cited volume growth estimate, Lemma 2.7
(`VolumeGrowthStmt`, EXTERNAL). -/
theorem firstPass_2_17 (h27 : VolumeGrowthStmt) : BoundedExitTimeRVStmt :=
  boundedExitTimeRV_of_steps h27

/-- **Lemma 2.19** (lemma:expected-exit-time-explicit-bound, first pass). Uses Lemma 2.17 (`BoundedExitTimeRVStmt`) and
the cited exit time upper bound, Lemma 2.18 (`ExitTimeUpperBoundStmt`, EXTERNAL). -/
theorem firstPass_2_19 {𝒮 : SpaceFillingSLEModel} (h17 : BoundedExitTimeRVStmt)
    (h18 : ExitTimeUpperBoundStmt 𝒮) : ExpectedExitTimeExplicitBoundStmt 𝒮 :=
  expectedExitTimeExplicitBound_of_steps h17 h18

/-- **Proposition 8.1** (prop:IDLA-constrained-convergence, line 3270), first pass. The union bound of Propositions 5.1
(`IDLALowerBoundStmt`), 6.1 (`IDLAUpperBoundStmt`), 4.2 (`DivSandpileLowerBoundStmt`) and 7.1
(`DivSandpileUpperBoundStmt`): hypotheses are Draft statements of other numbered results. -/
theorem firstPass_8_1 {𝒮 : SpaceFillingSLEModel} (h42 : DivSandpileLowerBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮) (h71 : DivSandpileUpperBoundStmt 𝒮) :
    IDLAConstrainedConvergenceStmt 𝒮 :=
  iDLAConstrainedConvergence_of_steps 𝒮 h42 h51 h61 h71

end MatedCRT
