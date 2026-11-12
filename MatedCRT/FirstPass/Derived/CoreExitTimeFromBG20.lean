import MatedCRT.FirstPass.S5qe
import MatedCRT.FirstPass.SLERef.BG20
import MatedCRT.FirstPass.S3c.ExitTimeCore
import MatedCRT.Proofs.Sec3.ConeBallMass
import MatedCRT.FirstPass.Derived.HBBallMassHolds

/-!
# Lemma 2.18 from BG20 Proposition 5.1 alone

Lemma 2.18 of the paper (`ExitTimeUpperBoundStmt 𝒮`, the exit-time moment bounds) follows from Berestycki-Gwynne,
Proposition 5.1, eq. (5.1) (`BG20Prop51 𝒮`) and the volume growth of the γ-quantum cone (Lemma 2.7,
`VolumeGrowthStmt`), by `exitTimeUpperBoundStmt_core`. The volume growth is a theorem: it follows from the
Berestycki-Gwynne ball-mass bounds (BG20 Lemma A.1, `frozenBerestyckiGwynneConeBallMass_holds`, itself derived from
the Ding-Gwynne ball-mass bounds of the γ-LQG measure).

Hence conjunct 14 (`ExitTimeUpperBoundStmt 𝒮`) of `CertifiedReferenceModelCore ν 𝒮` is a consequence of conjunct 16
(`BG20Prop51 𝒮`), and the converse is `bg20Prop51_of_exitTime`. The constructor
`CertifiedReferenceModelCore.of_bg20Prop51` builds the core from the sixteen other conjuncts, so the core cites
BG20 Proposition 5.1 and no longer assumes the paper's own Lemma 2.18.

## Main statements

* `volumeGrowthStmt_holds`: Lemma 2.7, with no hypothesis.
* `exitTimeUpperBoundStmt_of_bg20Prop51`: Lemma 2.18 from BG20 Proposition 5.1.
* `bg20Prop51_iff_exitTimeUpperBoundStmt`: the two statements are equivalent.
* `CertifiedReferenceModelCore.of_bg20Prop51`: the core without its conjunct 14.
-/

namespace MatedCRT.FirstPass.Derived

/-- **Lemma 2.7** (volume growth of the γ-quantum cone), with no hypothesis: BG20 Lemma A.1
(`frozenBerestyckiGwynneConeBallMass_holds`) through `volumeGrowthStmt_of_berestyckiGwynne`. -/
theorem volumeGrowthStmt_holds : MatedCRT.VolumeGrowthStmt :=
  MatedCRT.volumeGrowthStmt_of_berestyckiGwynne frozenBerestyckiGwynneConeBallMass_holds

/-- **Lemma 2.18** (`ExitTimeUpperBoundStmt 𝒮`) from Berestycki-Gwynne, Proposition 5.1 (`BG20Prop51 𝒮`) alone. -/
theorem exitTimeUpperBoundStmt_of_bg20Prop51 {𝒮 : MatedCRT.SpaceFillingSLEModel} (h : MatedCRT.BG20Prop51 𝒮) :
    MatedCRT.ExitTimeUpperBoundStmt 𝒮 :=
  MatedCRT.exitTimeUpperBoundStmt_core h volumeGrowthStmt_holds

/-- BG20 Proposition 5.1 and Lemma 2.18 are equivalent for every space-filling SLE model. -/
theorem bg20Prop51_iff_exitTimeUpperBoundStmt (𝒮 : MatedCRT.SpaceFillingSLEModel) :
    MatedCRT.BG20Prop51 𝒮 ↔ MatedCRT.ExitTimeUpperBoundStmt 𝒮 :=
  ⟨exitTimeUpperBoundStmt_of_bg20Prop51, MatedCRT.bg20Prop51_of_exitTime⟩

/-- The certified reference model core from its conjuncts other than conjunct 14 (`ExitTimeUpperBoundStmt 𝒮`,
Lemma 2.18), which follows from conjunct 16 (`BG20Prop51 𝒮`, BG20 Proposition 5.1). The arguments are the
conjuncts of `CertifiedReferenceModelCore` (`FirstPass/S5qe.lean:33`) in the same order. -/
theorem CertifiedReferenceModelCore.of_bg20Prop51 {ν : ℝ → MeasureTheory.Measure MatedCRT.SLEPathCode}
    {𝒮 : MatedCRT.SpaceFillingSLEModel}
    (h1 : MatedCRT.HasNormalizedSLELaw 𝒮 ν) (h2 : MatedCRT.SLEModelClosureInput 𝒮)
    (h3 : MatedCRT.MepsScalingInput 𝒮) (h4 : MatedCRT.DegreeBoundInput 𝒮)
    (h5 : MatedCRT.CellSizeEstimateStmt 𝒮) (h6 : MatedCRT.CountingMeasureConvergenceStmt 𝒮)
    (h7 : MatedCRT.DegreeMeasureConvergenceStmt 𝒮) (h8 : MatedCRT.FrozenConeScalingLaw 𝒮)
    (h9 : MatedCRT.FrozenLBMGreenOccupationRescaled 𝒮) (h10 : MatedCRT.HasReferenceEnvironments 𝒮)
    (h11 : MatedCRT.RandomWalkToLBMStmt 𝒮) (h12 : MatedCRT.GreenKernelUpperBoundStmt 𝒮)
    (h13 : MatedCRT.GreenKernelLowerBoundStmt 𝒮)
    (h15 : MatedCRT.FrozenDiscreteHolderContinuityCorrected 𝒮) (h16 : MatedCRT.BG20Prop51 𝒮)
    (h17 : MatedCRT.FPSimilarityTransferCorrected 𝒮) :
    MatedCRT.CertifiedReferenceModelCore ν 𝒮 :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, exitTimeUpperBoundStmt_of_bg20Prop51 h16, h15, h16,
    h17⟩

end MatedCRT.FirstPass.Derived
