import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Final
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Final
import MatedCRT.FirstPass.Frozen.S3S4

/-!
# First pass: paper-owned results of Sections 3 and 4 (task fp-S3S4, q2)

Each `firstPass_<section>_<number>` takes as hypotheses only Draft statements of numbered results used by the printed
(or corrected) proof, the frozen external inputs of `MatedCRT/FirstPass/Frozen/S3S4.lean` and the existing External
inputs (`MepsScalingInput`). Cited results (Lemma 3.2, Lemmas 2.7, 2.18) get no theorem of their own.
-/

namespace MatedCRT

/-- **Lemma 3.1** (lemma:discrete-potential-tightness), corrected form (C3, C11; `DiscretePotentialTightnessCorrectedStmt`,
since the printed Draft is false). Hypotheses: `MepsScalingInput` (External, eq:meps-scaling), Lemma 2.7
(`VolumeGrowthStmt`), Lemma 2.18 (`ExitTimeUpperBoundStmt`) and the frozen corrected Lemma 3.2. -/
theorem firstPass_3_1_corrected {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    DiscretePotentialTightnessCorrectedStmt 𝒮 :=
  discretePotentialTightnessCorrected_of_inputs hm h27 h218 h32

/-- **Lemma 4.3** (lemma:discrete-basic-properties, paper line 1690). No hypothesis. -/
theorem firstPass_4_3 (𝒮 : SpaceFillingSLEModel) : DiscreteBasicPropertiesStmt 𝒮 :=
  discreteBasicProperties 𝒮

/-- **Lemma 4.4** (lemma:discrete-laplacian-bound, paper line 1708), corrected form (C7: the origin clause needs
`0 ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`; `DiscreteLaplacianBoundCorrectedStmt`). No hypothesis. -/
theorem firstPass_4_4_corrected (𝒮 : SpaceFillingSLEModel) : DiscreteLaplacianBoundCorrectedStmt 𝒮 :=
  discreteLaplacianBoundCorrected 𝒮

/-- **Lemma 4.5** (lemma:discrete-conservation-of-mass, paper line 1716), corrected form (C7;
`DiscreteConservationOfMassCorrectedStmt`). No hypothesis. -/
theorem firstPass_4_5_corrected (𝒮 : SpaceFillingSLEModel) : DiscreteConservationOfMassCorrectedStmt 𝒮 :=
  discreteConservationOfMassCorrected 𝒮

/-- **Lemma 4.7** (lemma:equibounded, paper line 1740). Hypotheses: Lemma 2.7 (`VolumeGrowthStmt`), Lemma 2.18
(`ExitTimeUpperBoundStmt`) and `MepsScalingInput` (External). -/
theorem firstPass_4_7 {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hm : MepsScalingInput 𝒮) : EquiboundedStmt 𝒮 :=
  equibounded_of_inputs h27 h218 hm

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.firstPass_3_1_corrected
#print axioms MatedCRT.firstPass_4_3
#print axioms MatedCRT.firstPass_4_4_corrected
#print axioms MatedCRT.firstPass_4_5_corrected
#print axioms MatedCRT.firstPass_4_7
