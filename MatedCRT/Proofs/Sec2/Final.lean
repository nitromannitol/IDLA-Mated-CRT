import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.MeasureLaw
import MatedCRT.Proofs.Measurability.ConeScaleInputs
import MatedCRT.Proofs.Measurability.BoundaryLayer
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.LQGScaling
import MatedCRT.Proofs.Sec2.ConeHarmonicBallsUpToFixedTime.Main
import MatedCRT.Proofs.Sec2.LQGMeasureProperties.ConformalCovariance
import MatedCRT.Proofs.Sec6.IDLAUpperBound.OfConeFamily

/-!
# Section 2: final assembly of Theorem 2.3 and Lemmas 2.4-2.6 (and Proposition 6.1)

The results of Section 2 on the harmonic balls of the `γ`-quantum cone, from

* the harmonic-balls Draft statements (Bou-Rabee-Gwynne, *Harmonic balls in Liouville quantum gravity*: Theorem 1.1,
  Theorem 5.5, Proposition 5.6, Lemmas 3.1-3.5, Propositions 5.2, 5.3, Lemma 5.8), bundled in
  `HarmonicBallsDraftInputs`;
* the literature input `QuantumConeScalingInput` (DMS14 Proposition 4.13(i), MatedCRT/External);
* the three cited parts of Fact 2.2 (non-atomicity, locality, dilation covariance of the LQG measure);
* Lemma 2.7 (`VolumeGrowthStmt`, BG20 Lemma A.1) where the measurability of the stopped families is used;
* the named steps not in the paper (each documented at its definition):
  `WholePlaneLogLQGExistenceStep`, `ConeRestrictionStep`, `ConeHarmonicBallLocalityStep` (Lemma 2.4),
  `ConeHarmonicBallStrictGrowthStep` (strict growth `cl Λ_s ⊆ Λ_t`; used by every route to 2.3-2.5
  and to the measurability of the stopped families), `ConeHalfBallFamilyFunctionalStep` (Lemma 2.5) and
  `ConeHarmonicBallFunctionalStep` (Lemma 2.6), the measurable dependence of the harmonic balls on the circle average
  process.

The measurability step `ConeFamilyAEMeasurableStep` is obtained without circularity (`coneFamilyAEMeasurable_final`):
`coneFamilyAEMeasurableStep_of_scaling` uses neither Lemma 2.5 nor Theorem 2.3, only Lemma 2.7, strict growth, the
quantum cone scaling and the LQG scaling of Fact 2.2.
-/

open _root_.HarmonicBalls

namespace MatedCRT

open LQGMeasure

/-- The Draft statements of the harmonic-balls paper used in Section 2 (universe `0`): Theorem 1.1, Theorem 5.5,
Proposition 5.6, Lemmas 3.1-3.5, Propositions 5.2 and 5.3, Lemma 5.8. -/
def HarmonicBallsDraftInputs : Prop :=
  ExistenceUniquenessHarmonicBallsStmt.{0} ∧ ExistenceHarmonicBallsStmt.{0} ∧ UniquenessHarmonicBallsStmt.{0} ∧
    LeastSupersolutionMemStmt.{0} ∧ ClusterOpenLaplacianStmt.{0} ∧ ClusterMonotoneStmt.{0} ∧
    ClusterConservationOfMassStmt.{0} ∧ ClusterCompatibilityStmt.{0} ∧ ClusterContinuityStmt.{0} ∧
    ClusterBoundaryMeasureZeroStmt.{0} ∧ ClusterStrongCompatibilityStmt.{0}

/-- **Fact 2.2** from its three cited parts. -/
theorem lqgMeasureProperties_final (hna : LQGMeasureNonAtomicPart) (hloc : LQGMeasureLocalityPart)
    (hdil : LQGMeasureDilationCovariancePart) : LQGMeasurePropertiesStmt :=
  lqgMeasureProperties_of_citedParts hna hloc hdil

/-- **Measurability of the stopped harmonic ball families of the cone** (`ConeFamilyAEMeasurableStep`), without
Lemma 2.5 or Theorem 2.3: from Lemma 2.7, strict growth, the quantum cone scaling and Fact 2.2. -/
theorem coneFamilyAEMeasurable_final (h27 : VolumeGrowthStmt) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hscale : QuantumConeScalingInput) (hna : LQGMeasureNonAtomicPart) (hloc : LQGMeasureLocalityPart)
    (hdil : LQGMeasureDilationCovariancePart) : ConeFamilyAEMeasurableStep :=
  coneFamilyAEMeasurableStep_of_scaling h27 hgrow hscale
    (coneLQGScalingStep_of_steps (lqgMeasureProperties_final hna hloc hdil) (coneScaleRadiusPosStep_of_input hscale))

/-- **Lemma 2.4** (lemma:existence-up-to-fixed-time, line 533). -/
theorem coneHarmonicBallsUpToFixedTime_final (hHB : HarmonicBallsDraftInputs) (h0 : WholePlaneLogLQGExistenceStep)
    (h3 : ConeRestrictionStep) (h4 : ConeHarmonicBallLocalityStep) (hgrow : ConeHarmonicBallStrictGrowthStep) :
    ConeHarmonicBallsUpToFixedTimeStmt := by
  obtain ⟨h11, h55, h56, h31, h32, h33, h34, h35, h52, h53, h58⟩ := hHB
  exact coneHarmonicBallsUpToFixedTime_of_hb h11 h55 h56 h31 h32 h33 h34 h35 h52 h53 h58 h0 h3 h4 hgrow

/-- **Lemma 2.5** (lemma:scale-invariance-up-to-fixed-time, line 548). -/
theorem coneScaleInvarianceUpToFixedTime_final (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hscale : QuantumConeScalingInput) (hna : LQGMeasureNonAtomicPart) (hloc : LQGMeasureLocalityPart)
    (hdil : LQGMeasureDilationCovariancePart) (hfun : ConeHalfBallFamilyFunctionalStep) :
    ConeScaleInvarianceUpToFixedTimeStmt :=
  coneScaleInvarianceUpToFixedTime_of_scaleRadiusPos hscale (lqgMeasureProperties_final hna hloc hdil)
    (coneScaleRadiusPosStep_of_input hscale) hgrow hfun

/-- **Lemma 2.6** (lemma:scale-invariance, line 562). -/
theorem coneScaleInvariance_final (hscale : QuantumConeScalingInput) (hna : LQGMeasureNonAtomicPart)
    (hloc : LQGMeasureLocalityPart) (hdil : LQGMeasureDilationCovariancePart)
    (hfun : ConeHarmonicBallFunctionalStep) : ConeScaleInvarianceStmt :=
  coneScaleInvariance_of_scaleRadiusPos hscale (lqgMeasureProperties_final hna hloc hdil)
    (coneScaleRadiusPosStep_of_input hscale) hfun

/-- **Theorem 2.3** (thm:cone-harmonic-balls, line 520), from Lemmas 2.4, 2.5 and the measurability of the stopped
families (`coneFamilyAEMeasurable_final`). -/
theorem coneHarmonicBalls_final (hHB : HarmonicBallsDraftInputs) (h0 : WholePlaneLogLQGExistenceStep)
    (h3 : ConeRestrictionStep) (h4 : ConeHarmonicBallLocalityStep) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hscale : QuantumConeScalingInput) (hna : LQGMeasureNonAtomicPart) (hloc : LQGMeasureLocalityPart)
    (hdil : LQGMeasureDilationCovariancePart) (h27 : VolumeGrowthStmt) (hfun : ConeHalfBallFamilyFunctionalStep) :
    ConeHarmonicBallsStmt :=
  coneHarmonicBalls_of_steps (coneHarmonicBallsUpToFixedTime_final hHB h0 h3 h4 hgrow)
    (coneScaleInvarianceUpToFixedTime_final hgrow hscale hna hloc hdil hfun)
    (coneFamilyAEMeasurable_final h27 hgrow hscale hna hloc hdil)

/-- **`BoundaryLayerMeasurableStep`** (gap of the proof of Proposition 6.1, line 2875) from Lemma 2.4 and the
measurability of the stopped families. -/
theorem boundaryLayerMeasurableStep_final (𝒮 : SpaceFillingSLEModel) (hHB : HarmonicBallsDraftInputs)
    (h0 : WholePlaneLogLQGExistenceStep) (h3 : ConeRestrictionStep) (h4 : ConeHarmonicBallLocalityStep)
    (hgrow : ConeHarmonicBallStrictGrowthStep) (hscale : QuantumConeScalingInput) (hna : LQGMeasureNonAtomicPart)
    (hloc : LQGMeasureLocalityPart) (hdil : LQGMeasureDilationCovariancePart) (h27 : VolumeGrowthStmt) :
    BoundaryLayerMeasurableStep 𝒮 :=
  boundaryLayerMeasurableStep_of_coneFamilyAEMeasurable 𝒮 (coneFamilyAEMeasurable_final h27 hgrow hscale hna hloc hdil)
    (coneHarmonicBallsUpToFixedTime_final hHB h0 h3 h4 hgrow)

/-- **Proposition 6.1** (prop:IDLA-upper-bound, line 2252) from Lemma 6.10, Proposition 5.1 and the Section 2
inputs of Lemma 2.4 and of the measurability of the stopped families. -/
theorem iDLAUpperBound_final (𝒮 : SpaceFillingSLEModel) (h610 : IterativeBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (hHB : HarmonicBallsDraftInputs) (h0 : WholePlaneLogLQGExistenceStep)
    (h3 : ConeRestrictionStep) (h4 : ConeHarmonicBallLocalityStep) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hscale : QuantumConeScalingInput) (hna : LQGMeasureNonAtomicPart) (hloc : LQGMeasureLocalityPart)
    (hdil : LQGMeasureDilationCovariancePart) (h27 : VolumeGrowthStmt) : IDLAUpperBoundStmt 𝒮 :=
  iDLAUpperBound_of_coneFamilyAEMeasurable 𝒮 h610 h51 (coneFamilyAEMeasurable_final h27 hgrow hscale hna hloc hdil)
    (coneHarmonicBallsUpToFixedTime_final hHB h0 h3 h4 hgrow)

end MatedCRT
