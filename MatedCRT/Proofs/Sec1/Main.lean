import MatedCRT.Proofs.Sec1.ScaledClusterExitTime

/-!
# Theorems 1.4 and 1.6: the scaling steps discharged (Section 8.1, lines 3284-3336)

The reductions `convergenceOfIDLA_of_steps`, `convergenceOfDivSandpile_of_steps` (Steps/Sec1/Convergence.lean) take
four scaling steps. Three of them are proved or reduced here:
* `HarmonicBallFamilyScalingStep`: proved (`harmonicBallFamilyScalingStep`);
* `ConeScaleRadiusStep`: from `QuantumConeScalingInput` (`coneScaleRadiusStep_of_input`);
* `ScaledClusterExitTimeStep`: from Lemma 2.5, `ConeFamilyAEMeasurableStep` and `ConeHarmonicBallStrictGrowthStep`
  (`scaledClusterExitTimeStep_of_steps`).
The fourth, `ConeEnvironmentScalingStep` (the rescaled environment is valid), remains a hypothesis. Through the reductions of Lemma 2.5 and of `ConeFamilyAEMeasurableStep`, the Section 2 hypotheses
become Fact 2.2, strict growth and the half-ball functional step (`..._of_coneSteps`).
-/

namespace MatedCRT

/-- **Theorem 1.4** from Proposition 8.1, the validity of the rescaled environment, the scaling of the quantum cone,
Lemma 2.5 and the measurability and strict growth of the cone harmonic ball families. -/
theorem convergenceOfIDLA_of_scalingInputs (𝒮 : SpaceFillingSLEModel) (h81 : IDLAConstrainedConvergenceStmt 𝒮)
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hscale : QuantumConeScalingInput)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt) (hmeas : ConeFamilyAEMeasurableStep)
    (hgrow : ConeHarmonicBallStrictGrowthStep) : ConvergenceOfIDLAStmt 𝒮 :=
  convergenceOfIDLA_of_steps 𝒮 h81 hEnv harmonicBallFamilyScalingStep (coneScaleRadiusStep_of_input hscale)
    (scaledClusterExitTimeStep_of_steps h25 hmeas hgrow)

/-- **Theorem 1.6** from Proposition 8.1, the validity of the rescaled environment, the scaling of the quantum cone,
Lemma 2.5 and the measurability and strict growth of the cone harmonic ball families. -/
theorem convergenceOfDivSandpile_of_scalingInputs (𝒮 : SpaceFillingSLEModel)
    (h81 : IDLAConstrainedConvergenceStmt 𝒮) (hEnv : ConeEnvironmentScalingStep 𝒮)
    (hscale : QuantumConeScalingInput) (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (hmeas : ConeFamilyAEMeasurableStep) (hgrow : ConeHarmonicBallStrictGrowthStep) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  convergenceOfDivSandpile_of_steps 𝒮 h81 hEnv harmonicBallFamilyScalingStep (coneScaleRadiusStep_of_input hscale)
    (scaledClusterExitTimeStep_of_steps h25 hmeas hgrow)

/-- Lemma 2.5 and `ConeFamilyAEMeasurableStep` from Fact 2.2, strict growth and the half-ball functional step
(the reductions, with `ConeScaleRadiusPosStep`, `ConeRescaledCircleAEMeasurableStep` discharged by the
scaling of the quantum cone). -/
theorem coneScaleInvarianceUpToFixedTime_and_aemeasurable_of_coneSteps (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hfun : ConeHalfBallFamilyFunctionalStep) :
    ConeScaleInvarianceUpToFixedTimeStmt ∧ ConeFamilyAEMeasurableStep :=
  ⟨coneScaleInvarianceUpToFixedTime_of_inputs hscale h22 (coneScaleRadiusPosStep_of_input hscale) hgrow
      (coneRescaledCircleAEMeasurableStep_of_input hscale) hfun,
    coneFamilyAEMeasurableStep_of_steps hscale hgrow
      (coneLQGScalingStep_of_steps h22 (coneScaleRadiusPosStep_of_input hscale))
      (coneRescaledCircleAEMeasurableStep_of_input hscale) hfun⟩

/-- **Theorem 1.4** from Proposition 8.1, `ConeEnvironmentScalingStep`, `QuantumConeScalingInput`, Fact 2.2 and the
two open steps of Theorem 2.3 (strict growth, half-ball functional step). -/
theorem convergenceOfIDLA_of_coneSteps (𝒮 : SpaceFillingSLEModel) (h81 : IDLAConstrainedConvergenceStmt 𝒮)
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (hgrow : ConeHarmonicBallStrictGrowthStep) (hfun : ConeHalfBallFamilyFunctionalStep) :
    ConvergenceOfIDLAStmt 𝒮 :=
  have h := coneScaleInvarianceUpToFixedTime_and_aemeasurable_of_coneSteps hscale h22 hgrow hfun
  convergenceOfIDLA_of_scalingInputs 𝒮 h81 hEnv hscale h.1 h.2 hgrow

/-- **Theorem 1.6** from Proposition 8.1, `ConeEnvironmentScalingStep`, `QuantumConeScalingInput`, Fact 2.2 and the
two open steps of Theorem 2.3 (strict growth, half-ball functional step). -/
theorem convergenceOfDivSandpile_of_coneSteps (𝒮 : SpaceFillingSLEModel) (h81 : IDLAConstrainedConvergenceStmt 𝒮)
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (hgrow : ConeHarmonicBallStrictGrowthStep) (hfun : ConeHalfBallFamilyFunctionalStep) :
    ConvergenceOfDivSandpileStmt 𝒮 :=
  have h := coneScaleInvarianceUpToFixedTime_and_aemeasurable_of_coneSteps hscale h22 hgrow hfun
  convergenceOfDivSandpile_of_scalingInputs 𝒮 h81 hEnv hscale h.1 h.2 hgrow

/-- **Theorem 1.4** from Propositions 4.2, 5.1, 6.1, 7.1 and the inputs of `convergenceOfIDLA_of_coneSteps`. -/
theorem convergenceOfIDLA_of_bounds_coneSteps (𝒮 : SpaceFillingSLEModel) (h42 : DivSandpileLowerBoundStmt 𝒮)
    (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮) (h71 : DivSandpileUpperBoundStmt 𝒮)
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (hgrow : ConeHarmonicBallStrictGrowthStep) (hfun : ConeHalfBallFamilyFunctionalStep) :
    ConvergenceOfIDLAStmt 𝒮 :=
  convergenceOfIDLA_of_coneSteps 𝒮 (iDLAConstrainedConvergence_of_steps 𝒮 h42 h51 h61 h71) hEnv hscale h22 hgrow hfun

/-- **Theorem 1.6** from Propositions 4.2, 5.1, 6.1, 7.1 and the inputs of `convergenceOfDivSandpile_of_coneSteps`. -/
theorem convergenceOfDivSandpile_of_bounds_coneSteps (𝒮 : SpaceFillingSLEModel)
    (h42 : DivSandpileLowerBoundStmt 𝒮) (h51 : IDLALowerBoundStmt 𝒮) (h61 : IDLAUpperBoundStmt 𝒮)
    (h71 : DivSandpileUpperBoundStmt 𝒮) (hEnv : ConeEnvironmentScalingStep 𝒮) (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hfun : ConeHalfBallFamilyFunctionalStep) : ConvergenceOfDivSandpileStmt 𝒮 :=
  convergenceOfDivSandpile_of_coneSteps 𝒮 (iDLAConstrainedConvergence_of_steps 𝒮 h42 h51 h61 h71) hEnv hscale h22
    hgrow hfun

end MatedCRT
