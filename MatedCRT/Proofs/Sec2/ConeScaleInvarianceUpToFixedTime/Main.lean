import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.Obstacle
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.LQGScaling
import MatedCRT.Steps.Sec2.ConeHarmonicBalls

/-!
# Lemma 2.5 from its inputs; the measurability step of Theorem 2.3

* `coneScaleInvarianceUpToFixedTime_of_inputs`: Lemma 2.5 with the deterministic scaling step proved
  (`coneHarmonicBallFamilyOnScalingStep`) and `ConeLQGScalingStep` derived from Fact 2.2 and `R_b > 0`.
* `coneFamilyAEMeasurableStep_of_steps`: worker A's `ConeFamilyAEMeasurableStep` (Theorem 2.3: the families of
  Lemmas 2.4, 2.5 are random variables) follows from the functional step, strict growth and the scaling of the field.
* `coneHarmonicBalls_of_inputs`: Theorem 2.3 from the named steps of Lemmas 2.4 and 2.5.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal

/-- **Lemma 2.5** from its inputs. -/
theorem coneScaleInvarianceUpToFixedTime_of_inputs (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) (hpos : ConeScaleRadiusPosStep) (hgrow : ConeHarmonicBallStrictGrowthStep)
    (hmeasb : ConeRescaledCircleAEMeasurableStep) (hfun : ConeHalfBallFamilyFunctionalStep) :
    ConeScaleInvarianceUpToFixedTimeStmt :=
  coneScaleInvarianceUpToFixedTime_of_steps hscale hgrow (coneLQGScalingStep_of_steps h22 hpos) hmeasb hfun
    coneHarmonicBallFamilyOnScalingStep

/-- **The families of Lemmas 2.4 and 2.5 are random variables** (worker A's `ConeFamilyAEMeasurableStep`, used for
Theorem 2.3): a.s. their family processes are `Φ` of the circle average processes of `h`, resp. `h^b`. -/
theorem coneFamilyAEMeasurableStep_of_steps (hscale : QuantumConeScalingInput)
    (hgrow : ConeHarmonicBallStrictGrowthStep) (hlqg : ConeLQGScalingStep)
    (hmeasb : ConeRescaledCircleAEMeasurableStep) (hfun : ConeHalfBallFamilyFunctionalStep) :
    ConeFamilyAEMeasurableStep := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc μ hcone
  obtain ⟨G, Φ, hGΦ, hchar⟩ := hfun γ hγ0 hγ2
  obtain ⟨-, hΦmeas⟩ := hGΦ Ω P hC hcirc μ hcone
  have hmeasc : AEMeasurable (fun ω => circleProcess (hcirc ω)) P :=
    hcone.2.1.measurable_circleProcess.aemeasurable
  have hgr := hgrow γ hγ0 hγ2 Ω P hC hcirc μ hcone
  refine ⟨fun T Λ hTΛ => ?_, fun b hb Tb Λb hTΛb => ?_⟩
  · refine (hmeasc.prodMk (hΦmeas.comp_aemeasurable hmeasc)).congr ?_
    filter_upwards [hTΛ, hgr, hcone.2.1.ae_continuousOn_circle, hcone.2.2] with ω hω hg hc hl
    exact Prod.ext rfl ((hchar _ hc _ hl).2 _ _ ⟨hω.1, hω.2.1, hω.2.2, hg _ _ hω.2.1⟩).symm
  · have hP : IsProbabilityMeasure P := hcone.1
    have hlaw := hscale γ hγ0 hγ2 Ω P hC hcirc hP hcone.2.1 b hb
    have hmb := hmeasb γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb
    have hΦb : AEMeasurable Φ
        (P.map fun ω => circleProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) := by
      rw [hlaw]
      exact hΦmeas
    refine (hmb.prodMk (hΦb.comp_aemeasurable hmb)).congr ?_
    filter_upwards [hTΛb, hgr, hcone.2.1.ae_continuousOn_circle, hlqg γ hγ0 hγ2 Ω P hC hcirc μ hcone b hb]
      with ω hω hg hc hs
    have hfam := coneHarmonicBallFamilyOnScalingStep (μ ω) (Λb ω) _ b (Tb ω) hs.1 hb hω.2.1
    have hstrict : IsStrictHalfBallFamily (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)
        (rescaledFamily (Λb ω) (coneScaleRadius γ (hcirc ω) b) b) (Tb ω) :=
      ⟨hω.1, hfam, hω.2.2, (hg _ _ hω.2.1).rescaledFamily hb⟩
    exact Prod.ext rfl ((hchar _ (continuousOn_rescaledCircle hc hs.1) _ hs.2).2 _ _ hstrict).symm

/-- **Theorem 2.3** from the named steps of Lemmas 2.4 and 2.5 (through worker A's `coneHarmonicBalls_of_steps`). -/
theorem coneHarmonicBalls_of_inputs (h0 : WholePlaneLogLQGExistenceStep) (h1 : WholePlaneConeHarmonicBallsStep)
    (h2 : WholePlaneHarmonicBallsSmallTimeStep) (h3 : ConeRestrictionStep) (h4 : ConeHarmonicBallLocalityStep)
    (hgrow : ConeHarmonicBallStrictGrowthStep) (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (hpos : ConeScaleRadiusPosStep) (hmeasb : ConeRescaledCircleAEMeasurableStep)
    (hfun : ConeHalfBallFamilyFunctionalStep) : ConeHarmonicBallsStmt :=
  coneHarmonicBalls_of_steps (coneHarmonicBallsUpToFixedTime_of_steps h0 h1 h2 h3 h4 hgrow)
    (coneScaleInvarianceUpToFixedTime_of_inputs hscale h22 hpos hgrow hmeasb hfun)
    (coneFamilyAEMeasurableStep_of_steps hscale hgrow (coneLQGScalingStep_of_steps h22 hpos) hmeasb hfun)

end MatedCRT
