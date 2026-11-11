import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapConeAssembly
import MatedCRT.Proofs.Sec4.Prop42Closure.ConeWholePlaneSteps
import MatedCRT.Proofs.Sec4.Prop42Closure.LQGMeasureFunctional

/-!
# Frozen external inputs for the strict obstacle gap (Proposition 4.2 route; Lemmas 5.1, 5.3)

Each `FP...` Prop is an external fact: general whole-plane GFF, LQG measure and Cameron-Martin theory, not specific to arXiv:2211.04891. It is frozen: nothing in this layer proves it.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Metric _root_.HarmonicBalls

/-- Mutual absolute continuity of the laws of the whole-plane pairings (modulo constants) under a smooth test-function shift of the whole-plane GFF: the Cameron-Martin shift used in the strict obstacle gap. Source: Miller-Sheffield, Imaginary Geometry IV, Proposition 2.9 (arXiv:1302.4738v2, p. 49). The source-exact form (RN density, fields modulo `r Z`) has no concrete Lean carrier yet; this is the form stated in `harmonicBallStrictObstacleGapStep_of_restrictedLaw_and_pairingLaws`.
Truth check: TRUE. Miller-Sheffield arXiv:1302.4738v2, p. 49, Proposition 2.9, equation (2.8). -/
def FPPairingLawIG4 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF Q hC hcirc → ∀ (α : ℝ) (g : ℂ → ℝ), IsTestFunction univ g →
      Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ) ≪
          Q.map (localModConstPairings α hC univ) ∧
        Q.map (localModConstPairings α hC univ) ≪
          Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ)

/-- A whole-plane GFF with its `γ`-LQG measure exists, for every `γ ∈ (0,2)`. Source: Duplantier-Sheffield 2011, Proposition 1.1; Berestycki 2017. Locator: Duplantier-Miller-Sheffield, arXiv:1409.7055v4, §4.1.4, with Duplantier-Sheffield, arXiv:0808.1560v2, Proposition 1.1.
Truth check: TRUE. The body is the same proposition as `WholePlaneLogLQGExistence`. -/
def FPWholePlaneLQGModel : Prop := WholePlaneLQGModelStep

/-- Field-level law identity on `B_1` between the quantum cone and a whole-plane GFF with the log singularity. Source: paper eq:gff (line 443, eq. (2.4)); Duplantier-Sheffield 2011. Locator: Duplantier-Miller-Sheffield, arXiv:1409.7055v4, paragraph following Definition 4.10.
Truth check: TRUE. `TestB1` and `CircleB1` contain exactly the admissible local observables. -/
def FPConeWholePlaneFieldLaw : Prop := ConeWholePlaneFieldLawStep

/-- Locality of the `γ`-LQG measure: for each open `U ⊆ B_1`, the mass `μ(U)` is a measurable functional of the restricted field, the same functional for the cone field and for the whole-plane field. Source: Duplantier-Sheffield 2011 (LQG measure as a limit of circle-average approximations). Locator: Duplantier-Sheffield, arXiv:0808.1560v2, Proposition 1.1 with local approximations.
Truth check: TRUE. One deterministic measurable decoder of the local circle coordinates is fixed before either model is chosen. -/
def FPLQGMeasureLocality : Prop := LQGMeasureLocalityFunctionalStep

end MatedCRT
