import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalence
import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceLateral
import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceInner
import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceOuter
import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceLocal

/-!
# The laws of the area measures of the two quantum cones on a bounded annulus are equivalent

`ConeAnnulusAreaLawEquivalence γ` (`GMS21Lemma33Cone.lean`) holds: for `0 < γ < 2`, a whole-plane GFF and Brownian
motions with the independence structure of the cone data, and a curve independent of them, the laws of the outer data
`(e, μ|{δ < |z| < M})` of the `γ`-quantum cone and of the `0`-quantum cone are mutually absolutely continuous for
every `0 < δ < M`. This is `coneAnnulusAreaLawEquivalence_of_steps` with the four steps proved:
the locality of the area measure (`coneAnnulusLocality`), the inner radial paths (`coneInnerPathLaw`, with
`brownianPathAEMeasurable`), the outer radial windows (`coneOuterWindowLaw`, `coneOuterWindowMeasurable`) and the
law of the lateral part (`lateralPartLaw`).

Source: the answer to MQ-sbl-18, section "The field laws on a bounded annulus"; Gwynne–Miller–Sheffield
(arXiv:1705.11161), §2.3.1, and the local absolute continuity used in the proof of Theorem 3.4, case 1;
Duplantier–Miller–Sheffield (arXiv:1409.7055), Definition 4.10.
-/

open MeasureTheory ProbabilityTheory Set

namespace MatedCRT

/-- **The laws of the area measures of the `γ`-quantum cone and the `0`-quantum cone on a bounded annulus are
mutually absolutely continuous, jointly with an independent curve** (premise `h1` of
`tutteLP_canonical_of_theorem310_quenchedZeroCone`). -/
theorem coneAnnulusAreaLawEquivalence (γ : ℝ) : ConeAnnulusAreaLawEquivalence γ := by
  intro Ω _ P _ X X₀ B B' B₀ B₀' e hγ
  exact coneAnnulusAreaLawEquivalence_of_steps brownianPathAEMeasurable
    (fun δ M hδ hδM => coneAnnulusLocality hγ hδ hδM) coneInnerPathLaw coneOuterWindowLaw
    coneOuterWindowMeasurable lateralPartLaw P X X₀ B B' B₀ B₀' e hγ

end MatedCRT
