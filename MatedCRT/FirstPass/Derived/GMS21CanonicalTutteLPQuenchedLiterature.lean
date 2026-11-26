import MatedCRT.FirstPass.Derived.GMS21CanonicalTutteLPQuenched
import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideInputsProof

/-!
# The premise `tutteLP` at the canonical model from Theorem 3.10, with the Brownian inputs from the literature

The counted form `tutteLP_canonical_of_theorem310_quenchedZeroCone` (`GMS21CanonicalTutteLPQuenched.lean`) takes the
two inputs on correlated Brownian motion of the code of the edge counts as premises:

* `CorrelatedBMNoCommonLocalMin`: a correlated two-sided Brownian pair almost surely has no time which is a local
  minimum of both coordinates. It follows from Le Gall's theorem that planar Brownian motion has no two-sided cone
  points of angle less than `π` (`correlatedBMNoCommonLocalMin` from `PlanarBMNoTwoSidedConePoints`).
* `CorrelatedBMPeanosphereTriplePointsNoContinuum`: for almost every correlated Brownian pair, the points visited three
  times by any Peanosphere curve of the pair contain no continuum of positive diameter. It follows from the same
  property of the space-filling SLE traversal attached to almost every pair, since two Peanosphere curves of the same
  pair differ by a homeomorphism of the plane (`ae_forall_peanosphere_not_containsNondegenerateContinuum` from
  `CorrelatedBMTraversalTriplePointsNoContinuum`; Duplantier–Miller–Sheffield, arXiv:1409.7055, Theorem 1.9 and
  Lemmas 8.8-8.15; Gwynne–Holden–Miller–Sun, arXiv:1510.04687, Theorem 1.1; Gwynne–Holden–Miller, arXiv:1512.01223,
  Corollary 6.5).

## Main statements

* `tutteLP_canonical_of_theorem310_quenchedZeroCone_literature`: the premise `tutteLP` at the canonical model from the
  couplings, Theorem 3.10 of arXiv:1807.07515, the polygonal cell configuration, the two statements of the literature
  above and the first and third inputs of Lemma 3.3.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric Filter Topology HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b GMS310Transfer

/-- **The premise `tutteLP` at the canonical model from Theorem 3.10 and the quenched unit-scale convergence, with
the Brownian inputs from the literature** (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Theorem 3.4, case 1,
and proof of Lemma 3.5). If the couplings with code law `ν (16/γ²)` exist, Theorem 3.10 of arXiv:1807.07515 holds,
every mating-of-trees coupling on `ℝ` has a polygonal cell configuration carrying the walk of its zero-cone cells,
planar Brownian motion has no two-sided cone points of angle less than `π` (`PlanarBMNoTwoSidedConePoints`, Le Gall),
almost every correlated Brownian pair carries a space-filling SLE traversal whose triple points contain no continuum
(`CorrelatedBMTraversalTriplePointsNoContinuum`), and the first and third inputs of Lemma 3.3 hold for every
`γ ∈ (0, 2)`, then for every `γ ∈ (0, 2)` the canonical model has a valid environment whose walk and Brownian motion
stopped at their exits from `B_R(0)` are close in Lévy–Prokhorov distance from every selected start with probability
tending to one. -/
theorem tutteLP_canonical_of_theorem310_quenchedZeroCone_literature (ν : ℝ → Measure SLEPathCode)
    (hcpl : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∃ (P : Measure ℝ) (X X₀ hIG₀ : ℝ → Field) (B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ) (U : ℝ → ℝ)
        (ηL η η₀ : ℝ → C(ℝ, ℂ)) (bm : ℝ → Path2),
        IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm ∧
        P.map (fun ω => slePathCode (ηL ω)) = ν (16 / γ ^ 2))
    (h310 : GMSTheorem310)
    (hpoly : ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) {P : Measure ℝ} {X X₀ hIG₀ : ℝ → Field}
      {B B' B₀ B₀' : ℝ≥0 → ℝ → ℝ} {U : ℝ → ℝ} {ηL η η₀ : ℝ → C(ℝ, ℂ)} {bm : ℝ → Path2}
      (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm), ZeroConePolygonalConfiguration D hγ)
    (hLG : PlanarBMNoTwoSidedConePoints) (hA : CorrelatedBMTraversalTriplePointsNoContinuum)
    (h1 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeAnnulusAreaLawEquivalence γ)
    (h3 : ∀ γ ∈ Ioo (0 : ℝ) 2, ConeConfigReconstruction γ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ :=
  tutteLP_canonical_of_theorem310_quenchedZeroCone ν hcpl h310 hpoly (correlatedBMNoCommonLocalMin hLG)
    (fun _ hγ0 hγ2 _ hμ => ae_forall_peanosphere_not_containsNondegenerateContinuum hA hγ0 hγ2 hμ) h1 h3

end MatedCRT
