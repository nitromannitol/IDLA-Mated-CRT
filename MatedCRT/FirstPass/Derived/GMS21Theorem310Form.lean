import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement
import LatticeProb.Topology.TranslatedCurveLawContinuity
import LatticeProb.Walk.CellConfigVisitPathLaw

/-!
# Gwynne–Miller–Sheffield, Theorem 3.10: the uniform-start invariance principle, as a statement

Source: E. Gwynne, J. Miller, S. Sheffield, *An invariance principle for ergodic scale-free random environments*,
arXiv:1807.07515, Theorem 3.10 (Section 3.3, "Convergence is uniform in the starting point"). For `z ∈ ℂ` let `Y^z` be
the simple random walk on the cell configuration `H` started from a cell `H_z` containing `z`; let `Ŷ^z_j` be a chosen
point of the cell `Y^z_j`, extended to `[0, ∞)` by piecewise linear interpolation; let `Σ` be the covariance matrix of
Theorem 1.16. For each fixed compact set `A ⊂ ℂ`, almost surely, as `ε → 0`, the maximum over `z ∈ A` of the Prokhorov
distance between the conditional law of `ε Ŷ^{z/ε}` given `H` and the law of Brownian motion with covariance `Σ`
started from `z`, for the topology on curves modulo time parametrization of (1.8), tends to `0`.

The definitions and the statement below are copied verbatim from the Lattice-Probability file
`LatticeProb/Bonanno/ReflectedGMS/GMS/Theorem310Statement.lean` (commit e21c68da), which is not part of the
Lattice-Probability version this repository depends on (its imports are). The copies live in the namespace
`MatedCRT.GMS310`; `CellConfig.scaledStepPath` and `CellConfig.walkCurveLaw` there become `GMS310.scaledStepPath` and
`GMS310.walkCurveLaw` with the cell configuration as explicit first argument.

## Encoding (as in the source file)

* Curves modulo time parametrization: `UnboundedRayCurveSpace 2`, continuous paths with unbounded range modulo zero
  distance for the local curve distance of (1.8), with its Borel σ-algebra.
* The law modulo time parametrization of a law `μ` on continuous paths, `unboundedCurveLaw μ`, is the restriction of `μ`
  to the paths with unbounded range, projected to curve classes.
* The walk `Y^z` is given by the law `Q` of its jump chain (`IsSRWLaw`, as in Theorem 1.16), and `ε Ŷ` is the path
  through the points `ε p(Y_j)` at the integer times `j`, linearly interpolated (`scaledStepPath`).
* `H_z` is any cell containing `z`; the point `p K ∈ K` is arbitrary and fixed before `A` and `ε`.
* `Σ` is the covariance of Theorem 1.16: the statement repeats the convergence of Theorem 1.16 for the same `target`.

## Main definitions

* `GMSTheorem310Form μ`: the conclusion of Theorem 3.10 for a configuration law `μ`.
* `GMSTheorem310`: Theorem 3.10 (every law satisfying the hypotheses of Theorem 1.16 satisfies the conclusion).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace MatedCRT

noncomputable section

local instance : MeasurableSpace (LatticeProb.UnboundedRayCurveSpace 2) := borel _

namespace GMS310

open ReflectedGMS.GMS ReflectedGMS.StatementIngredients
open LatticeProb.UnboundedRayIntervalIntegrand LatticeProb.UnboundedRayCurveSpace

/-- The law modulo time parametrization of a law `μ` on continuous planar paths: the restriction of
`μ` to the paths with unbounded range, projected to their classes in `UnboundedRayCurveSpace 2`. -/
def unboundedCurveLaw (μ : Measure (LatticeProb.UnboundedRayIntervalIntegrand.Path 2)) :
    Measure (LatticeProb.UnboundedRayCurveSpace 2) :=
  (μ.comap (Subtype.val : UnboundedRay 2 → LatticeProb.UnboundedRayIntervalIntegrand.Path 2)).map project

/-- `ε Ŷ`: the path through the points `ε p(ω j)` at the integer times `j`, linearly interpolated
(GMS, Theorem 3.10). -/
def scaledStepPath (H : ReflectedGMS.GMS.CellConfig) (p : H.cells → ReflectedGMS.Plane) (ε : ℝ)
    (ω : ℕ → H.cells) : LatticeProb.UnboundedRayIntervalIntegrand.Path 2 :=
  LatticeProb.ConstantStepInterpolation.continuousPlanePath 1 (fun n => ε • p (ω n))

/-- The law modulo time parametrization of `ε Ŷ` when the jump chain has law `Q`. -/
def walkCurveLaw (H : ReflectedGMS.GMS.CellConfig) (p : H.cells → ReflectedGMS.Plane) (ε : ℝ)
    (Q : Measure (ℕ → H.cells)) : Measure (LatticeProb.UnboundedRayCurveSpace 2) :=
  unboundedCurveLaw (Q.map (scaledStepPath H p ε))

/-- The law modulo time parametrization of Brownian motion with the covariance of `target`, started
from `z`: the local curve law of the translated Brownian path law. -/
def brownianCurveLaw (target : AnisotropicBrownianTarget) (z : ReflectedGMS.Plane) :
    Measure (LatticeProb.UnboundedRayCurveSpace 2) :=
  translatedCurveProbability (target.pathLaw : Measure (LatticeProb.UnboundedRayIntervalIntegrand.Path 2))
    (ae_unbounded_range_anisotropicBrownian target) z

end GMS310

open ReflectedGMS.GMS ReflectedGMS.StatementIngredients

/-- **The conclusion of Gwynne–Miller–Sheffield, Theorem 3.10, for a configuration law `μ`** (the body of
`Theorem3_10` of the source file after its hypotheses): there is a Brownian covariance (`target`) such that `μ`-almost
surely the walk converges to Brownian motion with this covariance (Theorem 1.16), and `μ`-almost surely, for every
choice of points `p K ∈ K`, every compact set `A` and every `δ > 0`, for all small `ε > 0`, for every `z ∈ A`, every
cell `K` containing `z / ε` and every law `Q` of the simple random walk started from `K`, the Lévy–Prokhorov distance
between the law of `ε Ŷ` modulo time parametrization and the law of Brownian motion with covariance `Σ` started from
`z` modulo time parametrization is less than `δ`.

This declaration states a proposition; it does not assert that it has been proved. -/
def GMSTheorem310Form (μ : Measure GMSSpace) : Prop :=
  ∃ target : AnisotropicBrownianTarget,
    (∀ᵐ H ∂μ, ∀ (K₀ : H.1.cells) (Q : Measure (ℕ → H.1.cells)), H.1.IsSRWLaw K₀ Q →
      ∀ p : H.1.cells → ReflectedGMS.Plane,
        (∀ K : H.1.cells, p K ∈ ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane)) →
        ConvergesWeaklyInC Q (H.1.interpolatedWalk p) target) ∧
    ∀ᵐ H ∂μ, ∀ p : H.1.cells → ReflectedGMS.Plane,
      (∀ K : H.1.cells, p K ∈ ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane)) →
      ∀ A : Set ReflectedGMS.Plane, IsCompact A → ∀ δ : ℝ, 0 < δ →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∀ z ∈ A, ∀ K : H.1.cells, ε⁻¹ • z ∈ ((K : ReflectedGMS.GMS.Cell) : Set ReflectedGMS.Plane) →
            ∀ Q : Measure (ℕ → H.1.cells), H.1.IsSRWLaw K Q →
              levyProkhorovEDist (GMS310.walkCurveLaw H.1 p ε Q) (GMS310.brownianCurveLaw target z) <
                ENNReal.ofReal δ

/-- **Gwynne–Miller–Sheffield, Theorem 3.10** (arXiv:1807.07515): every probability law on the GMS space satisfying the
hypotheses of Theorem 1.16 (mass transport, ergodicity modulo scaling, finite expectation, connectedness along lines)
satisfies the conclusion `GMSTheorem310Form`. This is `Theorem3_10` of the source file.

This declaration states a proposition; it does not assert that it has been proved. -/
def GMSTheorem310 : Prop :=
  ∀ (μ : Measure GMSSpace) [IsProbabilityMeasure μ],
    MassTransport μ → ErgodicModuloScaling μ → FiniteExpectation μ → ConnectedAlongLines μ →
      GMSTheorem310Form μ

end

end MatedCRT
