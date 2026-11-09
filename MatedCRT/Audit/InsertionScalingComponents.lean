import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionScalingLawAssembly

/-! # Audit of the components assembly of Input K (`InsertionScalingLawAssembly.lean`)

Task `z1-steps3-insertion-scaling-consumer-assembly`. Audit only. It contains an exact-type check against the existing Step
`InsertionLQGScalingLawStep` (`PlateauScaleLaw.lean:106`), the signatures of the exports, and the axioms of the main exports.
It proves no Step and adds no premise. The conditional export has exactly two hypotheses: the Sheffield-Wang compact-interior
input `SheffieldWangCircleAverageAllScaleInteriorStmt.{0}` and the local Dirichlet/harmonic decomposition
`LocalDirichletHarmonicDecompositionStep`. -/

namespace MatedCRT

/-- Exact-type check: the export has the existing Step as its conclusion, from exactly the two named inputs. -/
theorem check_insertionLQGScalingLawStep_of_components :
    SheffieldWangCircleAverageAllScaleInteriorStmt.{0} → LocalDirichletHarmonicDecompositionStep →
      InsertionLQGScalingLawStep :=
  insertionLQGScalingLawStep_of_components

#check @insertionLQGScalingLawStep_of_components
#check @insertionLQGScalingLaw_fixed_a_of_components

#print axioms MatedCRT.insertionCoordinateExtensionStep_of_components
#print axioms MatedCRT.insertionLQGScalingLawStep_of_coordinateRule
#print axioms MatedCRT.insertionLQGScalingLawStep_of_components
#print axioms MatedCRT.insertionLQGScalingLaw_fixed_a_of_components

end MatedCRT
