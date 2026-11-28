import MatedCRT.Assembly.Canonical
import MatedCRT.FirstPass.Derived.CanonicalCountedFormsChartSteps
import MatedCRT.Assembly.CanonicalWrappers
import MatedCRT.FirstPass.Derived.CanonicalCountedFormsBrownianInputs

/-!
# Axiom audit of Theorems 1.4 and 1.6 at the canonical model

Each line must print only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms MatedCRT.convergenceOfIDLA_canonical
#print axioms MatedCRT.convergenceOfDivSandpile_canonical
#print axioms MatedCRT.FirstPass.Derived.closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField
#print axioms MatedCRT.FirstPass.Derived.closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartField
#print axioms MatedCRT.FirstPass.Derived.bg20ChartFieldInput_canonical_of_chartSteps
#print axioms MatedCRT.FirstPass.Derived.closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartSteps
#print axioms MatedCRT.FirstPass.Derived.closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_chartSteps

-- Lemmas 5.4, 7.2 (corrected, above the scale) and 7.4 at the canonical model.
#print axioms MatedCRT.lLowerBound_canonical
#print axioms MatedCRT.massBoundOdometerAboveScale_canonical
#print axioms MatedCRT.crudeUpperBound_canonical

-- Theorems 1.4 and 1.6 at the canonical model with the window geometry, the cone points and the Beurling estimate
-- proved.
#print axioms MatedCRT.FirstPass.Derived.closed_1_4_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_genuineCurve
#print axioms MatedCRT.FirstPass.Derived.closed_1_6_quantumConeScaling_coneDimension_canonical_of_coupling_tutteLP_genuineCurve
