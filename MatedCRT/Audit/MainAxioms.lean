import MatedCRT.Assembly.Reference

/-!
# Axiom audit of Theorems 1.4 and 1.6 for every model

Each line must print only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms MatedCRT.convergenceOfIDLA_conditional
#print axioms MatedCRT.convergenceOfDivSandpile_conditional
#print axioms MatedCRT.RemainingHypotheses.toMainHypotheses
#print axioms MatedCRT.convergenceOfIDLA_of_remaining
#print axioms MatedCRT.convergenceOfDivSandpile_of_remaining
#print axioms MatedCRT.ConeRestriction.coneRestrictionStep_holds
#print axioms MatedCRT.wholePlaneLogLQGExistenceStep_holds
#print axioms MatedCRT.prestonAnalyticUniversallyMeasurableStmt_holds
#print axioms MatedCRT.ReferenceHypotheses.toRemainingHypotheses
#print axioms MatedCRT.convergenceOfIDLA_of_reference
#print axioms MatedCRT.convergenceOfDivSandpile_of_reference
#print axioms MatedCRT.referenceHypotheses_canonical
#print axioms MatedCRT.mainHypotheses_canonical
