import MatedCRT.FirstPass.Derived.Counted
import MatedCRT.FirstPass.Derived.ZeroConeAreaCoordinateChangeProof
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA4Proof
import MatedCRT.FirstPass.Derived.BG20FrozenWindowLawComparisonProof
import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideInputsProof
import MatedCRT.FirstPass.Derived.GMS21CanonicalTutteLPQuenched
import MatedCRT.FirstPass.Derived.GMS21CanonicalTutteLPQuenchedLiterature
import MatedCRT.FirstPass.Derived.WindowFrontierJordanTransfer
import MatedCRT.FirstPass.Derived.PlanarBMConePoints.Holds
import MatedCRT.FirstPass.Derived.BrownianBeurling.BrownianBeurlingEstimateProof
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.CellSideOfPeanosphere
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ContinuumCover
import MatedCRT.FirstPass.Derived.GFFLocalRegularity.Main
import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceHolds

/-!
# Axiom audit of the derived counted forms

Each line must print only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms MatedCRT.closed_1_4_lp_noSC_noSup_derivedInputs
#print axioms MatedCRT.closed_1_6_lp_noSC_noSup_derivedInputs
#print axioms MatedCRT.closed_2_3_lp_derivedInputs
#print axioms MatedCRT.closed_2_4_lp_derivedInputs
#print axioms MatedCRT.closed_2_5_lp_derivedInputs
#print axioms MatedCRT.closed_2_6_lp_derivedInputs
#print axioms MatedCRT.closed_2_19_ownBinders_derivedInputs
#print axioms MatedCRT.closed_3_3_ownBinders_derivedInputs
#print axioms MatedCRT.closed_3_4_ownBinders_derivedInputs
#print axioms MatedCRT.closed_3_5_lp_derivedInputs
#print axioms MatedCRT.closed_3_6_lp_uniform_derivedInputs
#print axioms MatedCRT.closed_3_7_lp_derivedInputs
#print axioms MatedCRT.closed_4_1_lp_derivedInputs
#print axioms MatedCRT.FirstPassClosure.closed_4_2_lp_derivedInputs
#print axioms MatedCRT.closed_4_7_ownBinders_derivedInputs
#print axioms MatedCRT.closed_4_8_lp_derivedInputs
#print axioms MatedCRT.FirstPassClosure.closed_5_1_lp_noSup_derivedInputs
#print axioms MatedCRT.closed_5_2_ownBinders_derivedInputs
#print axioms MatedCRT.closed_5_3_clean_derivedInputs
#print axioms MatedCRT.closed_6_1_lp_noSup_derivedInputs
#print axioms MatedCRT.closed_6_4_lp_derivedInputs
#print axioms MatedCRT.closed_6_10_lp_derivedInputs
#print axioms MatedCRT.closed_7_1_lp_derivedInputs
#print axioms MatedCRT.closed_8_1_lp_noSup_derivedInputs
#print axioms MatedCRT.firstPass_2_17_ownBinders_derivedInputs
#print axioms MatedCRT.S3c.firstPass_3_1_faithful_derivedInputs
#print axioms MatedCRT.firstPass_4_6_h35c_derivedInputs
#print axioms MatedCRT.FirstPass64.firstPass_6_5_uniform_derivedInputs
#print axioms MatedCRT.LIClosed68Y.firstPass_6_7_derivedInputs
#print axioms MatedCRT.LIClosed68Y.firstPass_6_8_derivedInputs
#print axioms MatedCRT.LIClosed68Y.firstPass_6_9_derivedInputs

-- Proved inputs of the counted forms: the coordinate change of the area measure of the zero cone and Lemma A.4 at
-- uniform roots (Sheffield–Wang, arXiv:1605.06171; Gwynne–Miller–Sheffield, arXiv:1705.11161).
#print axioms MatedCRT.zeroConeAreaCoordinateChange
#print axioms MatedCRT.zeroConeLemmaA4

-- Proved inputs of the counted forms: the frozen window law comparison (Berestycki–Gwynne, arXiv:2003.10320).
#print axioms MatedCRT.bg20FrozenWindowLawComparison

-- Proved inputs of the counted forms: the Brownian inputs of the cell-side identity.
#print axioms MatedCRT.correlatedBMNoCommonLocalMin
#print axioms MatedCRT.validEnvTriplePointsNoContinuum
#print axioms MatedCRT.matingOfTreesCellSideIdentity_of_literature

-- Proved inputs of the counted forms: the premise `tutteLP` from the quenched unit-scale convergence of the zero cone.
#print axioms MatedCRT.tutteLP_canonical_of_theorem310_quenchedZeroCone_edgeCountCode
#print axioms MatedCRT.tutteLP_canonical_of_theorem310_quenchedZeroCone
#print axioms MatedCRT.tutteLP_canonical_of_theorem310_quenchedZeroCone_literature

-- Proved inputs of the counted forms: the Jordan frontier of the windows from one curve per correlated pair.
#print axioms MatedCRT.windowFrontierJordanInput_of_genuineCurve

-- Proved inputs of the counted forms: planar Brownian motion has no two-sided cone points of angle less than `π`
-- (Le Gall, Saint-Flour XX, Chapter III, Theorem 3(i)).
#print axioms MatedCRT.PlanarBMConePoints.noTwoSidedConePoints
#print axioms MatedCRT.planarBMNoTwoSidedConePoints
#print axioms MatedCRT.correlatedBMNoCommonLocalMin_holds
#print axioms MatedCRT.matingOfTreesCellSideIdentity_of_triplePoints

-- Proved inputs of the counted forms: the Beurling estimate for planar Brownian motion (Lawler, Theorem 3.76).
#print axioms MatedCRT.BrownianBeurling.brownianBeurlingEstimate

-- Proved inputs of the counted forms: the cell-side identity from the triple points of Peanosphere curves.
#print axioms MatedCRT.validEnvTriplePointsNoContinuum_of_peanosphere
#print axioms MatedCRT.matingOfTreesCellSideIdentity_of_peanosphere
#print axioms MatedCRT.PeanosphereTriplePoints.not_containsNondegenerateContinuum_of_subset_biUnion

-- A proved input of the coordinate change of the LQG measure: the local negative regularity of the zero-boundary
-- Gaussian free field on a disc (De Nitti–Schweiger, arXiv:2301.13781v4, Proposition 2.1).
#print axioms MatedCRT.GFFLocalRegularity.zeroBoundaryGFFLocalRegularity

-- A proved input of the premise tutteLP: the mutual absolute continuity of the area measures of the quantum cones
-- on a bounded annulus.
#print axioms MatedCRT.coneAnnulusAreaLawEquivalence
