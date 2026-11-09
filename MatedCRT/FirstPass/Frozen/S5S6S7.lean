import MatedCRT.Steps.Sec6.AnnulusHit
import MatedCRT.Steps.Sec6.GoodAnnulusPrevalence

/-!
# FIRST PASS frozen external inputs for Sections 5-7 of arXiv:2211.04891 (corrected draft)

Each `FP...` Prop is an EXTERNAL fact (general LQG / whole-plane field theory, not specific to this paper). It is
frozen: no theorem in this layer proves it. Its statement is the Step Prop of the same content in `MatedCRT/Steps/`,
used unchanged. Locators: see each docstring.
-/

namespace MatedCRT

/-- FIRST-PASS FROZEN. A whole-plane GFF with its `γ`-LQG measure exists, for every `γ ∈ (0,2)`.
Source: Sheffield 2007, Section 2; Duplantier-Sheffield 2011, Proposition 1.1; INPUT-REQUESTS IR-c4-1; standard; locator pending.
Used by: firstPass_6_4, firstPass_6_5, firstPass_6_10. -/
def FPWholePlaneLQGExistence : Prop := WholePlaneLQGExistenceStep

/-- FIRST-PASS FROZEN. Comparison of the cone field near an admissible annulus with the whole-plane field carrying
the density `|x|^{-γ²}` (Weyl scaling): the law of the good-annulus event is the same under the two fields.
Source: paper line 2348-2355 (Lemma 6.5, Step 1); Duplantier-Sheffield 2011, Proposition 1.2; IR-c4-2; standard; locator pending.
Used by: firstPass_6_4, firstPass_6_5, firstPass_6_10. -/
def FPConeWholePlaneWeylComparison : Prop := ConeWholePlaneWeylComparisonStep

/-- FIRST-PASS FROZEN. Scale and translation invariance of the whole-plane LQG measure modulo constants (eq:gff-scaling,
the LQG coordinate change formula, Weyl scaling by constants). Source: paper line 2367 (Lemma 6.5, Step 2);
Duplantier-Sheffield 2011, Propositions 1.2 and 2.1; IR-c4-3; standard; locator pending.
Used by: firstPass_6_4, firstPass_6_5, firstPass_6_10. -/
def FPWholePlaneLQGCoordinateChange : Prop := WholePlaneLQGCoordinateChangeStep

/-- FIRST-PASS FROZEN. Uniform upper volume bound for the whole-plane LQG measure, `μ(B_s(z)) ≤ s^β` for all `z ∈ B_3`,
with probability `1 - O(s^q)`. Source: Rhodes-Vargas 2014, Theorem 2.6; Baverez-Gwynne/BG20 arXiv:2003.10320, eq. (A.2);
IR-c4-4; standard; locator pending. Used by: firstPass_6_4, firstPass_6_5, firstPass_6_10. -/
def FPWholePlaneUpperVolumeTail : Prop := WholePlaneUpperVolumeTailStep

/-- FIRST-PASS FROZEN. Restriction of eq:gff to mean-zero pairings on circles (the input of IR-c4-5 in the cone-field
transfer of Lemma 6.6). Source: paper eq:gff, line 444; IR-c4-5; standard; locator pending.
Used by: firstPass_6_4, firstPass_6_10. -/
def FPConeMeanZeroRestriction : Prop := ConeMeanZeroRestrictionStep

end MatedCRT
