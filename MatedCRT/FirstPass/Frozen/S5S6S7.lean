import MatedCRT.Steps.Sec6.AnnulusHit
import MatedCRT.Steps.Sec6.GoodAnnulusPrevalence

/-!
# Frozen external inputs for Sections 5-7 of arXiv:2211.04891

Each `FP...` Prop is an external fact (general LQG and whole-plane field theory, not specific to this paper). It is frozen: no theorem in this layer proves it. Locators: see each docstring. One Prop is retired (proved): `FPConeWholePlaneWeylComparison`.
-/

namespace MatedCRT

/-- A whole-plane GFF with its `γ`-LQG measure exists, for every `γ ∈ (0,2)`. Source: Sheffield 2007, Section 2; Duplantier-Sheffield 2011, Proposition 1.1; standard; locator not yet pinned. -/
def FPWholePlaneLQGExistence : Prop := WholePlaneLQGExistenceStep

/-- Retired: proved. The comparison of the cone field near an admissible annulus with the whole-plane field carrying the density `|x|^{-γ²}` (Weyl scaling; the law of the good-annulus event is the same under the two fields; paper lines 2348-2355, Lemma 6.5 Step 1; Duplantier-Sheffield 2011, Proposition 1.2). It is now the proved theorem `MatedCRT.AnnulusHitField.coneWholePlaneWeylComparison` (`Proofs/Sec6/AnnulusHit/FieldWeylComparison.lean:442`, axioms audited in `FirstPass/S4S5b/AxiomsWeyl.lean`). No theorem uses this Prop any more; its name is retained so that existing references still resolve. -/
def FPConeWholePlaneWeylComparison : Prop := ConeWholePlaneWeylComparisonStep

/-- Scale and translation invariance of the whole-plane LQG measure modulo constants (eq:gff-scaling, the LQG coordinate change formula, Weyl scaling by constants). Source: paper line 2367 (Lemma 6.5, Step 2); Duplantier-Sheffield 2011, Propositions 1.2 and 2.1; standard; locator not yet pinned. -/
def FPWholePlaneLQGCoordinateChange : Prop := WholePlaneLQGCoordinateChangeStep

/-- Uniform upper volume bound for the whole-plane LQG measure, `μ(B_s(z)) ≤ s^β` for all `z ∈ B_3`, with probability `1 - O(s^q)`. Source: Rhodes-Vargas 2014, Theorem 2.6; Baverez-Gwynne / BG20 arXiv:2003.10320, eq. (A.2); standard; locator not yet pinned.
Truth check: TRUE. The GFF normalization is fixed, and the constants are existential after the model. -/
def FPWholePlaneUpperVolumeTail : Prop := WholePlaneUpperVolumeTailStep

/-- Restriction of eq:gff to mean-zero pairings on circles (the input of the cone-field transfer of Lemma 6.6). Source: paper eq:gff, line 444; standard; locator not yet pinned.
Truth check: TRUE. The admissible local test subtype is explicit.
Discharged: `MatedCRT.ConeMeanZeroRestriction.fpConeMeanZeroRestriction_of_radialLateralIndep` (`MatedCRT/FirstPass/LPBridge/ConeMeanZeroRestrictionFinal.lean:136`) applied to `MatedCRT.ConeMeanZeroRestriction.gffRadialLateralIndep_holds` (`MatedCRT/FirstPass/LPBridge/GFFRadialLateralIndep.lean:1029`) proves it. -/
def FPConeMeanZeroRestriction : Prop := ConeMeanZeroRestrictionStep

end MatedCRT
