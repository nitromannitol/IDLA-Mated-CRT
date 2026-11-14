import MatedCRT.FirstPass.Derived.MatingTriplePointsCone
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Cone triple points and pairs of times

A cone triple point is the apex or one of its two direct partners. Recording the
apex and either partner as a pair allows Hausdorff-dimension bounds for the pair
set to be transferred to all three times by coordinate projection.
-/

set_option autoImplicit false

open Set
open MatedCRTHarmonic.MatedCRT (DirectRel lrCoord Path2)
open scoped ENNReal

namespace MatedCRT

/-- Pairs consisting of a cone apex and one of its two distinct direct partners. -/
def coneTriplePairs (b : Path2) : Set (ℝ × ℝ) :=
  {p | ∃ t₁ t₂, t₁ ≠ t₂ ∧
    ((DirectRel (fun u => lrCoord 0 u b) p.1 t₁ ∧
      DirectRel (fun u => lrCoord 1 u b) p.1 t₂) ∨
     (DirectRel (fun u => lrCoord 0 u b) t₁ p.1 ∧
      DirectRel (fun u => lrCoord 1 u b) t₂ p.1)) ∧
    (p.2 = t₁ ∨ p.2 = t₂)}

/-- The apex and both partners are precisely the coordinate projections of the pair set. -/
theorem coneTriplePoints_eq_image_coneTriplePairs (b : Path2) :
    coneTriplePoints b = Prod.fst '' coneTriplePairs b ∪ Prod.snd '' coneTriplePairs b := by
  ext x
  constructor
  · rintro ⟨s, t₁, t₂, hne, hrel, hx | hx | hx⟩
    · left
      exact ⟨(s, t₁), ⟨t₁, t₂, hne, hrel, Or.inl rfl⟩, hx.symm⟩
    · right
      exact ⟨(s, t₁), ⟨t₁, t₂, hne, hrel, Or.inl rfl⟩, hx.symm⟩
    · right
      exact ⟨(s, t₂), ⟨t₁, t₂, hne, hrel, Or.inr rfl⟩, hx.symm⟩
  · rintro (⟨⟨s, t⟩, ⟨t₁, t₂, hne, hrel, ht⟩, rfl⟩ |
      ⟨⟨s, t⟩, ⟨t₁, t₂, hne, hrel, ht⟩, rfl⟩)
    · exact ⟨s, t₁, t₂, hne, hrel, Or.inl rfl⟩
    · exact ⟨s, t₁, t₂, hne, hrel, Or.inr ht⟩

/-- A dimension bound for the pair set bounds the cone triple points. -/
theorem dimH_coneTriplePoints_le_of_pairs (b : Path2) {d : ℝ≥0∞}
    (h : dimH (coneTriplePairs b) ≤ d) : dimH (coneTriplePoints b) ≤ d := by
  rw [coneTriplePoints_eq_image_coneTriplePairs, dimH_union]
  exact max_le ((LipschitzWith.prod_fst.dimH_image_le _).trans h)
    ((LipschitzWith.prod_snd.dimH_image_le _).trans h)

end MatedCRT
