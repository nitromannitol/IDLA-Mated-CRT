import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Null measurability from compact inner approximation

Let `ν` be a finite Borel measure on a Hausdorff space `X` with its Borel σ-algebra. If the outer measure
`ν A` of a set `A` is approximated from inside by compact subsets, `ν A ≤ ν K + ε` with `K ⊆ A` compact, then
`A` is `ν`-null-measurable. This is the measure-theoretic reduction used for the universal measurability of
analytic sets (Lusin; Kechris, *Classical Descriptive Set Theory*, Thm 21.10, through the capacitability of
analytic sets, Thm 30.13). The compact inner approximation is the input; no property of analytic sets is used here.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- A set whose outer measure is approximated from inside by compact subsets is null-measurable for every
finite Borel measure: the compact subsets give a measurable inner set `K` with `ν (A \ K) = 0`. -/
theorem nullMeasurableSet_of_compact_inner (ν : Measure X) [IsFiniteMeasure ν] {A : Set X}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ ν A ≤ ν K + ε) :
    NullMeasurableSet A ν := by
  -- a measurable hull `G ⊇ A` with the same outer measure
  set G : Set X := toMeasurable ν A with hG
  have hGm : MeasurableSet G := measurableSet_toMeasurable ν A
  have hAG : A ⊆ G := subset_toMeasurable ν A
  have hνG : ν G = ν A := measure_toMeasurable A
  -- countably many compact inner approximations, one for each `(n : ℝ≥0∞)⁻¹`
  choose K hKc hKA hKν using fun n : ℕ => h (n : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
  set K' : Set X := ⋃ n, K n with hK'
  have hK'm : MeasurableSet K' :=
    MeasurableSet.iUnion fun n => (hKc n).isClosed.measurableSet
  have hK'A : K' ⊆ A := iUnion_subset fun n => hKA n
  have hK'G : K' ⊆ G := hK'A.trans hAG
  -- `ν A ≤ ν K'` by letting the approximation error go to zero
  have hge : ν A ≤ ν K' := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (ε : ℝ≥0∞) ≠ 0 := by simpa using hε.ne'
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε'
    calc ν A ≤ ν (K n) + (n : ℝ≥0∞)⁻¹ := hKν n
      _ ≤ ν K' + ε := add_le_add (measure_mono (subset_iUnion K n)) hn.le
  -- hence the measurable set `K'` carries all of `A` up to a null set
  have hnull : ν (A \ K') = 0 := by
    have hsub : A \ K' ⊆ G \ K' := sdiff_subset_sdiff_left hAG
    have hfin : ν K' ≠ ∞ := measure_ne_top ν K'
    have hdiff : ν (G \ K') = ν G - ν K' := measure_sdiff hK'G hK'm.nullMeasurableSet hfin
    have hzero : ν (G \ K') = 0 := by
      rw [hdiff, hνG]
      exact tsub_eq_zero_of_le hge
    exact measure_mono_null hsub hzero
  -- `A = K' ∪ (A \ K')` is a union of a measurable set and a null-measurable set
  have hsplit : A = K' ∪ (A \ K') := (union_sdiff_cancel hK'A).symm
  rw [hsplit]
  exact hK'm.nullMeasurableSet.union (NullMeasurableSet.of_null hnull)

#print axioms LatticeProb.nullMeasurableSet_of_compact_inner

end LatticeProb
