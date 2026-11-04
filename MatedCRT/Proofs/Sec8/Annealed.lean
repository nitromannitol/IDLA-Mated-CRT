import MatedCRT.Defs.Setting

/-!
# Union bounds for the annealed outer probability

The annealed outer probability `annealedOuterProb P κ E` (review-S (S5), MatedCRT/Defs/Notation.lean) is the outer
integral of the quenched probability `ω ↦ κ ω (E_ω)`. This file proves the two bounds used to combine the lower and
upper bounds of Section 8 and to transfer events between two environments in the proof of Theorems 1.4 and 1.6:

* `annealedOuterProb_le_add_of_subset_union`: subadditivity, `P*(E) ≤ P*(E₁) + P*(E₂)` for `E ⊆ E₁ ∪ E₂`;
* `annealedOuterProb_le_of_forall_not_mem`: if off a set `B` of environments the quenched probability of `E` under `κ`
  is at most that of `E'` under `κ'`, then `P*_κ(E) ≤ P*_{κ'}(E') + P(B)` (outer measure of `B`).
-/

namespace MatedCRT

namespace Sec8

open MeasureTheory Set
open scoped ENNReal

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- **Subadditivity of the annealed outer probability**: if `E ⊆ E₁ ∪ E₂` then `P*(E) ≤ P*(E₁) + P*(E₂)`. -/
theorem annealedOuterProb_le_add_of_subset_union (P : Measure Ω) (κ : Ω → Measure X) {E E₁ E₂ : Set (Ω × X)}
    (hE : E ⊆ E₁ ∪ E₂) :
    annealedOuterProb P κ E ≤ annealedOuterProb P κ E₁ + annealedOuterProb P κ E₂ := by
  unfold annealedOuterProb outerLIntegral
  rw [ENNReal.iInf_add]
  refine le_iInf fun g₁ => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hg₁ => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hfg₁ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun g₂ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hg₂ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hfg₂ => ?_
  refine iInf_le_of_le (g₁ + g₂) (iInf_le_of_le (hg₁.add hg₂) (iInf_le_of_le ?_ ?_))
  · intro ω
    calc κ ω (Prod.mk ω ⁻¹' E) ≤ κ ω (Prod.mk ω ⁻¹' E₁ ∪ Prod.mk ω ⁻¹' E₂) := by
          rw [← preimage_union]
          exact measure_mono (preimage_mono hE)
      _ ≤ κ ω (Prod.mk ω ⁻¹' E₁) + κ ω (Prod.mk ω ⁻¹' E₂) := measure_union_le _ _
      _ ≤ g₁ ω + g₂ ω := add_le_add (hfg₁ ω) (hfg₂ ω)
  · show ∫⁻ ω, g₁ ω + g₂ ω ∂P ≤ _
    rw [lintegral_add_left hg₁]

/-- **Transfer of an annealed event off a bad set of environments**: if for every environment `ω ∉ B` the quenched
probability of `E` under `κ ω` is at most that of `E'` under `κ' ω`, and the quenched laws `κ ω` are sub-probability
measures, then `P*_κ(E) ≤ P*_{κ'}(E') + P(B)`. -/
theorem annealedOuterProb_le_of_forall_not_mem (P : Measure Ω) (κ κ' : Ω → Measure X)
    (hκ : ∀ ω, κ ω univ ≤ 1) (E E' : Set (Ω × X)) (B : Set Ω)
    (h : ∀ ω, ω ∉ B → κ ω (Prod.mk ω ⁻¹' E) ≤ κ' ω (Prod.mk ω ⁻¹' E')) :
    annealedOuterProb P κ E ≤ annealedOuterProb P κ' E' + P B := by
  unfold annealedOuterProb outerLIntegral
  set g₂ : Ω → ℝ≥0∞ := (toMeasurable P B).indicator 1 with hg₂
  have hg₂m : Measurable g₂ := measurable_one.indicator (measurableSet_toMeasurable P B)
  have hg₂i : ∫⁻ ω, g₂ ω ∂P = P B := by
    rw [hg₂, lintegral_indicator_one (measurableSet_toMeasurable P B), measure_toMeasurable]
  rw [ENNReal.iInf_add]
  refine le_iInf fun g => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hg => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hfg => ?_
  refine iInf_le_of_le (g + g₂) (iInf_le_of_le (hg.add hg₂m) (iInf_le_of_le ?_ ?_))
  · intro ω
    by_cases hω : ω ∈ B
    · have : g₂ ω = 1 := by
        rw [hg₂, indicator_of_mem (subset_toMeasurable P B hω), Pi.one_apply]
      calc κ ω (Prod.mk ω ⁻¹' E) ≤ κ ω univ := measure_mono (subset_univ _)
        _ ≤ 1 := hκ ω
        _ ≤ g ω + g₂ ω := by rw [this]; exact le_add_self
    · exact (h ω hω).trans ((hfg ω).trans le_self_add)
  · show ∫⁻ ω, g ω + g₂ ω ∂P ≤ _
    rw [lintegral_add_left hg, hg₂i]

/-- The annealed outer probability is monotone in the event. -/
theorem annealedOuterProb_mono (P : Measure Ω) (κ : Ω → Measure X) {E E' : Set (Ω × X)} (hE : E ⊆ E') :
    annealedOuterProb P κ E ≤ annealedOuterProb P κ E' := by
  unfold annealedOuterProb outerLIntegral
  refine le_iInf fun g => le_iInf fun hg => le_iInf fun hfg => iInf_le_of_le g (iInf_le_of_le hg
    (iInf_le_of_le (fun ω => (measure_mono (preimage_mono hE)).trans (hfg ω)) le_rfl))

end Sec8

end MatedCRT
