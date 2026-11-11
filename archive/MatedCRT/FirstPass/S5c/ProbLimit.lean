import Mathlib

/-!
# FIRST PASS, Lemma 5.3: from almost-sure eventual absence to vanishing probability (B2 final step)

If the failure events `A k` (here `A k = F ∩ (E ε_k)ᶜ` along the B2 subsequence) are null
measurable, and almost surely each `ω` lies in only finitely many `A k`, then `P (A k) → 0`. Proof: the tails
`D M = ⋃_j A (M + j)` are decreasing with `P(⋂ D M) = 0` (the intersection is contained in the exceptional null set), so
`P(D M) → 0` by continuity from above, and `P (A k) ≤ P (D k)`. The measurability hypothesis is exactly the open
"fixed-mesh failure-event measurability" ; without it, continuity from above of outer measure
is not available.
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Topology Set

/-- **From almost-sure eventual absence to vanishing probability** (B2 final step): see the module docstring. -/
theorem tendsto_measure_zero_of_ae_eventually_not_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (A : ℕ → Set Ω) (hA : ∀ k, NullMeasurableSet (A k) P)
    (h : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ A k) :
    Tendsto (fun k => P (A k)) atTop (𝓝 0) := by
  -- the tails D M = ⋃_j A (M + j)
  let D : ℕ → Set Ω := fun M => ⋃ j : ℕ, A (M + j)
  have hD : ∀ M, NullMeasurableSet (D M) P := fun M => NullMeasurableSet.iUnion fun j => hA (M + j)
  have hanti : Antitone D := by
    intro M M' hMM' ω hω
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMM'
    obtain ⟨j, hj⟩ := mem_iUnion.1 hω
    exact mem_iUnion.2 ⟨d + j, by rw [← add_assoc]; exact hj⟩
  -- the intersection of the tails is null
  have hnull : P (⋂ M, D M) = 0 := by
    have hexc : ∀ᵐ ω ∂P, ω ∉ ⋂ M, D M := by
      filter_upwards [h] with ω hω hint
      obtain ⟨M, hM⟩ := eventually_atTop.1 hω
      obtain ⟨j, hj⟩ := mem_iUnion.1 (mem_iInter.1 hint M)
      exact hM (M + j) (Nat.le_add_right M j) hj
    have hsub : (⋂ M, D M) ⊆ {ω | ¬ ω ∉ ⋂ M, D M} := fun ω hω hn => hn hω
    exact measure_mono_null hsub (ae_iff.1 hexc)
  -- continuity from above along the tails
  have hfin : ∃ i, P (D i) ≠ ⊤ := ⟨0, measure_ne_top P _⟩
  have htail := tendsto_measure_iInter_atTop hD hanti hfin
  rw [hnull] at htail
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun k => zero_le) (fun k => measure_mono fun ω hω => ?_)
  exact mem_iUnion.2 ⟨0, by simpa using hω⟩

end MatedCRT.S5c
