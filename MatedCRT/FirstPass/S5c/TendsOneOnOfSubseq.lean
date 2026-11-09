import MatedCRT.Defs.Notation
import MatedCRT.FirstPass.S5c.ProbLimit
import MatedCRT.FirstPass.S5c.SubseqCriterion

/-!
# FIRST PASS, Lemma 5.3 and E-c1-5: `TendsToOneOn` from subsequential almost-sure goodness (B2 assembly, pure probability)

The B2 argument (CHATGPT-5-1-B2-Ec15.md §1) proves, along any mesh sequence `x_n ↓ 0`, a subsequence `φ` such that almost
surely on the event `F`, the good event `E (x (φ k))` holds for all large `k`; the failure events `F ∩ (E ε)ᶜ` are assumed
null measurable (the open fixed-mesh measurability of the failure events). Then the outer-measure failure probability
`P[F ∩ (E ε)ᶜ]` tends to zero as `ε ↓ 0`, i.e. `TendsToOneOn P F E` (Defs/Notation.lean:40). This is the generic
composition of ProbLimit.lean and SubseqCriterion.lean.
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Topology Set

/-- **`TendsToOneOn` from subsequential almost-sure goodness** (B2 assembly): see the module docstring. -/
theorem tendsToOneOn_of_subseq_ae_eventually_good {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : Set Ω) (E : ℝ → Set Ω)
    (hmeas : ∀ ε : ℝ, NullMeasurableSet (F ∩ (E ε)ᶜ) P)
    (hsub : ∀ x : ℕ → ℝ, (∀ n, 0 < x n) → Tendsto x atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ω ∈ F → ∀ᶠ k in atTop, ω ∈ E (x (φ k))) :
    TendsToOneOn P F E := by
  unfold TendsToOneOn
  refine tendsto_nhdsWithin_zero_of_subseq fun x hpos hx => ?_
  obtain ⟨φ, hφ, hae⟩ := hsub x hpos hx
  refine ⟨φ, hφ, tendsto_measure_zero_of_ae_eventually_not_mem
    (fun k => F ∩ (E (x (φ k)))ᶜ) (fun k => hmeas (x (φ k))) ?_⟩
  filter_upwards [hae] with ω hω
  by_cases hF : ω ∈ F
  · filter_upwards [hω hF] with k hk
    exact fun hbad => hbad.2 hk
  · exact Eventually.of_forall fun k hbad => hF hbad.1

end MatedCRT.S5c
