import MatedCRT.FirstPass.S5c.SubseqCriterion
import MatedCRT.Defs.Notation

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (c)): the subsequence criterion for `TendsToOneOn` with outer probabilities

`TendsToOneOn P F E` (Defs/Notation.lean) says that `P (F ∩ (E ε)ᶜ) → 0` as `ε ↓ 0`, where `P` is evaluated on arbitrary
sets (outer measure). This criterion asks only for a subsequence, along every mesh sequence, on which the outer probabilities
of the failure events tend to zero. It needs no measurability of `F` or of the success events `E ε`; the bounds along the
subsequence come from countable subadditivity of the outer measure (three-inputs §8, the summable bounds), not from
null measurability (three-inputs §6.1 needs `NullMeasurableSet (E n) P`, which is avoided here).
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Topology Set ENNReal

/-- **Subsequence criterion with outer probabilities**: if along every positive sequence `x → 0` some subsequence has
`P (F ∩ (E (x (φ k)))ᶜ) → 0`, then `TendsToOneOn P F E`. No measurability of `F` or `E ε` is assumed. -/
theorem tendsToOneOn_of_outer_subseq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Set Ω) (E : ℝ → Set Ω)
    (h : ∀ x : ℕ → ℝ, (∀ n, 0 < x n) → Tendsto x atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => P (F ∩ (E (x (φ k)))ᶜ)) atTop (𝓝 0)) :
    MatedCRT.TendsToOneOn P F E := by
  unfold MatedCRT.TendsToOneOn
  exact tendsto_nhdsWithin_zero_of_subseq (f := fun ε => P (F ∩ (E ε)ᶜ)) h

end MatedCRT.S5c
