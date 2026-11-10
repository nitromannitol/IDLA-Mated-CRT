import MatedCRT.FirstPass.S5c.MarginInf

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), step M5): the measurable margin and its positive modification

For a countable index set `D ⊆ ℂ`, events `F q` and random variables `A q`, the outcome-wise margin
`marginFn D F A ω = ⨅ q ∈ D, (if ω ∈ F q then A q ω else 1)` is `m`-measurable when every `F q` is `m`-measurable and every
`A q` is `m`-measurable (a countable infimum of `Measurable.ite`). Its positive modification
`c ω = if 0 < W ω then W ω else 1` is `m`-measurable, everywhere positive, and equal to `W` wherever `W > 0`.
`marginFn_eq` identifies the outcome-wise margin with `marginInf` (MarginInf.lean) of the index set `I` at outcome `ω`
when the events and the values agree. No frozen input.
-/

namespace MatedCRT.S5c

open MeasureTheory Set
open scoped Classical

variable {Ω : Type*}

/-- The outcome-wise margin of the index family `F` with values `A` (`marginInf` at the outcome `ω`). -/
noncomputable def marginFn (D : Set ℂ) (F : ℂ → Set Ω) (A : ℂ → Ω → ℝ) (ω : Ω) : ℝ :=
  ⨅ q : D, if ω ∈ F q then A q ω else 1

/-- At an outcome `ω`, the margin of the events `F q` is the deterministic margin `marginInf` of the index set `I`,
provided the events and the values agree on `D`. -/
theorem marginFn_eq {D I : Set ℂ} {F : ℂ → Set Ω} {A : ℂ → Ω → ℝ} {A' : ℂ → ℝ} {ω : Ω}
    (hF : ∀ q ∈ D, ω ∈ F q ↔ q ∈ I) (hA : ∀ q ∈ D, ω ∈ F q → A q ω = A' q) :
    marginFn D F A ω = marginInf D I A' := by
  unfold marginFn marginInf
  refine iInf_congr fun q => ?_
  by_cases h : ω ∈ F q
  · have hI : (q : ℂ) ∈ I := (hF q q.2).1 h
    simp only [h, hI, ↓reduceIte, hA q q.2 h]
  · have hI : (q : ℂ) ∉ I := fun hI => h ((hF q q.2).2 hI)
    simp only [h, hI, ↓reduceIte]

/-- **Measurable margin** (M5): for a countable `D` and `m`-measurable events and values, there is an `m`-measurable
`c > 0` (everywhere) which equals the margin `marginFn D F A` wherever the margin is positive. -/
theorem exists_measurable_marginFn {m : MeasurableSpace Ω} {D : Set ℂ} (hD : D.Countable)
    (F : ℂ → Set Ω) (A : ℂ → Ω → ℝ) (hF : ∀ q, MeasurableSet[m] (F q)) (hA : ∀ q, Measurable[m] (A q)) :
    ∃ c : Ω → ℝ, Measurable[m] c ∧ (∀ ω, 0 < c ω) ∧
      ∀ ω, 0 < marginFn D F A ω → c ω = marginFn D F A ω := by
  have : Countable D := hD.to_subtype
  have hW : Measurable[m] (marginFn D F A) :=
    Measurable.iInf fun q => Measurable.ite (p := fun ω => ω ∈ F q) (hF q) (hA q) measurable_const
  refine ⟨fun ω => if 0 < marginFn D F A ω then marginFn D F A ω else 1, ?_, ?_, ?_⟩
  · exact Measurable.ite (p := fun ω => 0 < marginFn D F A ω) (measurableSet_lt measurable_const hW) hW
      measurable_const
  · intro ω
    dsimp only
    split_ifs with h
    · exact h
    · exact one_pos
  · intro ω h
    simp only [h, ↓reduceIte]

end MatedCRT.S5c
