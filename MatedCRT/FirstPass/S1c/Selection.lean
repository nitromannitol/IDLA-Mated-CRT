import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable radius from null-measurable containment events (selection step of Lemma 1, fleet note G-hT)

Pure measure theory, no paper-specific input. This is the last step of `FixedTimeRadiusStep`
(`MatedCRT/FirstPass/S1c.lean`): once the events `{ω | Λ_u(ω) ⊆ B̄_n}` are null-measurable for every integer `n`
and a.s. some of them occurs, the first index that occurs gives a measurable radius.
-/

namespace MatedCRT

open MeasureTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- First index selection from measurable versions `F n` of the events `E n`: if `F n` is measurable and a.s.
`ω ∈ F n ↔ ω ∈ E n` for all `n` simultaneously, and a.s. some `E n` holds, then the least `n` with `ω ∈ F n`
(total via a catch-all set `Z` where no `F n` holds) is a measurable index with `ω ∈ E (M ω)` a.s. -/
theorem exists_measurable_index_mem_of_versions (P : Measure Ω) (E F : ℕ → Set Ω)
    (hFm : ∀ n, MeasurableSet (F n)) (hFE : ∀ᵐ ω ∂P, ∀ n, (ω ∈ F n ↔ ω ∈ E n))
    (hex : ∀ᵐ ω ∂P, ∃ n, ω ∈ E n) :
    ∃ M : Ω → ℕ, Measurable M ∧ ∀ᵐ ω ∂P, ω ∈ E (M ω) := by
  classical
  set Z : Set Ω := ⋂ n, (F n)ᶜ with hZ
  have hZm : MeasurableSet Z := MeasurableSet.iInter fun n => (hFm n).compl
  have hG : ∀ ω, ∃ n, ω ∈ F n ∪ Z := by
    intro ω
    by_cases h : ∃ n, ω ∈ F n
    · obtain ⟨n, hn⟩ := h
      exact ⟨n, Or.inl hn⟩
    · refine ⟨0, Or.inr ?_⟩
      exact mem_iInter.2 fun n hn => h ⟨n, hn⟩
  have hGm : ∀ k, MeasurableSet {ω | ω ∈ F k ∪ Z} := fun k => (hFm k).union hZm
  refine ⟨fun ω => Nat.find (hG ω), measurable_find (p := fun ω n => ω ∈ F n ∪ Z) hG hGm, ?_⟩
  filter_upwards [hFE, hex] with ω hω hωex
  obtain ⟨m, hm⟩ := hωex
  have hωZ : ω ∉ Z := fun hz => (mem_iInter.1 hz m) ((hω m).2 hm)
  rcases Nat.find_spec (hG ω) with h1 | h2
  · exact (hω _).1 h1
  · exact absurd h2 hωZ

/-- Real-valued radius form (the shape of `FixedTimeRadiusStep`): if for each integer `n` the set of `ω` with
`S ω ⊆ B̄_n` is null-measurable, and a.s. `S ω` lies in some `B̄_n`, then there is a measurable real radius `M`
with `S ω ⊆ B̄_{M ω}` almost surely. -/
theorem exists_measurable_radius_of_null_measurable (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → Set ℂ) (hS : ∀ n : ℕ, NullMeasurableSet {ω | S ω ⊆ Metric.closedBall 0 (n : ℝ)} P)
    (hbdd : ∀ᵐ ω ∂P, ∃ n : ℕ, S ω ⊆ Metric.closedBall 0 (n : ℝ)) :
    ∃ M : Ω → ℝ, Measurable M ∧ ∀ᵐ ω ∂P, S ω ⊆ Metric.closedBall 0 (M ω) := by
  let E : ℕ → Set Ω := fun n => {ω | S ω ⊆ Metric.closedBall 0 (n : ℝ)}
  let F : ℕ → Set Ω := fun n => toMeasurable P (E n)
  have hFm : ∀ n, MeasurableSet (F n) := fun n => measurableSet_toMeasurable P (E n)
  have hFE : ∀ᵐ ω ∂P, ∀ n, (ω ∈ F n ↔ ω ∈ E n) :=
    ae_all_iff.2 fun n => (hS n).toMeasurable_ae_eq.mem_iff
  obtain ⟨M, hMm, hM⟩ := exists_measurable_index_mem_of_versions P E F hFm hFE hbdd
  exact ⟨fun ω => ((M ω : ℕ) : ℝ), measurable_from_nat.comp hMm, by filter_upwards [hM] with ω hω; exact hω⟩

end MatedCRT
