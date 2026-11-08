import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Borel null sandwiches and law transfer for universally measurable sets

Measure-theoretic first component of `lem:allstarts` (env-steps.tex:380-446) and of the proof of `prop:clock`
(env-steps.tex:449-487). A universally measurable set `G` is null-measurable for every finite Borel measure, in
particular for the law `ν = P.map X`, so it is sandwiched between Borel sets `A ⊆ G ⊆ B` with `ν (B \ A) = 0`.
Equality in law then transfers almost-sure membership in `G` from `X` to `Y`, using only the inverse images of
`A` and `B`; the probability space need not be complete.
-/

namespace MatedCRT.EnvClock

open MeasureTheory

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- A Borel null sandwich of `G` for the law `ν`: Borel sets `A ⊆ G ⊆ B` with `ν (B \ A) = 0`. -/
def HasBorelNullSandwich (ν : Measure E) (G : Set E) : Prop :=
  ∃ A B : Set E, MeasurableSet A ∧ MeasurableSet B ∧ A ⊆ G ∧ G ⊆ B ∧ ν (B \ A) = 0

/-- Universal measurability: `G` is null-measurable for every finite Borel measure on `E`. -/
def IsUniversallyMeasurableSet (G : Set E) : Prop :=
  ∀ ν : Measure E, IsFiniteMeasure ν → NullMeasurableSet G ν

/-- A null-measurable set has a Borel null sandwich for its own measure. -/
theorem hasBorelNullSandwich_of_nullMeasurableSet {ν : Measure E} {G : Set E}
    (h : NullMeasurableSet G ν) : HasBorelNullSandwich ν G := by
  obtain ⟨B, hGB, hBm, hBeq⟩ := h.exists_measurable_superset_ae_eq
  obtain ⟨A, hAG, hAm, hAeq⟩ := h.exists_measurable_subset_ae_eq
  refine ⟨A, B, hAm, hBm, hAG, hGB, ?_⟩
  have h1 : ν (B \ G) = 0 := (ae_eq_set.1 hBeq).1
  have h2 : ν (G \ A) = 0 := (ae_eq_set.1 hAeq).2
  refine measure_mono_null (t := (B \ G) ∪ (G \ A)) ?_ (measure_union_null h1 h2)
  rintro x ⟨hxB, hxA⟩
  by_cases hxG : x ∈ G
  · exact Or.inr ⟨hxG, hxA⟩
  · exact Or.inl ⟨hxB, hxG⟩

/-- Equality in law transfers almost-sure membership in a set with a Borel null sandwich. Only the inverse images
of the Borel sets `A` and `B` enter, so the probability space need not be complete (proof of `prop:clock`,
env-steps.tex:449-487). -/
theorem ae_mem_of_map_eq {P : Measure Ω} {X Y : Ω → E}
    (hX : Measurable X) (hY : Measurable Y) (hlaw : P.map X = P.map Y)
    {G : Set E} (hG : HasBorelNullSandwich (P.map X) G)
    (hXG : ∀ᵐ ω ∂P, X ω ∈ G) : ∀ᵐ ω ∂P, Y ω ∈ G := by
  obtain ⟨A, B, hAm, hBm, hAG, hGB, hnull⟩ := hG
  rw [ae_iff] at hXG ⊢
  have hBcX : (P.map X) Bᶜ = 0 := by
    rw [Measure.map_apply hX hBm.compl]
    exact measure_mono_null (t := {ω | ¬ X ω ∈ G}) (fun ω hω hGω => hω (hGB hGω)) hXG
  have hBcY : (P.map Y) Bᶜ = 0 := by rw [← hlaw]; exact hBcX
  have hdiffY : (P.map Y) (B \ A) = 0 := by rw [← hlaw]; exact hnull
  rw [Measure.map_apply hY hBm.compl] at hBcY
  rw [Measure.map_apply hY (hBm.diff hAm)] at hdiffY
  refine measure_mono_null (t := Y ⁻¹' (B \ A) ∪ Y ⁻¹' Bᶜ) ?_ (measure_union_null hdiffY hBcY)
  intro ω hω
  by_cases hB : Y ω ∈ B
  · exact Or.inl ⟨hB, fun hA => hω (hAG hA)⟩
  · exact Or.inr hB

/-- Almost-sure membership in a set with a Borel null sandwich is invariant under equality in law. -/
theorem ae_mem_iff_of_map_eq {P : Measure Ω} {X Y : Ω → E}
    (hX : Measurable X) (hY : Measurable Y) (hlaw : P.map X = P.map Y)
    {G : Set E} (hG : HasBorelNullSandwich (P.map X) G) :
    (∀ᵐ ω ∂P, X ω ∈ G) ↔ ∀ᵐ ω ∂P, Y ω ∈ G := by
  refine ⟨ae_mem_of_map_eq hX hY hlaw hG, fun hYG => ?_⟩
  have hG' : HasBorelNullSandwich (P.map Y) G := by rw [← hlaw]; exact hG
  exact ae_mem_of_map_eq hY hX hlaw.symm hG' hYG

/-- Universally measurable sets transfer almost-sure membership under equality in law. -/
theorem ae_mem_of_map_eq_of_univMeas {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → E}
    (hX : Measurable X) (hY : Measurable Y) (hlaw : P.map X = P.map Y)
    {G : Set E} (hG : IsUniversallyMeasurableSet G) (hXG : ∀ᵐ ω ∂P, X ω ∈ G) :
    ∀ᵐ ω ∂P, Y ω ∈ G :=
  ae_mem_of_map_eq hX hY hlaw
    (hasBorelNullSandwich_of_nullMeasurableSet (hG (P.map X) inferInstance)) hXG

end MatedCRT.EnvClock
