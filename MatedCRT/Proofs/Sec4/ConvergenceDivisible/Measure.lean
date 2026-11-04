import MatedCRT.Draft.Section4
import Mathlib.MeasureTheory.Integral.Indicator

/-! # A probability step for almost-sure eventual avoidance -/

open Filter MeasureTheory Set
open scoped Topology

namespace MatedCRT

/-- In a finite measure space, null-measurable events which occur only finitely often almost surely
have probabilities tending to zero. -/
theorem tendsto_measure_zero_of_ae_eventually_not_mem {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (E : ℕ → Set Ω)
    (hE : ∀ n, NullMeasurableSet (E n) P)
    (h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ E n) :
    Tendsto (fun n => P (E n)) atTop (𝓝 0) := by
  have heq : ∀ᵐ ω ∂P, ∀ n, ω ∈ toMeasurable P (E n) ↔ ω ∈ E n := by
    rw [ae_all_iff]
    intro n
    filter_upwards [(hE n).toMeasurable_ae_eq] with ω heqω
    exact iff_of_eq heqω
  have h' : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∈ toMeasurable P (E n) ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [h, heq] with ω hω heqω
    filter_upwards [hω] with n hn
    simp [heqω n, hn]
  simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := P) atTop (A := ∅) MeasurableSet.empty (fun n => measurableSet_toMeasurable P _) h'

/-- A subsequential almost-sure criterion for convergence of the probabilities of measurable
events as the positive mesh size tends to zero. -/
theorem tendsto_measure_zero_of_subsequence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (E : ℝ → Set Ω)
    (hE : ∀ ε, 0 < ε → NullMeasurableSet (E ε) P)
    (h : ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ E (εs (φ n))) :
    Tendsto (fun ε => P (E ε)) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro a ha
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hmesh : Tendsto (fun n => a (ns n)) atTop (𝓝[>] 0) := ha.comp hns
  have hpos : ∀ᶠ n in atTop, 0 < a (ns n) := hmesh.eventually self_mem_nhdsWithin
  let b : ℕ → ℝ := fun n => if 0 < a (ns n) then a (ns n) else 1 / ((n : ℝ) + 1)
  have hbpos : ∀ n, 0 < b n := by
    intro n
    dsimp [b]
    split_ifs with hn
    · exact hn
    · positivity
  have hbeq : b =ᶠ[atTop] fun n => a (ns n) := by
    filter_upwards [hpos] with n hn
    simp [b, hn]
  have hb : Tendsto b atTop (𝓝 0) :=
    (tendsto_nhdsWithin_iff.mp hmesh).1.congr' hbeq.symm
  obtain ⟨φ, hφ, hφae⟩ := h b hbpos hb
  have hprob := tendsto_measure_zero_of_ae_eventually_not_mem P (fun n => E (b (φ n)))
    (fun n => hE _ (hbpos _)) hφae
  refine ⟨φ, ?_⟩
  apply hprob.congr'
  filter_upwards [hφ.tendsto_atTop.eventually hbeq] with n hn
  simp only [Function.comp_apply]
  rw [hn]

end MatedCRT
