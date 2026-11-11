import Mathlib.MeasureTheory.Measure.Continuity
import MatedCRT.Defs.Notation

/-!
# FIRST PASS, 5.3: the sequence criterion for `TendsToOneOn`

If the success events `E n` are null measurable and `ω ∈ F` implies that `ω` eventually lies in every `E n`, almost surely,
then `P(F ∩ (E n)ᶜ) → 0`. The set `F` need not be measurable: `P` is an outer measure, and the proof uses only the
null-measurable sets `C n = ⋃_{k ≥ n} (E k)ᶜ`, `I = ⋂_n C n` and `R n = C n \ I` (continuity from above), together with
`F ∩ (E n)ᶜ ⊆ R n ∪ (F ∩ I)` and `P(F ∩ I) = 0`.
-/

namespace MatedCRT.S5c

open MeasureTheory Set Filter Topology

/-- **Sequence criterion for `TendsToOneOn`**: if `E n` are null measurable and almost surely
every point of `F` eventually lies in `E n`, then `P(F ∩ (E n)ᶜ) → 0`. -/
theorem tendsto_measure_inter_compl_of_ae_eventually {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Set Ω} {E : ℕ → Set Ω}
    (hE : ∀ n, NullMeasurableSet (E n) P)
    (hAE : ∀ᵐ ω ∂P, ω ∈ F → ∀ᶠ n in atTop, ω ∈ E n) :
    Tendsto (fun n => P (F ∩ (E n)ᶜ)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ : ∃ C : ℕ → Set Ω, C = fun n => ⋃ k : ℕ, ⋃ (_ : n ≤ k), (E k)ᶜ := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : Set Ω, I = ⋂ n : ℕ, C n := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ → Set Ω, R = fun n => C n \ I := ⟨_, rfl⟩
  have hCmeas : ∀ n, NullMeasurableSet (C n) P := by
    intro n
    rw [hC]
    exact NullMeasurableSet.iUnion fun k => NullMeasurableSet.iUnion fun _ => (hE k).compl
  have hImeas : NullMeasurableSet I P := by
    rw [hI]
    exact NullMeasurableSet.iInter hCmeas
  have hRmeas : ∀ n, NullMeasurableSet (R n) P := by
    intro n
    rw [hR]
    exact (hCmeas n).diff hImeas
  have hCanti : Antitone C := by
    intro n m hnm ω hω
    rw [hC] at hω ⊢
    simp only [mem_iUnion] at hω ⊢
    obtain ⟨k, hmk, hk⟩ := hω
    exact ⟨k, hnm.trans hmk, hk⟩
  have hRanti : Antitone R := by
    intro n m hnm
    rw [hR]
    exact sdiff_subset_sdiff_left (hCanti hnm)
  -- `⋂ n, R n = ∅`: a point of every `C n` lies in `I`.
  have hRempty : ⋂ n, R n = ∅ := by
    apply eq_empty_of_forall_notMem
    intro ω hω
    have hωR : ∀ n, ω ∈ C n ∧ ω ∉ I := fun n => by
      have := mem_iInter.mp hω n
      rw [hR] at this
      exact this
    apply (hωR 0).2
    rw [hI]
    exact mem_iInter.mpr fun n => (hωR n).1
  have hT : Tendsto (fun n => P (R n)) atTop (𝓝 (P (⋂ n, R n))) :=
    tendsto_measure_iInter_atTop hRmeas hRanti ⟨0, measure_ne_top P _⟩
  rw [hRempty, measure_empty] at hT
  -- `P(F ∩ I) = 0`: on `F ∩ I` the eventual membership fails, almost surely.
  have hFI0 : P (F ∩ I) = 0 := by
    apply measure_mono_null _ (ae_iff.mp hAE)
    rintro ω ⟨hωF, hωI⟩ hp
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hp hωF)
    have hωC : ω ∈ C N := by
      have := mem_iInter.mp (by rw [← hI]; exact hωI) N
      exact this
    rw [hC] at hωC
    simp only [mem_iUnion] at hωC
    obtain ⟨k, hNk, hk⟩ := hωC
    exact hk (hN k hNk)
  -- `F ∩ (E n)ᶜ ⊆ R n ∪ (F ∩ I)`.
  have hsplit : ∀ n, F ∩ (E n)ᶜ ⊆ R n ∪ (F ∩ I) := by
    intro n ω ⟨hωF, hωE⟩
    have hωC : ω ∈ C n := by
      rw [hC]
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨le_rfl, hωE⟩⟩
    by_cases hωI : ω ∈ I
    · exact Or.inr ⟨hωF, hωI⟩
    · left
      rw [hR]
      exact ⟨hωC, hωI⟩
  have hbd : ∀ n, P (F ∩ (E n)ᶜ) ≤ P (R n) := fun n => by
    calc P (F ∩ (E n)ᶜ) ≤ P (R n ∪ (F ∩ I)) := measure_mono (hsplit n)
      _ ≤ P (R n) + P (F ∩ I) := measure_union_le _ _
      _ = P (R n) := by rw [hFI0, add_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => zero_le) hbd

end MatedCRT.S5c
