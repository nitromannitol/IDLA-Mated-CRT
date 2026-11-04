import MatedCRT.Draft.Section3
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Almost-sure subsequences of high-probability events -/

namespace MatedCRT

open MeasureTheory Filter Topology Set

/-- Along any mesh sequence tending to zero, events whose probabilities tend
to one hold eventually on a further deterministic subsequence, almost surely. -/
theorem exists_subseq_eventually_of_probTendsToOne
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → Set Ω)
    (hE : ProbTendsToOne P E) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ E (ε (φ n)) := by
  classical
  let F : ℝ → Ω → ℝ := fun t ω => if ω ∈ E t then 0 else 1
  have hF : TendstoInMeasure P F (𝓝[>] 0) (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro δ hδ
    unfold ProbTendsToOne at hE
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE
      (fun _ => zero_le) fun t => ?_
    apply measure_mono
    intro ω hω
    change ω ∉ E t
    intro hmem
    simp [F, hmem, not_le_of_gt hδ] at hω
  obtain ⟨φ, hφ, hlim⟩ := (hF.comp hε).exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hlim] with ω hω
  filter_upwards [hω.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
  by_contra hnot
  simp [F, hnot] at hn
  norm_num at hn

end MatedCRT
