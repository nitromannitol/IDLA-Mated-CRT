import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitTimeMeasurable
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitLaplacianBound

/-! Measurable uniform bounds for countable families. -/

namespace MatedCRT

open MeasureTheory Filter
open scoped ENNReal

/-- A countable measurable family that is almost surely bounded has a
measurable positive bound, even if the original bound is not measurable. -/
theorem exists_measurable_uniform_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (m : MeasurableSpace Ω)
    (f : Ω → ℕ → ℤ → ℝ) (hf : ∀ n a, Measurable[m] fun ω => f ω n a)
    (hf0 : ∀ ω n a, 0 ≤ f ω n a)
    (hbound : ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ n a, f ω n a ≤ C) :
    ∃ C : Ω → ℝ, Measurable[m] C ∧ (∀ ω, 1 ≤ C ω) ∧
      ∀ᵐ ω ∂P, ∀ n a, f ω n a ≤ C ω := by
  let X : Ω → ℝ≥0∞ := fun ω => ⨆ n : ℕ, ⨆ a : ℤ, ENNReal.ofReal (f ω n a)
  have hXm : Measurable[m] X := by
    let : MeasurableSpace Ω := m
    exact Measurable.iSup fun n => Measurable.iSup fun a => ENNReal.measurable_ofReal.comp (hf n a)
  have hXfin : ∀ᵐ ω ∂P, X ω ≠ ⊤ := by
    filter_upwards [hbound] with ω ⟨C, hC⟩
    apply ne_of_lt
    refine lt_of_le_of_lt (b := ENNReal.ofReal C) ?_ ENNReal.ofReal_lt_top
    exact iSup_le fun n => iSup_le fun a => ENNReal.ofReal_le_ofReal (hC n a)
  refine ⟨fun ω => (X ω).toReal + 1, (ENNReal.measurable_toReal.comp hXm).add_const 1,
    (fun ω => by have := ENNReal.toReal_nonneg (a := X ω); linarith), ?_⟩
  filter_upwards [hXfin] with ω hω n a
  have hle : ENNReal.ofReal (f ω n a) ≤ X ω := le_iSup_of_le n (le_iSup (fun a => ENNReal.ofReal (f ω n a)) a)
  have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hω).2 hle
  rw [ENNReal.toReal_ofReal (hf0 ω n a)] at h
  linarith

/-- A pathwise bound for the normalized exit times along selected meshes can
be replaced by an environment-measurable bound. -/
theorem MatedCRTEnv.IsValid.exists_measurable_exit_time_bound
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℕ → ℝ) (I : Ω → ℕ → ℕ)
    (hI : ∀ n, Measurable[S.envSigma] fun ω => I ω n)
    (hε : ∀ ω n, 0 < ε (I ω n)) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D)
    (hbound : ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ n a,
      ε (I ω n) * |normExitTime (S.mult (ε (I ω n)) ω)
        (interiorCellVertices (ε (I ω n)) (S.η ω) D) a| ≤ C) :
    ∃ C : Ω → ℝ, Measurable[S.envSigma] C ∧ (∀ ω, 1 ≤ C ω) ∧
      ∀ᵐ ω ∂S.P, ∀ n a,
        |normExitTime (S.mult (ε (I ω n)) ω)
          (interiorCellVertices (ε (I ω n)) (S.η ω) D) a| ≤ C ω / ε (I ω n) := by
  obtain ⟨u, hum, hue⟩ := hS.exists_envSigma_measurable_selected_normExitTime ε D hD I hI
  let f : Ω → ℕ → ℤ → ℝ := fun ω n a => ε (I ω n) * |u ω n a|
  have hfm : ∀ n a, Measurable[S.envSigma] fun ω => f ω n a := by
    let : MeasurableSpace Ω := S.envSigma
    intro n a
    exact ((measurable_of_countable ε).comp (hI n)).mul (hum n a).abs
  have hf0 : ∀ ω n a, 0 ≤ f ω n a := fun ω n a =>
    mul_nonneg (hε ω n).le (abs_nonneg _)
  have hfb : ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ n a, f ω n a ≤ C := by
    filter_upwards [hbound, hue] with ω ⟨C, hC⟩ hu
    exact ⟨C, fun n a => by simpa [f, hu n a] using hC n a⟩
  obtain ⟨C, hCm, hC1, hCf⟩ := exists_measurable_uniform_bound S.P S.envSigma f hfm hf0 hfb
  refine ⟨C, hCm, hC1, ?_⟩
  filter_upwards [hCf, hue] with ω hω hu n a
  apply (le_div_iff₀ (hε ω n)).2
  simpa [f, hu n a, mul_comm] using hω n a

/-- For a bounded domain, an eventual pathwise bound on its cells suffices:
each earlier mesh has finitely many interior cells and the exit time vanishes
outside them. -/
theorem MatedCRTEnv.IsValid.exists_measurable_exit_time_bound_of_eventual
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℕ → ℝ) (I : Ω → ℕ → ℕ)
    (hI : ∀ n, Measurable[S.envSigma] fun ω => I ω n)
    (hε : ∀ ω n, 0 < ε (I ω n)) (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D)
    (hDb : Bornology.IsBounded D)
    (hbound : ∀ᵐ ω ∂S.P, ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε (I ω n)) (S.η ω) D,
        ε (I ω n) * |normExitTime (S.mult (ε (I ω n)) ω)
          (interiorCellVertices (ε (I ω n)) (S.η ω) D) a| ≤ C) :
    ∃ C : Ω → ℝ, Measurable[S.envSigma] C ∧ (∀ ω, 1 ≤ C ω) ∧
      ∀ᵐ ω ∂S.P, ∀ n a,
        |normExitTime (S.mult (ε (I ω n)) ω)
          (interiorCellVertices (ε (I ω n)) (S.η ω) D) a| ≤ C ω / ε (I ω n) := by
  apply hS.exists_measurable_exit_time_bound ε I hI hε D hD
  filter_upwards [hbound, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω ⟨C, htail⟩ hη hp
  have hs : ∀ n, ∃ B : ℝ, ∀ a : ℤ,
      ε (I ω n) * |normExitTime (S.mult (ε (I ω n)) ω)
        (interiorCellVertices (ε (I ω n)) (S.η ω) D) a| ≤ B := by
    intro n
    let A := interiorCellVertices (ε (I ω n)) (S.η ω) D
    let g : ℤ → ℝ := fun a => ε (I ω n) * |normExitTime (S.mult (ε (I ω n)) ω) A a|
    have hA : A.Finite :=
      (Tightness.cellVertices_finite hη.1 hp (hε ω n) hDb).subset (by
        dsimp [A, interiorCellVertices]
        exact Set.sdiff_subset)
    obtain ⟨B, hB⟩ := ((hA.image g).union (Set.finite_singleton 0)).bddAbove
    refine ⟨B, fun a => ?_⟩
    change g a ≤ B
    by_cases ha : a ∈ A
    · exact hB (Set.mem_union_left _ ⟨a, ha, rfl⟩)
    · have h0 : g a = 0 := by
        simp [g, normExitTime_eq_zero_of_not_mem _ ha]
      rw [h0]
      exact hB (Set.mem_union_right _ (Set.mem_singleton 0))
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  choose B hB using hs
  obtain ⟨B₀, hB₀⟩ := ((Finset.finite_toSet (Finset.range N)).image B).bddAbove
  refine ⟨max B₀ (max C 0), fun n a => ?_⟩
  by_cases hn : n < N
  · exact (hB n a).trans ((hB₀ ⟨n, Finset.mem_range.mpr hn, rfl⟩).trans (le_max_left _ _))
  · by_cases ha : a ∈ interiorCellVertices (ε (I ω n)) (S.η ω) D
    · have hac : a ∈ cellVertices (ε (I ω n)) (S.η ω) D := by
        exact Set.sdiff_subset ha
      exact (hN n (Nat.le_of_not_gt hn) a hac).trans (le_trans (le_max_left _ _) (le_max_right _ _))
    · rw [normExitTime_eq_zero_of_not_mem _ ha, abs_zero, mul_zero]
      exact le_trans (le_max_right _ _) (le_max_right _ _)

end MatedCRT
