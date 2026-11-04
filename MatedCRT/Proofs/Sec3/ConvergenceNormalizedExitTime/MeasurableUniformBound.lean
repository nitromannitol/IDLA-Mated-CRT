import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitTimeMeasurable

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

end MatedCRT
