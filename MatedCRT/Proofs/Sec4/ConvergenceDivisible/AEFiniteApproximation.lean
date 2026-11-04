import MatedCRT.Proofs.Sec4.ConvergenceDivisible.FiniteApproximation

/-! # Almost-sure finite discrete obstacle problems -/

namespace MatedCRT

open Set MeasureTheory

/-- If the finite-graph hypotheses hold on a measurable full-measure event,
the discrete least supersolution is almost everywhere measurable. -/
theorem MatedCRTEnv.IsValid.aemeasurable_discreteLeastSupersolution_of_finite
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (r φ : Ω → ℤ → ℝ) (hr : ∀ b, Measurable fun ω => r ω b)
    (hφ : ∀ b, Measurable fun ω => φ ω b) (a : ℤ)
    (B : Set Ω) (hB : MeasurableSet B) (hBae : ∀ᵐ ω ∂S.P, ω ∈ B)
    (hVW : ∀ ω ∈ B, V ω ⊆ W ω) (hr0 : ∀ ω ∈ B, ∀ b, 0 ≤ r ω b)
    (hφ0 : ∀ ω ∈ B, ∀ b, φ ω b ≤ 0)
    (hVfin : ∀ ω ∈ B, (V ω).Finite) (hWfin : ∀ ω ∈ B, (W ω).Finite)
    (hlf : ∀ ω ∈ B, ∀ b, b ∈ V ω → {c | S.mult ε ω b c ≠ 0}.Finite)
    (hrpos : ∀ ω ∈ B, ∀ b, b ∈ V ω → 0 < r ω b) :
    AEMeasurable (fun ω => discreteLeastSupersolution (S.mult ε ω) (V ω) (W ω)
      (r ω) (φ ω) a) S.P := by
  classical
  let V' : Ω → Set ℤ := fun ω => if ω ∈ B then V ω else ∅
  let W' : Ω → Set ℤ := fun ω => if ω ∈ B then W ω else ∅
  let r' : Ω → ℤ → ℝ := fun ω => if ω ∈ B then r ω else fun _ => 1
  let φ' : Ω → ℤ → ℝ := fun ω => if ω ∈ B then φ ω else fun _ => 0
  have hV' : Measurable V' := Measurable.ite hB hV measurable_const
  have hW' : Measurable W' := Measurable.ite hB hW measurable_const
  have hr' : ∀ b, Measurable fun ω => r' ω b := by
    intro b
    have hm : Measurable (fun ω => if ω ∈ B then r ω b else (1 : ℝ)) :=
      Measurable.ite hB (hr b) measurable_const
    convert hm using 1
    ext ω
    by_cases hω : ω ∈ B <;> simp [r', hω]
  have hφ' : ∀ b, Measurable fun ω => φ' ω b := by
    intro b
    have hm : Measurable (fun ω => if ω ∈ B then φ ω b else (0 : ℝ)) :=
      Measurable.ite hB (hφ b) measurable_const
    convert hm using 1
    ext ω
    by_cases hω : ω ∈ B <;> simp [φ', hω]
  have hVW' : ∀ ω, V' ω ⊆ W' ω := by
    intro ω
    by_cases hω : ω ∈ B
    · simpa [V', W', hω] using hVW ω hω
    · simp [V', hω]
  have hr0' : ∀ ω b, 0 ≤ r' ω b := by
    intro ω b
    by_cases hω : ω ∈ B
    · simpa [r', hω] using hr0 ω hω b
    · simp [r', hω]
  have hφ0' : ∀ ω b, φ' ω b ≤ 0 := by
    intro ω b
    by_cases hω : ω ∈ B
    · simpa [φ', hω] using hφ0 ω hω b
    · simp [φ', hω]
  have hVfin' : ∀ ω, (V' ω).Finite := by
    intro ω
    by_cases hω : ω ∈ B
    · simpa [V', hω] using hVfin ω hω
    · simp [V', hω]
  have hWfin' : ∀ ω, (W' ω).Finite := by
    intro ω
    by_cases hω : ω ∈ B
    · simpa [W', hω] using hWfin ω hω
    · simp [W', hω]
  have hlf' : ∀ ω b, b ∈ V' ω → {c | S.mult ε ω b c ≠ 0}.Finite := by
    intro ω b hb
    by_cases hω : ω ∈ B
    · exact hlf ω hω b (by simpa [V', hω] using hb)
    · simp [V', hω] at hb
  have hrpos' : ∀ ω b, b ∈ V' ω → 0 < r' ω b := by
    intro ω b hb
    by_cases hω : ω ∈ B
    · simpa [r', hω] using hrpos ω hω b (by simpa [V', hω] using hb)
    · simp [V', hω] at hb
  have hm := hS.measurable_discreteLeastSupersolution_of_finite ε V' W' hV' hW'
    r' φ' hr' hφ' a hVW' hr0' hφ0' hVfin' hWfin' hlf' hrpos'
  apply hm.aemeasurable.congr
  filter_upwards [hBae] with ω hω
  simp [V', W', r', φ', hω]

end MatedCRT
