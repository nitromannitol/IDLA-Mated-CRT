import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.MeasurableClipping
import MatedCRT.Draft.Section3

/-! # Clipping a sequence of locally harmonic functions -/

namespace MatedCRT.GreenEnvironment

open Set Filter MeasureTheory

/-- If a sequence is eventually locally harmonic and bounded almost surely,
measurable clipping enforces the hypotheses at every index and every sample,
without changing its almost-sure tail. -/
theorem exists_clipped_harmonic_sequence
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℕ → Ω → ℤ → ℤ → ℕ) (hM : ∀ n j k, Measurable fun ω => M n ω j k)
    (V W : ℕ → Ω → Set ℤ) (hV : ∀ n, Measurable (V n)) (hW : ∀ n, Measurable (W n))
    (u : Ω → ℕ → ℤ → ℝ) (hu : ∀ n k, Measurable fun ω => u ω n k)
    (K : ℝ) (hK : 0 ≤ K) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hgood : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (∀ a ∈ W n ω, matedLaplacian (M n ω) (u ω n) a = 0) ∧
      (∀ a ∈ V n ω, |u ω n a| ≤ K / ε n)) :
    ∃ v : Ω → ℕ → ℤ → ℝ, (∀ n k, Measurable fun ω => v ω n k) ∧
      (∀ ω n a, a ∈ W n ω → matedLaplacian (M n ω) (v ω n) a = 0) ∧
      (∀ ω n a, a ∈ V n ω → |v ω n a| ≤ K / ε n) ∧
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, v ω n = u ω n := by
  choose v hvm hvl hvb hve using fun n => exists_measurable_clipped_harmonic
    (M n) (hM n) (V n) (W n) (hV n) (hW n) (fun ω => u ω n) (hu n) K (ε n) hK (hε n)
  refine ⟨fun ω n => v n ω, hvm, ?_, ?_, ?_⟩
  · intro ω n a ha
    exact hvl n ω a ha
  · intro ω n a ha
    exact hvb n ω a ha
  · filter_upwards [hgood] with ω hω
    filter_upwards [hω] with n hn
    exact hve n ω hn.1 hn.2

end MatedCRT.GreenEnvironment
