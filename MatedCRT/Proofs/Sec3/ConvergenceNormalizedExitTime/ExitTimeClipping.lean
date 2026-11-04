import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.MeasurableClipping

/-! Measurable clipping for discrete functions with bounded Laplacian. -/

namespace MatedCRT.GreenEnvironment

open Set Filter MeasureTheory

/-- Clipping a measurable vertex function to zero when either its Laplacian
or its size bound fails enforces both bounds everywhere, while preserving the
function on the good event. -/
theorem exists_measurable_clipped_bounded_laplacian
    {Ω : Type} [MeasurableSpace Ω] (M : Ω → ℤ → ℤ → ℕ)
    (hM : ∀ j k, Measurable fun ω => M ω j k)
    (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (u : Ω → ℤ → ℝ) (hu : ∀ k, Measurable fun ω => u ω k)
    (C E : Ω → ℝ) (hC : Measurable C) (hE : Measurable E)
    (hC0 : ∀ ω, 0 ≤ C ω) (hE0 : ∀ ω, 0 < E ω) :
    ∃ v : Ω → ℤ → ℝ, (∀ k, Measurable fun ω => v ω k) ∧
      (∀ ω a, a ∈ W ω → |matedLaplacian (M ω) (v ω) a| ≤ C ω) ∧
      (∀ ω a, a ∈ V ω → |v ω a| ≤ C ω / E ω) ∧
      ∀ ω, (∀ a ∈ W ω, |matedLaplacian (M ω) (u ω) a| ≤ C ω) →
        (∀ a ∈ V ω, |u ω a| ≤ C ω / E ω) → v ω = u ω := by
  classical
  let G : Set Ω := {ω | (∀ a ∈ W ω, |matedLaplacian (M ω) (u ω) a| ≤ C ω) ∧
    (∀ a ∈ V ω, |u ω a| ≤ C ω / E ω)}
  have hG : MeasurableSet G := by
    have h1 : MeasurableSet {ω | ∀ a ∈ W ω,
        |matedLaplacian (M ω) (u ω) a| ≤ C ω} := by
      convert MeasurableSet.iInter (fun a : ℤ =>
        (measurableSet_setOfPred.mpr ((measurable_set_mem a).comp hW)).compl.union
          (measurableSet_le (measurable_matedLaplacian M hM u hu a).abs hC)) using 1
      ext ω
      simp [imp_iff_not_or]
    have h2 : MeasurableSet {ω | ∀ a ∈ V ω, |u ω a| ≤ C ω / E ω} := by
      convert MeasurableSet.iInter (fun a : ℤ =>
        (measurableSet_setOfPred.mpr ((measurable_set_mem a).comp hV)).compl.union
          (measurableSet_le (hu a).abs (hC.div hE))) using 1
      ext ω
      simp [imp_iff_not_or]
    exact h1.inter h2
  let v : Ω → ℤ → ℝ := fun ω a => if ω ∈ G then u ω a else 0
  refine ⟨v, (fun a => (hu a).ite hG measurable_const), ?_, ?_, ?_⟩
  · intro ω a ha
    by_cases h : ω ∈ G
    · have hv : v ω = u ω := by funext b; simp [v, h]
      rw [hv]
      exact h.1 a ha
    · have hv : v ω = fun _ => 0 := by funext b; simp [v, h]
      rw [hv]
      simpa [matedLaplacian, mLaplacian] using hC0 ω
  · intro ω a ha
    by_cases h : ω ∈ G
    · simpa [v, h] using h.2 a ha
    · simp [v, h, div_nonneg (hC0 ω) (hE0 ω).le]
  · intro ω hh hb
    funext a
    simp [v, show ω ∈ G from ⟨hh, hb⟩]

/-- An eventually good sequence is unchanged eventually almost surely by
measurable clipping, including for random positive meshes. -/
theorem exists_clipped_bounded_laplacian_sequence
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℕ → Ω → ℤ → ℤ → ℕ) (hM : ∀ n j k, Measurable fun ω => M n ω j k)
    (V W : ℕ → Ω → Set ℤ) (hV : ∀ n, Measurable (V n)) (hW : ∀ n, Measurable (W n))
    (u : Ω → ℕ → ℤ → ℝ) (hu : ∀ n k, Measurable fun ω => u ω n k)
    (C : Ω → ℝ) (hC : Measurable C) (hC0 : ∀ ω, 0 ≤ C ω)
    (E : Ω → ℕ → ℝ) (hE : ∀ n, Measurable fun ω => E ω n)
    (hE0 : ∀ ω n, 0 < E ω n)
    (hgood : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (∀ a ∈ W n ω, |matedLaplacian (M n ω) (u ω n) a| ≤ C ω) ∧
      (∀ a ∈ V n ω, |u ω n a| ≤ C ω / E ω n)) :
    ∃ v : Ω → ℕ → ℤ → ℝ, (∀ n k, Measurable fun ω => v ω n k) ∧
      (∀ ω n a, a ∈ W n ω → |matedLaplacian (M n ω) (v ω n) a| ≤ C ω) ∧
      (∀ ω n a, a ∈ V n ω → |v ω n a| ≤ C ω / E ω n) ∧
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, v ω n = u ω n := by
  choose v hvm hvl hvb hve using fun n => exists_measurable_clipped_bounded_laplacian
    (M n) (hM n) (V n) (W n) (hV n) (hW n) (fun ω => u ω n) (hu n)
    C (fun ω => E ω n) hC (hE n) hC0 (fun ω => hE0 ω n)
  refine ⟨fun ω n => v n ω, hvm, ?_, ?_, ?_⟩
  · intro ω n a ha
    exact hvl n ω a ha
  · intro ω n a ha
    exact hvb n ω a ha
  · filter_upwards [hgood] with ω hω
    filter_upwards [hω] with n hn
    exact hve n ω hn.1 hn.2

end MatedCRT.GreenEnvironment
