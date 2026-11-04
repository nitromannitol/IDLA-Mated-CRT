import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LQGMeasureMeasurable

/-! # Countable reductions for continuum supersolutions -/

namespace MatedCRT

open Set MeasureTheory Filter HarmonicBalls Laplacian Metric

/-- A countable determining family of test functions makes the distributional
Laplacian inequality for a fixed candidate a null-measurable event. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_laplacianLE_of_countable_tests
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (w : ℂ → ℝ) (U : Set ℂ) (φ : ℕ → ℂ → ℝ)
    (hφ : ∀ n, Continuous (φ n) ∧ HasCompactSupport (φ n))
    (hdet : ∀ᵐ ω ∂S.P, LaplacianLE w (S.μ ω) U ↔ ∀ n,
      (∫ x, w x * Δ (φ n) x) ≤ ∫ x, φ n x ∂(S.μ ω)) :
    NullMeasurableSet {ω | LaplacianLE w (S.μ ω) U} S.P := by
  have h : NullMeasurableSet {ω | ∀ n,
      (∫ x, w x * Δ (φ n) x) ≤ ∫ x, φ n x ∂(S.μ ω)} S.P := by
    convert NullMeasurableSet.iInter (fun n => nullMeasurableSet_le
      (aemeasurable_const : AEMeasurable (fun _ : Ω => ∫ x, w x * Δ (φ n) x) S.P)
      (hS.aemeasurable_lqg_integral (φ n) (hφ n).1 (hφ n).2)) using 1
    ext ω
    simp
  apply h.congr
  filter_upwards [hdet] with ω hω
  exact propext hω.symm

/-- Under a countable test criterion, admissibility of a fixed continuum
supersolution is null measurable. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_supersolution_of_countable_tests
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (r t : ℝ) (z : ℂ) (w : ℂ → ℝ) (φ : ℕ → ℂ → ℝ)
    (hφ : ∀ n, Continuous (φ n) ∧ HasCompactSupport (φ n))
    (hdet : ∀ᵐ ω ∂S.P, LaplacianLE w (S.μ ω) (ball 0 r) ↔ ∀ n,
      (∫ x, w x * Δ (φ n) x) ≤ ∫ x, φ n x ∂(S.μ ω)) :
    NullMeasurableSet {ω | w ∈ supersolutions (S.μ ω) r z t} S.P := by
  classical
  by_cases hc : ContinuousOn w (closedBall 0 r)
  · by_cases ho : ∀ x ∈ closedBall (0 : ℂ) r, x ≠ z →
        -t * greenFunction (ball 0 r) z x ≤ w x
    · have heq : {ω | w ∈ supersolutions (S.μ ω) r z t} =
          {ω | LaplacianLE w (S.μ ω) (ball 0 r)} := by
        ext ω
        change (ContinuousOn w (closedBall 0 r) ∧ LaplacianLE w (S.μ ω) (ball 0 r) ∧
          (∀ x ∈ closedBall (0 : ℂ) r, x ≠ z →
            -t * greenFunction (ball 0 r) z x ≤ w x)) ↔ _
        exact ⟨fun h => h.2.1, fun h => ⟨hc, h, ho⟩⟩
      rw [heq]
      exact hS.nullMeasurableSet_laplacianLE_of_countable_tests w _ φ hφ hdet
    · have heq : {ω | w ∈ supersolutions (S.μ ω) r z t} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro h
        exact ho h.2.2
      rw [heq]
      exact MeasurableSet.empty.nullMeasurableSet
  · have heq : {ω | w ∈ supersolutions (S.μ ω) r z t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h
      exact hc h.1
    rw [heq]
    exact MeasurableSet.empty.nullMeasurableSet

/-- If candidates have null-measurable admissibility and measurable values,
and form a pointwise determining family, their infimum is a.e. measurable. -/
theorem aemeasurable_leastSupersolution_of_countable_candidates
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (r t : ℝ) (z x : ℂ) (w : ℕ → Ω → ℂ → ℝ)
    (hmem : ∀ n, NullMeasurableSet {ω | w n ω ∈ supersolutions (μ ω) r z t} P)
    (hval : ∀ n, AEMeasurable (fun ω => w n ω x) P)
    (happrox : ∀ᵐ ω ∂P, ∀ q : ℝ,
      leastSupersolution (μ ω) r z t x < q ↔
        ∃ n, w n ω ∈ supersolutions (μ ω) r z t ∧ w n ω x < q) :
    AEMeasurable (fun ω => leastSupersolution (μ ω) r z t x) P := by
  have hm : @Measurable (NullMeasurableSpace Ω P) ℝ _ _
      (fun ω => leastSupersolution (μ ω) r z t x) := by
    apply measurable_of_Iio
    intro q
    have h : NullMeasurableSet {ω | ∃ n,
        w n ω ∈ supersolutions (μ ω) r z t ∧ w n ω x < q} P := by
      have hs : ∀ n, NullMeasurableSet {ω |
          w n ω ∈ supersolutions (μ ω) r z t ∧ w n ω x < q} P := by
        intro n
        exact (hmem n).inter (nullMeasurableSet_lt (hval n) aemeasurable_const)
      convert NullMeasurableSet.iUnion hs using 1
      ext ω
      simp
    apply h.congr
    filter_upwards [happrox] with ω hω
    exact propext (hω q).symm
  exact (show NullMeasurable (fun ω => leastSupersolution (μ ω) r z t x) P from hm).aemeasurable

end MatedCRT
