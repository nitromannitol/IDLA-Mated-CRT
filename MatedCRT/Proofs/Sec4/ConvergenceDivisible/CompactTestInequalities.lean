import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CountableDeterminingTests
import HarmonicBalls.Proofs.Potential.Fundamental
import HarmonicBalls.Proofs.Potential.GreenBall

/-! # Countable test inequalities on a ball -/

namespace MatedCRT

open Set MeasureTheory Metric Laplacian HarmonicBalls

/-- Nonnegative smooth tests supported in a Euclidean ball. -/
abbrev NonnegativeBallTest (r : ℝ) :=
  {φ : ℂ → ℝ // IsTestFunction (ball 0 r) φ ∧ 0 ≤ φ}

/-- A single countable family of nonnegative tests determines all weighted
integral inequalities on the closed ball, uniformly over finite measures and
continuous weights. -/
theorem exists_countable_nonnegative_ball_tests (r : ℝ) :
    ∃ C : Set (NonnegativeBallTest r), C.Countable ∧
      ∀ (μ ν : Measure (closedBall (0 : ℂ) r)),
        ∀ (_ : IsFiniteMeasure μ) (_ : IsFiniteMeasure ν),
        ∀ w : C(closedBall (0 : ℂ) r, ℝ),
        ((∀ φ ∈ C, (∫ x, w x * Δ φ.1 x ∂μ) ≤ ∫ x, φ.1 x ∂ν) ↔
          ∀ φ : NonnegativeBallTest r,
            (∫ x, w x * Δ φ.1 x ∂μ) ≤ ∫ x, φ.1 x ∂ν) := by
  let f : NonnegativeBallTest r → C(closedBall (0 : ℂ) r, ℝ) := fun φ =>
    ⟨fun x => φ.1 x, φ.2.1.1.continuous.comp continuous_subtype_val⟩
  let g : NonnegativeBallTest r → C(closedBall (0 : ℂ) r, ℝ) := fun φ =>
    ⟨fun x => Δ φ.1 x,
      (continuous_laplacian_of_contDiff (φ.2.1.1.of_le (by norm_cast))).comp
        continuous_subtype_val⟩
  obtain ⟨C, hCc, _, hC⟩ :=
    exists_countable_tests_determining_weighted_integrals Set.univ f g
  refine ⟨C, hCc, ?_⟩
  intro μ ν hμ hν w
  simpa only [mem_univ, true_implies, f, g, ContinuousMap.coe_mk] using hC μ ν hμ hν w

/-- A function supported in a measurable set has the same integral on that
set, viewed as a subtype, as on the ambient space. -/
theorem integral_subtype_of_support_subset
    {s : Set ℂ} (hs : MeasurableSet s) (μ : Measure ℂ) (f : ℂ → ℝ)
    (hf : Function.support f ⊆ s) :
    (∫ x : s, f x ∂(Measure.comap Subtype.val μ)) = ∫ x, f x ∂μ := by
  rw [integral_subtype_comap hs, ← integral_indicator hs, indicator_eq_self.2 hf]

/-- Nonnegative tests on a ball have a countable subfamily determining their
distributional inequalities for all continuous weights and locally finite
measures. -/
theorem exists_countable_ball_tests_determining_inequalities (r : ℝ) :
    ∃ C : Set (NonnegativeBallTest r), C.Countable ∧
      ∀ (μ : Measure ℂ), ∀ (_ : IsFiniteMeasureOnCompacts μ),
        ∀ w : ℂ → ℝ, ContinuousOn w (closedBall 0 r) →
        ((∀ φ ∈ C, (∫ x, w x * Δ φ.1 x) ≤ ∫ x, φ.1 x ∂μ) ↔
          ∀ φ : NonnegativeBallTest r, (∫ x, w x * Δ φ.1 x) ≤ ∫ x, φ.1 x ∂μ) := by
  obtain ⟨C, hCc, hC⟩ := exists_countable_nonnegative_ball_tests r
  refine ⟨C, hCc, ?_⟩
  intro μ hμ w hw
  let K := closedBall (0 : ℂ) r
  have hK : MeasurableSet K := isClosed_closedBall.measurableSet
  have hvol : IsFiniteMeasureOnCompacts (Measure.comap (Subtype.val : K → ℂ) volume) :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hK)
  have hmeasure : IsFiniteMeasureOnCompacts (Measure.comap (Subtype.val : K → ℂ) μ) :=
    IsFiniteMeasureOnCompacts.comap' μ continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hK)
  let W : C(K, ℝ) := ⟨fun x => w x, continuousOn_iff_continuous_domRestrict.mp hw⟩
  have htest (φ : NonnegativeBallTest r) : Function.support φ.1 ⊆ K :=
    (subset_tsupport φ.1).trans (φ.2.1.2.2.trans ball_subset_closedBall)
  have hlap (φ : NonnegativeBallTest r) : Function.support (Δ φ.1) ⊆ K :=
    (support_laplacian_subset φ.1).trans (φ.2.1.2.2.trans ball_subset_closedBall)
  have hmul (φ : NonnegativeBallTest r) : Function.support (fun x => w x * Δ φ.1 x) ⊆ K := by
    intro x hx
    apply hlap φ
    intro hzero
    apply hx
    simp [hzero]
  have hl (φ : NonnegativeBallTest r) :
      (∫ x : K, W x * Δ φ.1 x ∂(Measure.comap Subtype.val volume)) =
        ∫ x, w x * Δ φ.1 x :=
    integral_subtype_of_support_subset hK volume _ (hmul φ)
  have hr (φ : NonnegativeBallTest r) :
      (∫ x : K, φ.1 x ∂(Measure.comap Subtype.val μ)) = ∫ x, φ.1 x ∂μ :=
    integral_subtype_of_support_subset hK μ _ (htest φ)
  have hcriterion := hC (Measure.comap (Subtype.val : K → ℂ) volume)
    (Measure.comap (Subtype.val : K → ℂ) μ) (inferInstance) (inferInstance) W
  constructor
  · intro h φ
    have hcsub : ∀ φ ∈ C, (∫ x : K, W x * Δ φ.1 x ∂(Measure.comap Subtype.val volume)) ≤
        ∫ x : K, φ.1 x ∂(Measure.comap Subtype.val μ) := by
      intro φ hφ
      rw [hl φ, hr φ]
      exact h φ hφ
    have hres := hcriterion.mp hcsub φ
    rw [hl φ, hr φ] at hres
    exact hres
  · intro h φ hφ
    exact h φ

/-- The distributional Laplacian inequality for a continuous candidate on a
ball is determined by a countable sequence of nonnegative tests, uniformly
over measures finite on compact sets. -/
theorem exists_countable_ball_tests_for_laplacianLE (r : ℝ) :
    ∃ φ : ℕ → ℂ → ℝ,
      (∀ n, IsTestFunction (ball 0 r) (φ n) ∧ 0 ≤ φ n) ∧
      ∀ (μ : Measure ℂ), ∀ (_ : IsFiniteMeasureOnCompacts μ),
        ∀ w : ℂ → ℝ, ContinuousOn w (closedBall 0 r) →
        (LaplacianLE w μ (ball 0 r) ↔ ∀ n,
          (∫ x, w x * Δ (φ n) x) ≤ ∫ x, φ n x ∂μ) := by
  classical
  let zero : NonnegativeBallTest r := ⟨0, by
    refine ⟨⟨contDiff_const, HasCompactSupport.zero, ?_⟩, le_refl 0⟩
    simp⟩
  obtain ⟨C, hCc, hC⟩ := exists_countable_ball_tests_determining_inequalities r
  obtain ⟨seq, hseq⟩ := (hCc.insert zero).exists_eq_range ⟨zero, by simp⟩
  refine ⟨fun n => (seq n).1, fun n => (seq n).2, ?_⟩
  intro μ hμ w hw
  have hcriterion := hC μ hμ w hw
  have hlocal : LocallyIntegrableOn w (ball 0 r) :=
    (hw.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball
  constructor
  · intro h n
    exact h.2 (seq n).1 (seq n).2.1 (seq n).2.2
      ((seq n).2.1.1.continuous.integrable_of_hasCompactSupport (seq n).2.1.2.1)
  · intro h
    refine ⟨hlocal, ?_⟩
    intro ψ hψ hψpos hψint
    have hCtests : ∀ φ ∈ C, (∫ x, w x * Δ φ.1 x) ≤ ∫ x, φ.1 x ∂μ := by
      intro φ hφ
      have hm : φ ∈ range seq := hseq ▸ mem_insert_of_mem zero hφ
      obtain ⟨n, rfl⟩ := hm
      exact h n
    exact hcriterion.mp hCtests ⟨ψ, hψ, hψpos⟩

/-- Admissibility of a fixed continuum candidate is null measurable for the
LQG measure. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_continuum_supersolution
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (r t : ℝ) (z : ℂ) (w : ℂ → ℝ) :
    NullMeasurableSet {ω | w ∈ supersolutions (S.μ ω) r z t} S.P := by
  classical
  by_cases hw : ContinuousOn w (closedBall 0 r)
  · obtain ⟨φ, hφ, hdet⟩ := exists_countable_ball_tests_for_laplacianLE r
    apply hS.nullMeasurableSet_supersolution_of_countable_tests r t z w φ
      (fun n => ⟨(hφ n).1.1.continuous, (hφ n).1.2.1⟩)
    filter_upwards [hS.isLQGMeasure] with ω hω
    have := hω.isLocallyFiniteMeasure
    exact hdet (S.μ ω) inferInstance w hw
  · have heq : {ω | w ∈ supersolutions (S.μ ω) r z t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hw h.1
    rw [heq]
    exact MeasurableSet.empty.nullMeasurableSet

/-- The distributional inequality is null measurable for a jointly measurable
random field with almost surely continuous sample paths on the closed ball. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_random_laplacianLE
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (r : ℝ) (W : Ω × ℂ → ℝ) (hW : Measurable W)
    (hc : ∀ᵐ ω ∂S.P, ContinuousOn (fun x => W (ω, x)) (closedBall 0 r)) :
    NullMeasurableSet {ω | LaplacianLE (fun x => W (ω, x)) (S.μ ω) (ball 0 r)} S.P := by
  obtain ⟨φ, hφ, hdet⟩ := exists_countable_ball_tests_for_laplacianLE r
  have hi (n : ℕ) : Measurable (fun ω => ∫ x, W (ω, x) * Δ (φ n) x) := by
    have hΔ : Continuous (Δ (φ n)) :=
      continuous_laplacian_of_contDiff ((hφ n).1.1.of_le (by norm_cast))
    exact (hW.mul (hΔ.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have hevent : NullMeasurableSet {ω | ∀ n,
      (∫ x, W (ω, x) * Δ (φ n) x) ≤ ∫ x, φ n x ∂(S.μ ω)} S.P := by
    convert NullMeasurableSet.iInter (fun n => nullMeasurableSet_le (hi n).aemeasurable
      (hS.aemeasurable_lqg_integral (φ n) (hφ n).1.1.continuous (hφ n).1.2.1)) using 1
    ext ω
    simp
  apply hevent.congr
  filter_upwards [hc, hS.isLQGMeasure] with ω hω hμ
  have := hμ.isLocallyFiniteMeasure
  exact propext (hdet (S.μ ω) inferInstance (fun x => W (ω, x)) hω).symm

/-- A pointwise obstacle inequality on a separable spatial set is null
measurable when both sides are continuous there almost surely. -/
theorem nullMeasurableSet_continuous_obstacle
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (T : Set ℂ)
    (β : ℂ → ℝ) (hβ : ContinuousOn β T)
    (W : Ω × ℂ → ℝ) (hW : Measurable W)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun x => W (ω, x)) T) :
    NullMeasurableSet {ω | ∀ x ∈ T, β x ≤ W (ω, x)} P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense T
  have : Countable D := hDc.to_subtype
  have htest : NullMeasurableSet {ω | ∀ x : D, β x.1 ≤ W (ω, x.1)} P := by
    convert NullMeasurableSet.iInter (fun x : D => nullMeasurableSet_le
      (aemeasurable_const : AEMeasurable (fun _ : Ω => β x.1.1) P)
      (hW.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : Ω => x.1.1)))).aemeasurable) using 1
    ext ω
    simp
  apply htest.congr
  filter_upwards [hc] with ω hω
  apply propext
  constructor
  · intro h x hx
    have hβ' : Continuous (fun y : T => β y) := continuousOn_iff_continuous_domRestrict.mp hβ
    have hω' : Continuous (fun y : T => W (ω, y)) := continuousOn_iff_continuous_domRestrict.mp hω
    have hclosed : IsClosed {y : T | β y ≤ W (ω, y)} := isClosed_le hβ' hω'
    have hsub : D ⊆ {y : T | β y ≤ W (ω, y)} := fun y hy => h ⟨y, hy⟩
    exact closure_minimal hsub hclosed (hDd ⟨x, hx⟩)
  · intro h x
    exact h x.1.1 x.1.2

/-- A jointly measurable random continuous candidate is admissible for the
continuum obstacle problem on a null-measurable event. -/
theorem MatedCRTEnv.IsValid.nullMeasurableSet_random_continuum_supersolution
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (r t : ℝ) (z : ℂ) (hz : z ∈ ball 0 r)
    (W : Ω × ℂ → ℝ) (hW : Measurable W)
    (hc : ∀ᵐ ω ∂S.P, ContinuousOn (fun x => W (ω, x)) (closedBall 0 r)) :
    NullMeasurableSet {ω | (fun x => W (ω, x)) ∈ supersolutions (S.μ ω) r z t} S.P := by
  let T := closedBall (0 : ℂ) r \ {z}
  let β : ℂ → ℝ := fun x => -t * greenFunction (ball 0 r) z x
  have hβ : ContinuousOn β T := continuousOn_const.mul
    ((continuousOn_greenFunction_ball hz).mono (fun x hx => hx.2))
  have hcont : ∀ᵐ ω ∂S.P, ContinuousOn (fun x => W (ω, x)) T :=
    hc.mono fun _ hω => hω.mono sdiff_subset
  have hobs : NullMeasurableSet {ω | ∀ x ∈ closedBall (0 : ℂ) r, x ≠ z →
      β x ≤ W (ω, x)} S.P := by
    convert nullMeasurableSet_continuous_obstacle S.P T β hβ W hW hcont using 1
    ext ω
    simp [T, Set.mem_sdiff, Set.mem_singleton_iff]
  have h := (hS.nullMeasurableSet_random_laplacianLE r W hW hc).inter hobs
  apply h.congr
  filter_upwards [hc] with ω hω
  apply propext
  change (LaplacianLE (fun x => W (ω, x)) (S.μ ω) (ball 0 r) ∧
    (∀ x ∈ closedBall (0 : ℂ) r, x ≠ z → β x ≤ W (ω, x))) ↔ _
  exact ⟨fun h => ⟨hω, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

/-- A pointwise determining sequence of jointly measurable, almost surely
continuous candidates makes the continuum least supersolution measurable. -/
theorem MatedCRTEnv.IsValid.aemeasurable_leastSupersolution_of_measurable_candidates
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (r t : ℝ) (z x : ℂ) (hz : z ∈ ball 0 r)
    (W : ℕ → Ω × ℂ → ℝ) (hW : ∀ n, Measurable (W n))
    (hc : ∀ n, ∀ᵐ ω ∂S.P, ContinuousOn (fun y => W n (ω, y)) (closedBall 0 r))
    (happrox : ∀ᵐ ω ∂S.P, ∀ q : ℝ,
      leastSupersolution (S.μ ω) r z t x < q ↔
        ∃ n, (fun y => W n (ω, y)) ∈ supersolutions (S.μ ω) r z t ∧ W n (ω, x) < q) :
    AEMeasurable (fun ω => leastSupersolution (S.μ ω) r z t x) S.P := by
  apply aemeasurable_leastSupersolution_of_countable_candidates S.P S.μ r t z x
    (fun n ω y => W n (ω, y))
  · exact fun n => hS.nullMeasurableSet_random_continuum_supersolution r t z hz
      (W n) (hW n) (hc n)
  · intro n
    exact ((hW n).comp (measurable_id.prodMk measurable_const)).aemeasurable
  · exact happrox

end MatedCRT
