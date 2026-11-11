import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.ExitModulus
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.AeTightnessCompactness

/-!
# Lemma 3.7 along `2^{-n}`-dominated mesh sequences

The sequential criterion `asymptotic_modulus_of_mesh_sequences` (FilterModulus.lean) only needs mesh
sequences with `ε_n < 2^{-n}`: the bad meshes of the contradiction argument can be chosen that small. Such
sequences are polynomially summable, which is what the corrected Lemma 3.1 (N3) and the Borel-Cantelli
argument for the size bound of Step 1 need. This gives the interior convergence of Lemma 3.7, and with the
boundary layer (DiscreteBoundaryLayer.lean) Lemma 3.7 itself.
-/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- If every mesh sequence with `0 < ε_n < 2^{-n}` has an asymptotic modulus, then the modulus holds for the
full one-sided mesh limit. -/
theorem asymptotic_modulus_of_dyadic_mesh_sequences
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → ℝ → Set Ω)
    (hmono : ∀ δ δ' ε, δ ≤ δ' → E δ ε ⊆ E δ' ε)
    (hseq : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∀ e : ℝ≥0∞, 0 < e → ∃ δ : ℝ, 0 < δ ∧
        ∀ᶠ n in atTop, P (E δ (ε n)) ≤ e)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P (E δ ε) ≤ e := by
  classical
  by_contra hcontra
  have hbad : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε < (1 / 2 : ℝ) ^ n ∧
      e < P (E (1 / ((n : ℝ) + 1)) ε) := by
    intro n
    by_contra hnone
    apply hcontra
    refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (show (0 : ℝ) < (1 / 2 : ℝ) ^ n by positivity)] with ε hε
    intro hεpos
    change (0 : ℝ) < ε at hεpos
    have hεlt : ε < (1 / 2 : ℝ) ^ n := by
      have := hε
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hεpos] at this
      exact this
    exact le_of_not_gt (fun hgt => hnone ⟨ε, hεpos, hεlt, hgt⟩)
  choose ε hε using hbad
  obtain ⟨δ, hδ, hgood⟩ := hseq ε (fun n => ⟨(hε n).1, (hε n).2.1⟩) e he
  have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)).eventually (Iio_mem_nhds hδ)
  obtain ⟨n, hn, hn'⟩ := (hsmall.and hgood).exists
  have hcompare : P (E (1 / ((n : ℝ) + 1)) (ε n)) ≤ P (E δ (ε n)) :=
    measure_mono (hmono _ _ _ hn.le)
  exact (not_lt_of_ge (hcompare.trans hn')) (hε n).2.2

/-- Measurable event versions and random subsequential compactness along `2^{-n}`-dominated mesh sequences
give a full one-sided mesh modulus. -/
theorem mesh_modulus_of_dyadic_random_compactness_versions
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace α]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω)
    (K : Set α) (hK : IsCompact K) (F : ℝ → Ω → α → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hA : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, ∃ A : Set Ω,
      MeasurableSet[m] A ∧ @NullMeasurableSet Ω mΩ A P ∧
      ∀ᵐ ω ∂P, (ω ∈ A ↔ ∃ x ∈ K, ∃ y ∈ K,
        dist x y < δ ∧ t < |F ε ω x - F ε ω y|))
    (hcompact : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[m] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : α → ℝ,
        ContinuousOn u K ∧ TendstoUniformlyOn
          (fun k => F (ε (ψ (I ω (φ k)))) ω) u atTop K)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |F ε ω x - F ε ω y|} ≤ e := by
  let E : ℝ → ℝ → Set Ω := fun δ ε => {ω | ∃ x ∈ K, ∃ y ∈ K,
    dist x y < δ ∧ t < |F ε ω x - F ε ω y|}
  refine @asymptotic_modulus_of_dyadic_mesh_sequences Ω mΩ P E ?_ ?_ e he
  · intro δ δ' ε hδ ω hω
    obtain ⟨x, hx, y, hy, hxy, hbad⟩ := hω
    exact ⟨x, hx, y, hy, hxy.trans_le hδ, hbad⟩
  · intro ε hε e' he'
    let B : ℕ → ℕ → Set Ω := fun k n => E (1 / ((k : ℝ) + 1)) (ε n)
    have hmono : ∀ k l n, k ≤ l → B l n ⊆ B k n := by
      intro k l n hkl ω hω
      obtain ⟨x, hx, y, hy, hxy, hbad⟩ := hω
      have hden : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hscale : 1 / ((l : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
        apply one_div_le_one_div_of_le hden
        have hc : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
        linarith
      exact ⟨x, hx, y, hy, hxy.trans_le hscale, hbad⟩
    have hdiag : ∀ ψ : ℕ → ℕ, StrictMono ψ →
        Tendsto (fun k => P (B k (ψ k))) atTop (𝓝 0) := by
      intro ψ hψ
      refine @tendsto_oscillation_probability_of_random_compactness_versions Ω α mΩ _ P
        ‹IsFiniteMeasure P› m K hK (fun n => F (ε (ψ n))) t ht ?_ ?_
      · intro n
        exact hA (ε (ψ n)) (hε _).1 _
      · exact hcompact ε hε ψ hψ
    obtain ⟨k, hk⟩ := @exists_fixed_scale_of_diagonal_probabilities Ω mΩ P B hmono hdiag e' he'
    exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

/-- Random subsequential compactness of the rescaled exit times along `2^{-n}`-dominated mesh sequences
implies a probabilistic spatial modulus on a compact set. -/
theorem MatedCRTEnv.IsValid.exit_modulus_of_dyadic_random_compactness
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : IsOpen D ∨ IsClosed D) (K : Set ℂ) (hK : IsCompact K)
    (hcompact : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[S.envSigma] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂S.P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : ℂ → ℝ,
        ContinuousOn u K ∧ TendstoUniformlyOn
          (fun k => rescale (S.mε (ε (ψ (I ω (φ k))))) (ε (ψ (I ω (φ k)))) (S.η ω)
            (normExitTime (S.mult (ε (ψ (I ω (φ k)))) ω)
              (interiorCellVertices (ε (ψ (I ω (φ k)))) (S.η ω) D))) u atTop K)
    {t : ℝ} (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D)) x -
        rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) D)) y|} ≤ e := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply mesh_modulus_of_dyadic_random_compactness_versions S.P S.envSigma K hK _ t ht ?_ hcompact he
  intro ε hε δ
  obtain ⟨A, hAm, hAe⟩ := hS.exists_envSigma_measurable_exit_oscillation ε hε D hD K hK δ t
  exact ⟨A, hAm, hS.nullMeasurableSet_of_envSigma hAm, hAe⟩

/-- **Interior convergence in Lemma 3.7** (Steps 1-3 of the proof), from Lemmas 3.3, 3.5, 2.17, 2.18 and
Lemma 3.1 (corrected, almost-sure hypotheses). -/
theorem normalizedExitInterior_of_statements
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h35 : DiscreteDirichletProblemStmt 𝒮) (h217 : BoundedExitTimeRVStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hAe : DiscretePotentialTightnessAeStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r r' : ℝ} {z : ℂ} (hr : 0 < r) (hr' : r' < r)
    (hball : ball z r ⊆ ball 0 ρ) :
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))))
      (normalizedExitGreenPotential S r z) (closedBall z r') := by
  apply normalizedExitInterior_of_discrete_modulus 𝒮 h33 h35 h217 hγ hγ2 hρ hρ1
    S hS hr hr' hball
  intro t ht e he
  exact hS.exit_modulus_of_dyadic_random_compactness (ball z r) (Or.inl isOpen_ball)
    (closedBall z r') (isCompact_closedBall _ _)
    (exit_compactness_dyadic_of_statements 𝒮 h218 h217 hAe hγ hγ2 hρ hρ1 S hS hr hr' hball) ht he

/-- The interior step of Lemma 3.7 holds, given Lemma 2.18 and Lemma 3.1 (corrected, almost-sure
hypotheses); its own inputs supply Lemmas 3.3, 3.5 and 2.17. -/
theorem normalizedExitInteriorStep_of_statements (𝒮 : SpaceFillingSLEModel)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hAe : DiscretePotentialTightnessAeStep 𝒮) :
    NormalizedExitInteriorStep 𝒮 := by
  intro h33 _ _ h35 _ _ h217 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball r' _ hr'
  exact normalizedExitInterior_of_statements 𝒮 h33 h35 h217 h218 hAe hγ hγ2 hρ hρ1 S hS hr hr' hball

/-- **Lemma 3.7** from Lemmas 3.3, 3.5, 2.17, 2.18 and Lemma 3.1 (corrected, almost-sure hypotheses,
`DiscretePotentialTightnessAeStep`). Lemma 3.2 is not used. -/
theorem convergenceNormalizedExitTime_of_statements (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hAe : DiscretePotentialTightnessAeStep 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball
  refine ⟨normalizedExitGreenPotential S r z,
    normalizedExitPotentialStep_of_boundedExitTime 𝒮 h217 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball, ?_⟩
  apply uniformOn_closedBall_of_interior_boundary
  · intro r' _ hr'
    exact normalizedExitInterior_of_statements 𝒮 h33 h35 h217 h218 hAe hγ hγ2 hρ hρ1 S hS hr hr' hball
  · intro δ hδ e he
    have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
    obtain ⟨r₁, hr₁0, hr₁r, h₁⟩ := discreteExitBoundary_of_statements 𝒮 h33 h35 h217
      hγ hγ2 hρ hρ1 S hS hr hball hδ he2
    obtain ⟨r₂, hr₂0, hr₂r, h₂⟩ := normalizedExitGreenPotential_boundary_small_of_statements
      𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball hδ he2
    refine ⟨max r₁ r₂, lt_of_lt_of_le hr₁0 (le_max_left _ _), max_lt hr₁r hr₂r, ?_⟩
    filter_upwards [h₁] with ε hε
    calc
      S.P {ω | ∃ x ∈ closedBall z r \ closedBall z (max r₁ r₂),
          δ < |rescale (S.mε ε) ε (S.η ω)
            (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x| ∨
          δ < |normalizedExitGreenPotential S r z ω x|} ≤
        S.P ({ω | ∃ x ∈ closedBall z r \ closedBall z r₁,
          δ < |rescale (S.mε ε) ε (S.η ω)
            (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x|} ∪
        {ω | ∃ x ∈ closedBall z r \ closedBall z r₂,
          δ < |normalizedExitGreenPotential S r z ω x|}) := by
            apply measure_mono
            rintro ω ⟨x, ⟨hx, hxout⟩, h⟩
            have hx₁ : x ∉ closedBall z r₁ := fun hx' =>
              hxout (closedBall_subset_closedBall (le_max_left _ _) hx')
            have hx₂ : x ∉ closedBall z r₂ := fun hx' =>
              hxout (closedBall_subset_closedBall (le_max_right _ _) hx')
            rcases h with h | h
            · exact Or.inl ⟨x, ⟨hx, hx₁⟩, h⟩
            · exact Or.inr ⟨x, ⟨hx, hx₂⟩, h⟩
      _ ≤ _ := measure_union_le _ _
      _ ≤ e / 2 + e / 2 := add_le_add hε h₂
      _ = e := ENNReal.add_halves e

end MatedCRT
