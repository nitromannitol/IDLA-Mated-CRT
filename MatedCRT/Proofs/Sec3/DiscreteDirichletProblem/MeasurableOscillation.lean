import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OscillationMeasurable
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedMeshModulus

/-! Environment-measurable oscillation events for rescaled discrete functions. -/

namespace MatedCRT

open Set MeasureTheory Topology Metric Filter
open scoped ENNReal

/-- A vertex function with an environment-measurable version has an
    environment-measurable oscillation event on every compact set. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_rescale_oscillation
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (hε : 0 < ε) (F : Ω → ℤ → ℝ)
    (v : Ω → ℤ → ℝ) (hvm : ∀ a, Measurable[S.envSigma] fun ω => v ω a)
    (hv : ∀ᵐ ω ∂S.P, v ω = F ω)
    (K : Set ℂ) (hK : IsCompact K) (δ t : ℝ) :
    ∃ A : Set Ω, MeasurableSet[S.envSigma] A ∧ ∀ᵐ ω ∂S.P,
      (ω ∈ A ↔ ∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧
        t < |rescale (S.mε ε) ε (S.η ω) (F ω) x -
          rescale (S.mε ε) ε (S.η ω) (F ω) y|) := by
  obtain ⟨η, hηm, hη⟩ := hS.exists_envSigma_measurable_curve
  let u : Ω → ℤ → ℝ := fun ω a => (S.mε ε)⁻¹ * v ω a
  have hum : ∀ a, Measurable[S.envSigma] fun ω => u ω a :=
    fun a => measurable_const.mul (hvm a)
  have hI : ∀ k : ℤ, (Icc (ε * (k - 1)) (ε * k)).Nonempty := by
    intro k
    exact ⟨ε * (k - 1), le_rfl, mul_le_mul_of_nonneg_left (by linarith) hε.le⟩
  let A : Set Ω := {ω | ∃ N a b : ℤ,
      (∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j) ∧
      t < |u ω a - u ω b| ∧
      ∃ x ∈ K, ∃ y ∈ K, x ∈ cell ε (η ω) a ∧ y ∈ cell ε (η ω) b ∧
        dist x y < δ ∧ (∀ j ∈ Finset.Ico N a, x ∉ cell ε (η ω) j) ∧
        (∀ j ∈ Finset.Ico N b, y ∉ cell ε (η ω) j)}
  refine ⟨A, ?_, ?_⟩
  · let : MeasurableSpace Ω := S.envSigma
    exact measurableSet_bounded_index_oscillation η hηm u hum ε δ t K hK hI
  · filter_upwards [hη, hv, hS.isAreaParametrized, hS.ae_tendsto_cocompact]
      with ω hηω hvω harea hp
    have hfin := Tightness.cellVertices_finite harea.1 hp hε hK.isBounded
    obtain ⟨N, hN⟩ := hfin.bddBelow
    have hbound : ∃ N : ℤ, ∀ j < N, ∀ x ∈ K, x ∉ cell ε (η ω) j := by
      refine ⟨N, ?_⟩
      intro j hj x hx hcell
      have hjN : N ≤ j := hN ⟨x, by simpa [hηω] using hcell, hx⟩
      exact (not_lt_of_ge hjN) hj
    have hsel : ∀ x ∈ K, x ∈ cell ε (η ω) (vertexOf ε (η ω) x) := by
      intro x hx
      rw [hηω]
      exact Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hε x
    have heq := bounded_index_oscillation_iff (η ω) (u ω) ε δ t K hbound hsel
    change (∃ N a b : ℤ, _) ↔ _
    rw [← heq]
    simp only [hηω, u, hvω, rescale]

/-- Measurable versions and prepared random compactness imply a full mesh
    modulus in probability for rescaled discrete functions. -/
theorem MatedCRTEnv.IsValid.rescale_modulus_of_prepared_random_compactness
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (K : Set ℂ) (hK : IsCompact K) (F : ℝ → Ω → ℤ → ℝ)
    (hF : ∀ ε, 0 < ε → ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧ ∀ᵐ ω ∂S.P, v ω = F ε ω)
    (t : ℝ) (ht : 0 < t)
    (hcompact : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[S.envSigma] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂S.P, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ u : ℂ → ℝ,
        ContinuousOn u K ∧ TendstoUniformlyOn
          (fun k => rescale (S.mε (ε (φ (ψ (I ω (θ k))))))
            (ε (φ (ψ (I ω (θ k))))) (S.η ω)
            (F (ε (φ (ψ (I ω (θ k))))) ω)) u atTop K)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e := by
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply mesh_modulus_of_prepared_random_compactness_versions S.P S.envSigma K hK _ t ht ?_ hcompact he
  intro ε hε δ
  obtain ⟨v, hvm, hv⟩ := hF ε hε
  obtain ⟨A, hAm, hAe⟩ := hS.exists_envSigma_measurable_rescale_oscillation ε hε _ v hvm hv K hK δ t
  exact ⟨A, hAm, hS.nullMeasurableSet_of_envSigma hAm, hAe⟩

end MatedCRT
