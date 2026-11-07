import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GoodEventMeshModulus
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.MeasurableOscillation
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.EventualAgreementBounds

/-! # Rescaled moduli under local agreement on good events -/

namespace MatedCRT

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- A prepared compactness modulus for a measurable vertex field transfers to
any field agreeing with it locally on events whose complements vanish in
probability. No measurability of the original field is needed. -/
theorem MatedCRTEnv.IsValid.rescale_modulus_of_good_event_compactness
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (D K : Set ℂ) (hKD : K ⊆ D) (hK : IsCompact K)
    (F G : ℝ → Ω → ℤ → ℝ) (E : ℝ → Set Ω)
    (hEq : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P, ω ∈ E ε →
      ∀ a ∈ cellVertices ε (S.η ω) D, F ε ω a = G ε ω a)
    (hG : ∀ ε, 0 < ε → ∀ a, Measurable[S.envSigma] fun ω => G ε ω a)
    (hcompact : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ I : Ω → ℕ → ℕ,
      (∀ n, Measurable[S.envSigma] fun ω => I ω n) → (∀ ω n, n ≤ I ω n) →
      ∀ᵐ ω ∂S.P, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ u : ℂ → ℝ,
        ContinuousOn u K ∧ TendstoUniformlyOn
          (fun k => rescale (S.mε (ε (φ (ψ (I ω (θ k))))))
            (ε (φ (ψ (I ω (θ k))))) (S.η ω)
            (G (ε (φ (ψ (I ω (θ k))))) ω)) u atTop K)
    (hbad : Tendsto (fun ε => S.P (E ε)ᶜ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (t : ℝ) (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e := by
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨δ, hδ, hmod⟩ := hS.rescale_modulus_of_prepared_random_compactness
    K hK G (fun ε hε => ⟨G ε, hG ε hε, Filter.Eventually.of_forall fun _ => rfl⟩)
    t ht hcompact he2
  have hsmall := ENNReal.tendsto_nhds_zero.1 hbad (e / 2) he2
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hmod, hsmall, self_mem_nhdsWithin] with ε hmodε hsmallε hε
  have heq := hS.ae_rescale_eqOn_of_cellVertices_on_event ε hε (E ε) D K hKD
    (F ε) (G ε) (hEq ε hε)
  calc
    _ ≤ S.P {ω | ∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧
        t < |rescale (S.mε ε) ε (S.η ω) (G ε ω) x -
          rescale (S.mε ε) ε (S.η ω) (G ε ω) y|} + S.P (E ε)ᶜ :=
      measure_oscillation_le_of_eqOn_good_event S.P (E ε) K _ _ heq δ t
    _ ≤ e / 2 + e / 2 := add_le_add hmodε hsmallε
    _ = e := ENNReal.add_halves e

/-- Eventual local agreement and random bounds give prepared compactness for
the measurable representative, with deterministic thinning preceding all
measurable random index choices. -/
theorem MatedCRTEnv.IsValid.prepared_compactness_of_good_event_bounds
    {𝒮 : SpaceFillingSLEModel} (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hD : Metric.ball z r ⊆ Metric.ball 0 ρ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (F v : Ω → ℕ → ℤ → ℝ) (hvm : ∀ n a, Measurable[S.envSigma] fun ω => v ω n a)
    (C : Ω → ℝ) (hCm : Measurable[S.envSigma] C) (hC : ∀ ω, 0 < C ω)
    (hEq : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      ∀ a ∈ cellVertices (ε n) (S.η ω) (Metric.ball z r), v ω n a = F ω n a)
    (hb : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε n) (S.η ω) (Metric.ball z r),
        |matedLaplacian (S.mult (ε n) ω) (F ω n) a| ≤ C ω) ∧
      (∀ a ∈ cellVertices (ε n) (S.η ω) (Metric.ball z r), |F ω n a| ≤ C ω / ε n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ I : Ω → ℕ → ℕ, (∀ n, Measurable[S.envSigma] fun ω => I ω n) →
      (∀ ω n, n ≤ I ω n) → ∃ θ : Ω → ℕ → ℕ,
      (∀ n, Measurable[S.envSigma] fun ω => θ ω n) ∧
      ∀ᵐ ω ∂S.P, StrictMono (θ ω) ∧ ∃ u : ℂ → ℝ,
        ContinuousOn u (Metric.ball z r) ∧ ∀ K : Set ℂ, IsCompact K →
        closure K ⊆ Metric.ball z r → TendstoUniformlyOn
          (fun n => rescale (S.mε (ε (φ (I ω (θ ω n)))))
            (ε (φ (I ω (θ ω n)))) (S.η ω) (v ω (φ (I ω (θ ω n))))) u atTop K := by
  have hbv := hS.ae_eventual_bounds_of_local_agreement hγ hγ2 hr ε hε F v C hEq hb
  exact GreenEnvironment.prepared_compactness_of_eventual_random_bounds_ae
    𝒮 h31 hγ hγ2 hρ hρ1 S hS (Metric.ball z r) hD Metric.isOpen_ball
    (Metric.isConnected_ball hr) ε hε hε0 v hvm C hCm hC hbv

end MatedCRT
