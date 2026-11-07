import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedBoundedLaplacian
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.MeasurableOscillation

/-! Prepared moduli for measurable functions with eventual potential bounds. -/

namespace MatedCRT

open Set MeasureTheory Topology Metric Filter
open scoped ENNReal

/-- Eventual bounds for the Laplacian and size of measurable vertex data imply
    an asymptotic modulus in probability on compact subsets. -/
theorem MatedCRTEnv.IsValid.rescale_modulus_of_eventual_bounds
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hS : S.IsValid 𝒮 γ)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDo : IsOpen D) (hDc : IsConnected D)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ D)
    (F : ℝ → Ω → ℤ → ℝ) (hFm : ∀ ε a, Measurable[S.envSigma] fun ω => F ε ω a)
    (C : ℝ) (hC : 0 < C)
    (hgood : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        (∀ a ∈ interiorCellVertices (ε n) (S.η ω) D,
          |matedLaplacian (S.mult (ε n) ω) (F (ε n) ω) a| ≤ C) ∧
        (∀ a ∈ cellVertices (ε n) (S.η ω) D, |F (ε n) ω a| ≤ C / ε n))
    (t : ℝ) (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e := by
  apply hS.rescale_modulus_of_prepared_random_compactness K hK F ?_ t ht ?_ he
  · intro ε hε
    exact ⟨F ε, hFm ε, Filter.Eventually.of_forall fun _ => rfl⟩
  · intro ε hε
    have hε0 : Tendsto ε atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (show Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) from
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      · intro n; exact (hε n).1.le
      · intro n; exact (hε n).2.le
    obtain ⟨φ, hφ, hcompact⟩ :=
      GreenEnvironment.prepared_compactness_of_eventual_bounded_laplacian_random_ae
        𝒮 h31 hγ hγ2 hρ hρ1 S hS D hD hDo hDc ε (fun n => (hε n).1) hε0
        (fun ω n => F (ε n) ω) (fun n a => hFm (ε n) a) C hC (hgood ε hε)
    refine ⟨φ, hφ, ?_⟩
    intro ψ hψ I hIm hI
    let J : Ω → ℕ → ℕ := fun ω n => ψ (I ω n)
    have hJm : ∀ n, Measurable[S.envSigma] fun ω => J ω n := by
      intro n
      let : MeasurableSpace Ω := S.envSigma
      exact (measurable_from_nat (f := ψ)).comp (hIm n)
    have hJ : ∀ ω n, n ≤ J ω n := fun ω n => (hI ω n).trans (hψ.id_le _)
    obtain ⟨θ, hθm, hθ⟩ := hcompact J hJm hJ
    filter_upwards [hθ] with ω hω
    obtain ⟨hm, u, hu, hlocal⟩ := hω
    exact ⟨θ ω, hm, u, hu.mono (subset_closure.trans hKD), hlocal K hK hKD⟩

end MatedCRT
