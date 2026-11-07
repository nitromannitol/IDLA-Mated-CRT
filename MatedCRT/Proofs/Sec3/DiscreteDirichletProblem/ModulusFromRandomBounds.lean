import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.PreparedRandomBounds
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.MeasurableOscillation

/-! Prepared moduli for measurable functions with eventual potential bounds. -/

namespace MatedCRT

open Set MeasureTheory Topology Metric Filter
open scoped ENNReal

/-- After deterministic thinning, eventual bounds for the Laplacian and size of vertex data with measurable versions by a measurable random constant imply
    an asymptotic modulus in probability on compact subsets. -/
theorem MatedCRTEnv.IsValid.rescale_modulus_of_eventual_random_bounds
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hS : S.IsValid 𝒮 γ)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDo : IsOpen D) (hDc : IsConnected D)
    (K : Set ℂ) (hK : IsCompact K) (hKD : closure K ⊆ D)
    (F : ℝ → Ω → ℤ → ℝ)
    (hF : ∀ ε, 0 < ε → ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧ ∀ᵐ ω ∂S.P, v ω = F ε ω)
    (hgood : ∀ ε : ℕ → ℝ, (∀ n, 0 < ε n ∧ ε n < (1 / 2) ^ n) →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ C : Ω → ℝ, Measurable[S.envSigma] C ∧ (∀ ω, 0 < C ω) ∧
      ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        (∀ a ∈ interiorCellVertices (ε (τ n)) (S.η ω) D,
          |matedLaplacian (S.mult (ε (τ n)) ω) (F (ε (τ n)) ω) a| ≤ C ω) ∧
        (∀ a ∈ cellVertices (ε (τ n)) (S.η ω) D, |F (ε (τ n)) ω a| ≤ C ω / ε (τ n)))
    (t : ℝ) (ht : 0 < t) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ x ∈ K, ∃ y ∈ K,
      dist x y < δ ∧ t < |rescale (S.mε ε) ε (S.η ω) (F ε ω) x -
        rescale (S.mε ε) ε (S.η ω) (F ε ω) y|} ≤ e := by
  apply hS.rescale_modulus_of_prepared_random_compactness K hK F ?_ t ht ?_ he
  · exact hF
  · intro ε hε
    have hε0 : Tendsto ε atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (show Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) from
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      · intro n; exact (hε n).1.le
      · intro n; exact (hε n).2.le
    obtain ⟨τ, hτ, C, hCm, hC, hb⟩ := hgood ε hε
    choose v hvm hv using fun n => hF (ε (τ n)) (hε (τ n)).1
    have hall : ∀ᵐ ω ∂S.P, ∀ n, v n ω = F (ε (τ n)) ω := ae_all_iff.mpr hv
    have hbv : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
        (∀ a ∈ interiorCellVertices (ε (τ n)) (S.η ω) D,
          |matedLaplacian (S.mult (ε (τ n)) ω) (v n ω) a| ≤ C ω) ∧
        (∀ a ∈ cellVertices (ε (τ n)) (S.η ω) D, |v n ω a| ≤ C ω / ε (τ n)) := by
      filter_upwards [hall, hb] with ω hω hbω
      filter_upwards [hbω] with n hn
      simpa only [hω n] using hn
    obtain ⟨φ, hφ, hcompact⟩ :=
      GreenEnvironment.prepared_compactness_of_eventual_random_bounds_ae
        𝒮 h31 hγ hγ2 hρ hρ1 S hS D hD hDo hDc (ε ∘ τ) (fun n => (hε (τ n)).1) (hε0.comp hτ.tendsto_atTop)
        (fun ω n => v n ω) hvm C hCm hC hbv
    refine ⟨τ ∘ φ, hτ.comp hφ, ?_⟩
    intro ψ hψ I hIm hI
    let J : Ω → ℕ → ℕ := fun ω n => ψ (I ω n)
    have hJm : ∀ n, Measurable[S.envSigma] fun ω => J ω n := by
      intro n
      let : MeasurableSpace Ω := S.envSigma
      exact (measurable_from_nat (f := ψ)).comp (hIm n)
    have hJ : ∀ ω n, n ≤ J ω n := fun ω n => (hI ω n).trans (hψ.id_le _)
    obtain ⟨θ, hθm, hθ⟩ := hcompact J hJm hJ
    filter_upwards [hθ, hall] with ω hω hveq
    obtain ⟨hm, u, hu, hlocal⟩ := hω
    refine ⟨θ ω, hm, u, hu.mono (subset_closure.trans hKD), ?_⟩
    simpa only [hveq, J, Function.comp_apply] using hlocal K hK hKD

end MatedCRT
