import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedProxyDiagonal
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.PreparedFullSelection
import MatedCRT.Steps.Sec3.DiscretePotentialTightnessPrepared

/-! Common-event vertex moduli for the corrected proof of Lemma 3.1. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- Deterministic preparation yields the interior estimate and conditional
boundary estimate on one event, uniformly over admissible families, as in the
corrected proof of Lemma 3.1, paper lines 1031–1135. -/
def PreparedTightnessVertexModuliStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ e : ℕ → ℝ, (∀ n, 0 < e n) → Tendsto e atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ A : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ A) ∧
    ∀ (D : ℕ → Set ℂ), (∀ j, D j ⊆ ball 0 ρ ∧ IsOpen (D j) ∧ IsConnected (D j)) →
    ∀ (E : Ω → ℕ → ℝ) (u : ℕ → Ω → ℕ → ℤ → ℝ) (C : ℕ → Ω → ℝ),
      (∀ n, Measurable[S.envSigma] fun ω => E ω n) →
      (∀ ω n, E ω n ∈ range (e ∘ φ)) → (∀ ω, Tendsto (E ω) atTop (𝓝 0)) →
      (∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a) →
      (∀ j, Measurable[S.envSigma] (C j)) →
      ∀ ω ∈ A, PreparedTightnessBounds S D E u C ω → ∀ j,
        (∀ K, IsCompact K → K ⊆ D j →
          IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u j ω) K) ∧
        (PreparedHolderBoundary S (D j) E (u j) ω →
          IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u j ω)
            (closure (D j)))

/-- The common-event vertex moduli and the normalization of the random walk
imply the pathwise simultaneous extraction of corrected Lemma 3.1. -/
theorem preparedTightnessPathwiseStep_of_vertexModuli {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (hmod : PreparedTightnessVertexModuliStep 𝒮) :
    PreparedTightnessPathwiseStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS e he he0
  obtain ⟨φ, hφ, A, hA, hmodA⟩ := hmod γ hγ hγ2 ρ hρ hρ1 Ω S hS e he he0
  obtain ⟨Cm, hCm1, hmS⟩ := hm γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmε⟩ := hmS Ω S hS
  have hCm : 0 < Cm := one_pos.trans hCm1
  refine ⟨φ, hφ, {ω | ω ∈ A ∧ IsAreaParametrized (S.μ ω) (S.η ω) ∧
    Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)}, ?_, ?_⟩
  · filter_upwards [hA, hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω hω hη hp
    exact ⟨hω, hη, hp⟩
  · intro D hD E u C hEm hEr hE0 hum hCmeas ω hω hb
    have hEpos : ∀ n, 0 < E ω n := fun n => by
      obtain ⟨j, hj⟩ := hEr ω n
      rw [← hj]
      exact he (φ j)
    have hmev : ∀ᶠ n in atTop, 0 ≤ (S.mε (E ω n))⁻¹ ∧
        (S.mε (E ω n))⁻¹ ≤ Cm * E ω n := by
      filter_upwards [(hE0 ω).eventually (gt_mem_nhds hε₀)] with n hn
      have h := (hmε (E ω n) (hEpos n) hn).1
      have hpos : 0 < Cm⁻¹ * (E ω n)⁻¹ := mul_pos (inv_pos.2 hCm) (inv_pos.2 (hEpos n))
      refine ⟨inv_nonneg.2 (hpos.le.trans h), ?_⟩
      have h2 := inv_anti₀ hpos h
      rwa [mul_inv, inv_inv, inv_inv] at h2
    have hbounds : ∀ j c, ∃ M, ∀ᶠ n in atTop,
        |Tightness.proxyCoord (E ω) (S.η ω) (D j) (fun n => S.mε (E ω n))
          (u j ω) n c| ≤ M := by
      intro j c
      refine ⟨Cm * C j ω, ?_⟩
      filter_upwards [hmev] with n hn
      refine Tightness.abs_proxyValue_le (mul_pos hCm (hb j).1).le fun k hk => ?_
      have hkD : k ∈ cellVertices (E ω n) (S.η ω) (D j) :=
        Tightness.mem_cellVertices_of_vertexPoint_mem (hEpos n) hk
      show |(S.mε (E ω n))⁻¹ * u j ω n k| ≤ Cm * C j ω
      rw [abs_mul, abs_of_nonneg hn.1]
      calc (S.mε (E ω n))⁻¹ * |u j ω n k| ≤ (Cm * E ω n) * (C j ω / E ω n) :=
            mul_le_mul hn.2 ((hb j).2.2 n k hkD) (abs_nonneg _) (mul_pos hCm (hEpos n)).le
        _ = Cm * C j ω * (E ω n * (E ω n)⁻¹) := by ring
        _ = Cm * C j ω := by rw [mul_inv_cancel₀ (hEpos n).ne', mul_one]
    have hmodω := hmodA D hD E u C hEm hEr hE0 hum hCmeas ω hω.1 hb
    obtain ⟨ψ, hψ, hlim⟩ := Tightness.simultaneous_tightness_of_proxy_bounds
      (fun j => (hD j).2.1) (fun j => isBounded_ball.subset (hD j).1)
      hω.2.1.1 hω.2.2 hω.2.1.2.2.1 hEpos (hE0 ω) hCm hmev
      (fun j => (hmodω j).1) (fun j => PreparedHolderBoundary S (D j) E (u j) ω)
      (fun j => (hmodω j).2) hbounds
    exact ⟨ψ, hψ, hlim⟩

/-- The common-event vertex moduli imply the prepared, measurably selected
form of Lemma 3.1 with the normalization input. -/
theorem discretePotentialTightnessPrepared_of_vertexModuli {𝒮 : SpaceFillingSLEModel}
    (hm : MepsScalingInput 𝒮) (hmod : PreparedTightnessVertexModuliStep 𝒮) :
    DiscretePotentialTightnessPreparedStmt 𝒮 :=
  discretePotentialTightnessPrepared_of_pathwise 𝒮
    (preparedTightnessPathwiseStep_of_vertexModuli hm hmod)

end MatedCRT

#print axioms MatedCRT.discretePotentialTightnessPrepared_of_vertexModuli
