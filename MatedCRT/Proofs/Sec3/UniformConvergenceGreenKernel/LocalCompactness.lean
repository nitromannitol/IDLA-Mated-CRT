import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.SequenceClipping

/-! # Local compactness from eventually harmonic data -/

namespace MatedCRT.GreenEnvironment

open Set Filter MeasureTheory Topology Metric

/-- The tightness theorem applies to data whose harmonicity and size estimates
hold eventually almost surely, provided the graph and cell sets are measurable
with respect to the field-and-curve sigma-algebra. -/
theorem compactness_of_eventual_estimates (𝒮 : SpaceFillingSLEModel)
    (h31 : DiscretePotentialTightnessStmt 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDc : IsConnected D)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (u : Ω → ℕ → ℤ → ℝ) (hu : ∀ n a, Measurable[S.envSigma] fun ω => u ω n a)
    (K : ℝ) (hK : 0 < K)
    (hM : ∀ n j k, Measurable[S.envSigma] fun ω => S.mult (ε n) ω j k)
    (hV : ∀ n, Measurable[S.envSigma] fun ω => cellVertices (ε n) (S.η ω) D)
    (hW : ∀ n, Measurable[S.envSigma] fun ω => interiorCellVertices (ε n) (S.η ω) D)
    (hgood : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (ε n) (S.η ω) D,
        matedLaplacian (S.mult (ε n) ω) (u ω n) a = 0) ∧
      (∀ a ∈ cellVertices (ε n) (S.η ω) D, |u ω n a| ≤ K / ε n)) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
        ∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
          TendstoUniformlyOn (fun k => rescale (S.mε (ε (Φ ω k))) (ε (Φ ω k))
            (S.η ω) (u ω (Φ ω k))) ubar atTop O := by
  classical
  have hclip : ∀ n, ∃ v : Ω → ℤ → ℝ,
      (∀ a, Measurable[S.envSigma] fun ω => v ω a) ∧
      (∀ ω a, a ∈ interiorCellVertices (ε n) (S.η ω) D →
        matedLaplacian (S.mult (ε n) ω) (v ω) a = 0) ∧
      (∀ ω a, a ∈ cellVertices (ε n) (S.η ω) D → |v ω a| ≤ K / ε n) ∧
      ∀ ω, (∀ a ∈ interiorCellVertices (ε n) (S.η ω) D,
          matedLaplacian (S.mult (ε n) ω) (u ω n) a = 0) →
        (∀ a ∈ cellVertices (ε n) (S.η ω) D, |u ω n a| ≤ K / ε n) →
          v ω = u ω n := by
    intro n
    let M : Ω → ℤ → ℤ → ℕ := fun ω => S.mult (ε n) ω
    let V : Ω → Set ℤ := fun ω => cellVertices (ε n) (S.η ω) D
    let W : Ω → Set ℤ := fun ω => interiorCellVertices (ε n) (S.η ω) D
    let : MeasurableSpace Ω := S.envSigma
    exact exists_measurable_clipped_harmonic
      M (hM n) V W (hV n) (hW n)
      (fun ω => u ω n) (hu n) K (ε n) hK.le (hε n)
  choose v hvm hvl hvb hve using hclip
  let U : Ω → ℕ → ℤ → ℝ := fun ω n => v n ω
  obtain ⟨Φ, hΦm, hΦ⟩ := h31 γ hγ hγ2 ρ hρ hρ1 Ω S hS D hD hDc
    (fun _ n => ε n) U (fun _ => K) (fun _ => measurable_const)
    (fun _ n => hε n) (fun _ => hεlim) hvm measurable_const (fun _ => hK)
    (fun ω n a ha => by rw [hvl n ω a ha, abs_zero]; exact hK.le)
    (fun ω n a ha => hvb n ω a ha)
  refine ⟨Φ, hΦm, ?_⟩
  filter_upwards [hΦ, hgood] with ω hω hgoodω
  obtain ⟨hmono, ubar, hcont, hconv, -⟩ := hω
  refine ⟨hmono, ubar, hcont, ?_⟩
  intro O hOc hOD
  apply (hconv O hOc hOD).congr
  filter_upwards [hmono.tendsto_atTop.eventually hgoodω] with k hk
  have heq : U ω (Φ ω k) = u ω (Φ ω k) := hve (Φ ω k) ω hk.1 hk.2
  intro x hx
  rw [heq]

end MatedCRT.GreenEnvironment
