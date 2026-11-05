import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.AeTightnessCompactness
import MatedCRT.Steps.Sec3.ConvergenceNormalizedExitTime

/-! # Random subsequential compactness from the almost-sure form of Lemma 3.1

Along random scales `e (I ω n)` (with `I` measurable and `I ω n ≥ n`) inside polynomially summable
deterministic scales `e`, the corrected Lemma 3.1 with almost-sure hypotheses
(`DiscretePotentialTightnessAeStep`) gives a measurable random subsequence and a continuous limit for
measurable data whose harmonicity and size bounds hold eventually almost surely along `e`. -/

namespace MatedCRT.GreenEnvironment

open Set Filter MeasureTheory Topology Metric

/-- Random subsequential compactness of eventually harmonic, `ε⁻¹`-bounded measurable data. -/
theorem compactness_of_eventual_estimates_ae (𝒮 : SpaceFillingSLEModel)
    (hAe : DiscretePotentialTightnessAeStep 𝒮) {γ ρ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (D : Set ℂ) (hD : D ⊆ ball 0 ρ) (hDo : IsOpen D) (hDc : IsConnected D)
    (e : ℕ → ℝ) (he : IsPolySummableScales e)
    (u : Ω → ℕ → ℤ → ℝ) (hu : ∀ n a, Measurable[S.envSigma] fun ω => u ω n a)
    (K : ℝ) (hK : 0 < K)
    (hgood : ∀ᵐ ω ∂S.P, ∀ᶠ n in atTop,
      (∀ a ∈ interiorCellVertices (e n) (S.η ω) D,
        matedLaplacian (S.mult (e n) ω) (u ω n) a = 0) ∧
      (∀ a ∈ cellVertices (e n) (S.η ω) D, |u ω n a| ≤ K / e n))
    (I : Ω → ℕ → ℕ) (hIm : ∀ n, Measurable[S.envSigma] fun ω => I ω n)
    (hI : ∀ ω n, n ≤ I ω n) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
      ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
        ∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
          TendstoUniformlyOn (fun k => rescale (S.mε (e (I ω (Φ ω k)))) (e (I ω (Φ ω k)))
            (S.η ω) (u ω (I ω (Φ ω k)))) ubar atTop O := by
  have hItends : ∀ ω, Tendsto (I ω) atTop atTop := fun ω =>
    tendsto_atTop_mono (hI ω) tendsto_id
  have hEm : ∀ n, Measurable[S.envSigma] fun ω => e (I ω n) := fun n =>
    (measurable_of_countable e).comp (hIm n)
  have hUm : ∀ n a, Measurable[S.envSigma] fun ω => u ω (I ω n) a := by
    intro n a
    let : MeasurableSpace Ω := S.envSigma
    have h1 : Measurable fun p : Ω × ℕ => u p.1 p.2 a :=
      measurable_from_prod_countable_left fun m => hu m a
    exact h1.comp (measurable_id.prodMk (hIm n))
  exact hAe γ hγ hγ2 ρ hρ hρ1 Ω S hS D hD hDo hDc e he
    (fun ω n => e (I ω n)) (fun ω n => u ω (I ω n)) (fun _ => K) hEm
    (fun ω n => ⟨I ω n, rfl⟩) (fun ω => he.tendsto_zero.comp (hItends ω)) hUm
    measurable_const (fun _ => hK) (by
      filter_upwards [hgood] with ω hω
      exact ((hItends ω).eventually hω).mono fun n hn =>
        ⟨fun a ha => by rw [hn.1 a ha, abs_zero]; exact hK.le, hn.2⟩)

end MatedCRT.GreenEnvironment
