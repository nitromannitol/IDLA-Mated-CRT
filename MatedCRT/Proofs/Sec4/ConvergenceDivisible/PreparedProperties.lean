import MatedCRT.Draft.Section4PropertiesPrepared
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.Prepared

/-! Theorem 4.1 from the fixed-time prepared formulation of Lemma 4.8. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped Uniformity

/-- Prepared compactness and every-limit identification imply pathwise convergence. -/
theorem convergenceDivisible_pathwise_of_prepared_properties (𝒮 : SpaceFillingSLEModel)
    (h48 : SubsequentialPropertiesPreparedStmt 𝒮) (hu : ObstacleLimitUniquenessStep 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t : ℝ) (ht : 0 < t) (εs : ℕ → ℝ) (hε : ∀ n, 0 < εs n)
    (hε0 : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      t < clusterExitTime (Λ ω) ρ →
      TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t (εs (φ n)) ω)
        (fun x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) atTop (closedBall 0 ρ) := by
  obtain ⟨φ, hφ, hp⟩ := h48 γ hγ hγ' ρ hρ hρ' Ω S hS t ht εs hε hε0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hp, hu γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ] with ω hp hu
  intro hT
  apply tendstoUniformlyOn_of_subsequence
  intro ψ hψ
  obtain ⟨ζ, hζ, w, hw, hconv⟩ := hp.1 ψ hψ
  have hprops := hp.2 w ⟨hw, ψ ∘ ζ, hψ.comp hζ, hconv⟩
  have heq := hu t ht hT w hw hprops.1 hprops.2.1 hprops.2.2.1 hprops.2.2.2
  exact ⟨ζ, hζ, hconv.congr_right heq⟩

/-- Theorem 4.1 from the prepared Lemma 4.8 and existing uniqueness and
convergence-event measurability inputs. -/
theorem convergenceDivisible_of_prepared_properties (𝒮 : SpaceFillingSLEModel)
    (h48 : SubsequentialPropertiesPreparedStmt 𝒮)
    (hu : ObstacleLimitUniquenessStep 𝒮) (hm : ConvergenceDivisibleEventMeasurableStep 𝒮) :
    ConvergenceDivisibleStmt 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ t ht δ hδ
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply tendsto_measure_zero_of_subsequence S.P
  · intro ε hε
    exact hm γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ t δ ε ht hδ hε
  · intro εs hε hε0
    obtain ⟨φ, hφ, hφae⟩ := convergenceDivisible_pathwise_of_prepared_properties 𝒮 h48 hu
      γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ t ht εs hε hε0
    refine ⟨φ, hφ, ?_⟩
    filter_upwards [hφae] with ω hω
    by_cases hT : t < clusterExitTime (Λ ω) ρ
    · have hconv := hω hT
      have hU : {p : ℝ × ℝ | dist p.1 p.2 < δ} ∈ 𝓤 ℝ :=
        Metric.mem_uniformity_dist.mpr ⟨δ, hδ, fun _ _ h => h⟩
      filter_upwards [hconv _ hU] with n hn
      rintro ⟨_, x, hx, hbad⟩
      have hh := hn x (ball_subset_closedBall hx)
      have : |rescaledMatedLeastSupersolution S ρ t (εs (φ n)) ω x -
          S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x| < δ := by
        simpa [Real.dist_eq, abs_sub_comm] using hh
      exact (not_lt_of_ge this.le) hbad
    · exact Filter.Eventually.of_forall fun _ he => hT he.1

end MatedCRT
