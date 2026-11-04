import MatedCRT.Proofs.Sec4.ConvergenceDivisible.Subsequence
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.Measure

/-!
# Theorem 4.1: subsequence reduction

This is the pathwise compactness and uniqueness part of the proof. The obstacle comparison
and the passage to outer probability remain separate steps.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal Uniformity

/-- The properties of Lemma 4.8 characterize the scaled least supersolution on the ball. -/
def ObstacleLimitUniquenessStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t → t < clusterExitTime (Λ ω) ρ → ∀ w : ℂ → ℝ,
    ContinuousOn w (closedBall 0 ρ) →
    (∀ x ∈ closedBall (0 : ℂ) ρ, w x ≤ 0 ∧
      (x ≠ 0 → -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x ≤ w x)) →
    LaplacianGE w 0 (ball 0 ρ) →
    LaplacianLE w (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) (ball 0 ρ) →
    HasLaplacian w (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) 0
      {x ∈ ball (0 : ℂ) ρ | x = 0 ∨ -t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x < w x} →
    EqOn w (fun x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) (closedBall 0 ρ)

/-- The bounds in Lemma 4.8 force the limit to vanish on the boundary of the ball. -/
theorem obstacleLimit_eq_zero_on_sphere {ρ t c : ℝ} (hρ : 0 < ρ) {w : ℂ → ℝ}
    (hbound : ∀ x ∈ closedBall (0 : ℂ) ρ, w x ≤ 0 ∧
      (x ≠ 0 → -t * c * greenFunction (ball 0 ρ) 0 x ≤ w x)) :
    ∀ x ∈ sphere (0 : ℂ) ρ, w x = 0 := by
  intro x hx
  have hxb : x ∉ ball (0 : ℂ) ρ := by
    intro h
    have hs : dist x (0 : ℂ) = ρ := mem_sphere.mp hx
    have hb : dist x (0 : ℂ) < ρ := mem_ball.mp h
    linarith
  have hx0 : x ≠ 0 := by
    intro heq
    subst x
    exact hxb (mem_ball_self hρ)
  obtain ⟨hle, hge⟩ := hbound x (sphere_subset_closedBall hx)
  have hzero := greenFunction_of_notMem_right hxb (0 : ℂ)
  have : 0 ≤ w x := by simpa [hzero] using hge hx0
  exact le_antisymm hle this

/-- Lemmas 4.6 and 4.8 and obstacle uniqueness imply pathwise uniform convergence along a
deterministic subsequence of every deterministic sequence of mesh sizes. -/
theorem convergenceDivisible_pathwise_of_steps (𝒮 : SpaceFillingSLEModel)
    (h48 : SubsequentialPropertiesStmt 𝒮) (h46 : SubsequentialConvergenceStmt 𝒮)
    (hu : ObstacleLimitUniquenessStep 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (εs : ℕ → ℝ) (hε : ∀ n, 0 < εs n) (hε0 : Tendsto εs atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ t : ℝ, 0 < t →
      t < clusterExitTime (Λ ω) ρ →
      TendstoUniformlyOn (fun n => rescaledMatedLeastSupersolution S ρ t (εs (φ n)) ω)
        (fun x => S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x) atTop (closedBall 0 ρ) := by
  obtain ⟨φ, hφ, hp⟩ := h48 γ hγ hγ' ρ hρ hρ' Ω S hS εs hε hε0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hp, (h46 γ hγ hγ' ρ hρ hρ' Ω S hS).1,
    hu γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ] with ω hp hc hu
  intro t ht hT
  apply tendstoUniformlyOn_of_subsequence
  intro ψ hψ
  have hseq : Tendsto (fun n => εs (φ (ψ n))) atTop (𝓝 0) :=
    hε0.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
  obtain ⟨ζ, hζ, w, hw, _, hconv⟩ :=
    hc t ht (fun n => εs (φ (ψ n))) (fun n => hε _) hseq
  have hprops := hp t ht w ⟨hw, ψ ∘ ζ, hψ.comp hζ, hconv⟩
  have heq := hu t ht hT w hw hprops.1 hprops.2.1 hprops.2.2.1 hprops.2.2.2
  exact ⟨ζ, hζ, hconv.congr_right heq⟩

/-- Null measurability of the error events in Theorem 4.1. -/
def ConvergenceDivisibleEventMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t δ ε : ℝ, 0 < t → 0 < δ → 0 < ε →
    NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ ball (0 : ℂ) ρ,
      δ < |rescaledMatedLeastSupersolution S ρ t ε ω x -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|} S.P

/-- Theorem 4.1 follows from subsequential compactness, obstacle uniqueness and null measurability
of its error events. -/
theorem convergenceDivisible_of_steps (𝒮 : SpaceFillingSLEModel)
    (h48 : SubsequentialPropertiesStmt 𝒮) (h46 : SubsequentialConvergenceStmt 𝒮)
    (hu : ObstacleLimitUniquenessStep 𝒮) (hm : ConvergenceDivisibleEventMeasurableStep 𝒮) :
    ConvergenceDivisibleStmt 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ t ht δ hδ
  let : IsProbabilityMeasure S.P := hS.isProbabilityMeasure
  apply tendsto_measure_zero_of_subsequence S.P
  · intro ε hε
    exact hm γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ t δ ε ht hδ hε
  · intro εs hε hε0
    obtain ⟨φ, hφ, hφae⟩ := convergenceDivisible_pathwise_of_steps 𝒮 h48 h46 hu
      γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ εs hε hε0
    refine ⟨φ, hφ, ?_⟩
    filter_upwards [hφae] with ω hω
    by_cases hT : t < clusterExitTime (Λ ω) ρ
    · have hconv := hω t ht hT
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
