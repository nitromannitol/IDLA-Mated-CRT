import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapProbability

/-! # Coverage of random sets away from the coincidence set -/

namespace MatedCRT

open Filter Topology Set Metric MeasureTheory HarmonicBalls

/-- A random set contained in a deterministic set separated from the pole is
covered in probability on the event that its scaled obstacle gap has a fixed
positive lower bound. The random set need not be measurable. -/
theorem random_strict_gap_coverage_in_probability (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (O : Set ℂ) (K : Ω → Set ℂ)
    (hO : O ⊆ ball 0 ρ) (hO' : O ⊆ closedBall 0 ρ \ {0})
    (hdist : 0 < infDist (0 : ℂ) O) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ ∧ K ω ⊆ O ∧
      ∀ x ∈ K ω, s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
      fun ε => {ω | K ω ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)} := by
  have hw := h41 γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ t ht (s / 4) (by positivity)
  have hφ := obstacle_convergence_off_origin 𝒮 h33 γ hγ hγ' ρ hρ hρ' Ω S hS
    t (s / 4) ht (by positivity) O hO' hdist
  unfold ProbTendsToOne at hφ
  unfold TendsToOneOn
  have hsum := hw.add hφ
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply le_trans ?_ (measure_union_le _ _)
  apply measure_mono_ae
  filter_upwards [hS.ae_tendsto_cocompact, hS.isAreaParametrized] with ω hp harea
  rintro ⟨⟨hT, hKO, hgap⟩, hbad⟩
  by_cases hwbad : ∃ x ∈ ball (0 : ℂ) ρ,
      s / 4 < |rescaledMatedLeastSupersolution S ρ t ε ω x -
        S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|
  · exact Or.inl ⟨hT, hwbad⟩
  · by_cases hφbad : ∀ x ∈ O,
        |rescale (S.mε ε) ε (S.η ω) (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t) x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)| ≤ s / 4
    · exfalso
      apply hbad
      apply subset_fillCells_matedDiscreteCluster_of_strict_gap harea.1 hp harea.2.2.1 hε
        (medianOf_nonneg _) (hKO.trans hO) hs hgap
      · intro x hx
        have hbound : |rescaledMatedLeastSupersolution S ρ t ε ω x -
            S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x| ≤ s / 4 :=
          le_of_not_gt (fun hh => hwbad ⟨x, hO (hKO hx), hh⟩)
        change |rescaledMatedLeastSupersolution S ρ t ε ω x - _| < s / 2
        linarith
      · intro x hx
        have hbound := hφbad x (hKO hx)
        change |rescale (S.mε ε) ε (S.η ω) (matedObstacle (S.mult ε ω) ε (S.η ω) ρ t) x -
          (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)| < s / 2
        linarith
    · exact Or.inr hφbad

/-- The part of an arbitrary random set inside a deterministic region separated
from the pole is covered in probability when its obstacle gap has a fixed
positive lower bound. -/
theorem random_inter_strict_gap_coverage_in_probability (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (O : Set ℂ) (K : Ω → Set ℂ)
    (hO : O ⊆ ball 0 ρ) (hO' : O ⊆ closedBall 0 ρ \ {0})
    (hdist : 0 < infDist (0 : ℂ) O) :
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ ∧
      ∀ x ∈ K ω ∩ O, s ≤ S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x -
        (-t * (S.c₀ / 6) * greenFunction (ball 0 ρ) 0 x)}
      fun ε => {ω | K ω ∩ O ⊆ fillCells ε (S.η ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)} := by
  simpa only [inter_subset_right, true_and] using
    random_strict_gap_coverage_in_probability 𝒮 h41 h33 γ hγ hγ' ρ hρ hρ' Ω S hS
      Λ hΛ t s ht hs O (fun ω => K ω ∩ O) hO hO' hdist

end MatedCRT
