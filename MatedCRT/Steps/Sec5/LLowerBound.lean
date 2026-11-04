import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Sec5.LLowerBound.Algebra

/-!
# Lemma 5.4: Green-sum and diagonal estimates

The remaining estimate is stated as a step, with its three inputs from the
paper explicit.  A small loss in the Green-sum exponent permits the lower
bound to absorb a positive random mass without requiring a deterministic lower
bound for that mass.  The assembly below is deterministic once this event
estimate is available.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The estimates in the proof of Lemma 5.4, with a power loss in the Green
sum.  The proof is to use Lemmas 2.15, 2.16 and 2.9 and the geometry of the
cell union.  Positivity of the diagonal is included because `greenFn` is
real-valued and maps an infinite expectation to zero. -/
def LLowerBoundGreenEstimatesStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  GreenFunctionCrudeBoundStmt 𝒮 → GreenKernelLowerBoundStmt 𝒮 → CountingMeasureConvergenceStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) →
        ε ^ (-(3 / 4 : ℝ)) ≤ (∑' b : matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
          greenFn (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) b a) ∧
        0 < greenFn (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) a a ∧
        greenFn (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) a a ≤
          ε ^ (-(1 / 2 : ℝ))}

/-- Lemma 5.4 from the stated Green estimates, with `q = 1/4`. -/
theorem lLowerBound_of_steps (𝒮 : SpaceFillingSLEModel)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (hest : LLowerBoundGreenEstimatesStep 𝒮) :
    LLowerBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have h := hest h215 h216 h29 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply measure_mono
  intro ω hω
  refine ⟨hω.1, ?_⟩
  intro hgood
  apply hω.2
  intro a ha hdist
  obtain ⟨hN, hD, hupper⟩ := hgood a ha hdist
  apply (le_div_iff₀ hD).2
  calc
    ε ^ (-(1 / 4 : ℝ)) * greenFn (S.mult ε ω)
        (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) a a
      ≤ ε ^ (-(1 / 4 : ℝ)) * ε ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hupper (Real.rpow_nonneg hε.le _)
    _ = ε ^ (-(3 / 4 : ℝ)) := by
        rw [← Real.rpow_add hε]
        congr 1
        norm_num
    _ ≤ _ := hN

end MatedCRT
