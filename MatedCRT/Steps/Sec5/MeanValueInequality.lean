import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section5
import MatedCRT.Proofs.Sec5.MeanValueInequality.Reversibility

/-!
# Lemma 5.3: normalized mean-value inequality

The outstanding probabilistic/obstacle step is exposed below.  The assembly
uses Green-function reversibility and the normalized exit-time identity proved
in `Reversibility.lean`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- Data needed for the finite-volume Green-function reversibility identity. -/
def FiniteReversibleGreenData (m : ℤ → ℤ → ℕ) (A : Set ℤ) : Prop :=
  (∀ a b, m a b = m b a) ∧
  (∀ a, {b | m a b ≠ 0}.Finite) ∧ A.Finite ∧
  (∀ a, mdeg m a ≠ 0) ∧
  (∀ b, ∀ a ∈ A, mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0))

/-- The normalized inequality from the obstacle comparison and uniform bounds
in the proof of Lemma 5.3, together with the finite-graph data needed for
reversibility.  This step remains to be derived from the cited results. -/
def MeanValueNormalizedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
  ∃ s : Ω → ℝ, Measurable[S.envSigma] s ∧ (∀ ω, 0 < s ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      FiniteReversibleGreenData (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) ∧
      ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t))) →
        (1 + s ω) * normExitTime (S.mult ε ω)
          (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) a ≤
        t / ε * greenKernel (S.mult ε ω)
          (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) a 0}

/-- Lemma 5.3 from its normalized form and the finite-graph data. -/
theorem meanValueInequality_of_steps (𝒮 : SpaceFillingSLEModel)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hstep : MeanValueNormalizedStep 𝒮) :
    MeanValueInequalityStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨s, hs, hspos, h⟩ := hstep h44 h213 h41 h33 h218 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  refine ⟨s, hs, hspos, ?_⟩
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [] with ε
  apply measure_mono
  intro ω hω
  refine ⟨hω.1, ?_⟩
  intro hgood
  apply hω.2
  obtain ⟨⟨hsymm, hlf, hfinite, hdeg, hfirst⟩, hnorm⟩ := hgood
  intro a ha hdist
  exact meanValue_of_normalized_of_firstStep hsymm hlf hfinite hdeg hfirst a (t / ε) (s ω) (hnorm a ha hdist)

end MatedCRT
