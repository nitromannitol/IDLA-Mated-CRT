import MatedCRT.Proofs.Sec5.MeanValueInequality.BoundaryContactDirect

/-!
# Reduction of the normalized mean-value step

The remaining event contains the finite obstacle data and the two bounds used
in the paper (corrected.tex 2128-2140): a lower bound on the obstacle surplus
`v^ε_t = w̃^ε_t + (t ε⁻¹) g^ε_{B_ρ}(0, ·)` and an upper bound on the normalized
exit time. The finite-graph comparison and margin are proved in
`ObstacleComparison.lean`; the contact `v^ε_t = 0` off `Λ^ε_t` is proved in
`BoundaryContactDirect.lean` without any connectivity hypothesis (E-c1-2), so
the event below carries no obstacle-setting field.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- Remaining event estimate for Lemma 5.3: the surplus has a positive
uniform lower bound and the normalized exit time has a finite upper bound,
both of order `ε⁻¹`, along with the finite-graph comparison hypotheses. -/
def MeanValueSurplusStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
  ∃ c C : Ω → ℝ, Measurable[S.envSigma] c ∧ Measurable[S.envSigma] C ∧
    (∀ ω, 0 < c ω) ∧ (∀ ω, 0 < C ω) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      MeanValueSurplusData (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)
        (ballInterior ε (S.η ω) ρ)
        {a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t |
          δ < infDist (vertexPoint ε (S.η ω) a)
            (frontier (fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)))}
        (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) (t / ε) ε (c ω) (C ω)}

/-- The finite maximum-principle argument reduces the normalized inequality to
the surplus and exit-time bounds. -/
theorem meanValueNormalizedStep_of_surplus (𝒮 : SpaceFillingSLEModel)
    (hstep : MeanValueSurplusStep 𝒮) : MeanValueNormalizedStep 𝒮 := by
  intro h44 h213 h41 h33 h218 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  obtain ⟨c, C, hc, hC, hcpos, hCpos, h⟩ :=
    hstep h44 h213 h41 h33 h218 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  refine ⟨fun ω => c ω / C ω, hc.div hC, fun ω => div_pos (hcpos ω) (hCpos ω), ?_⟩
  unfold TendsToOneOn at h ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply measure_mono
  intro ω hω
  refine ⟨hω.1, ?_⟩
  intro hgood
  apply hω.2
  obtain ⟨hdata, -⟩ := id hgood
  exact ⟨hdata, fun a ha hdist =>
    normalized_meanValue_of_surplus_direct (Set.mem_Ioi.1 hε) ht (hcpos ω) (hCpos ω) hgood ha hdist⟩

/-- Lemma 5.3 from the two quantitative surplus/exit-time bounds and the
finite-graph data in `MeanValueSurplusStep`. -/
theorem meanValueInequality_of_surplus (𝒮 : SpaceFillingSLEModel)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮) (h213 : MaximumPrincipleStmt 𝒮)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (hstep : MeanValueSurplusStep 𝒮) :
    MeanValueInequalityStmt 𝒮 :=
  meanValueInequality_of_steps 𝒮 h44 h213 h41 h33 h218 (meanValueNormalizedStep_of_surplus 𝒮 hstep)

end MatedCRT
