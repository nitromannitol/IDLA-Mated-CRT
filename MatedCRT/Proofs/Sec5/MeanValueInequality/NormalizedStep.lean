import MatedCRT.Steps.Sec5.MeanValueInequality
import MatedCRT.Proofs.Sec5.MeanValueInequality.ObstacleComparison

/-!
# Reduction of the normalized mean-value step

The remaining event contains the finite obstacle data and the two bounds used
in the paper: a lower bound on the obstacle surplus and an upper bound on the
normalized exit time.  The finite-graph comparison and margin are proved in
`ObstacleComparison.lean`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- Finite-graph hypotheses for the obstacle comparison, together with the
two quantitative bounds on a prescribed set of interior vertices. -/
def MeanValueSurplusData (m : ℤ → ℤ → ℕ) (A B I : Set ℤ) (w : ℤ → ℝ)
    (K ε c C : ℝ) : Prop :=
  FiniteReversibleGreenData m A ∧
  (∀ a, m a (a + 1) ≠ 0) ∧ B.Finite ∧ A ⊆ B ∧ (0 : ℤ) ∈ A ∧
  (∀ b, ∀ a ∈ B, mLaplacian m (fun x => greenFn m B x b) a = -(if a = b then 1 else 0)) ∧
  (∀ a ∈ A, mLaplacian m w a = (mdeg m a : ℝ)⁻¹) ∧
  (∀ a ∉ A, w a + K * greenKernel m B 0 a ≤ 0) ∧
  (∀ a ∈ I, c / ε ≤ w a + K * greenKernel m B 0 a ∧ normExitTime m A a ≤ C / ε)

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
      let m := S.mult ε ω
      let A := matedDiscreteCluster m ε (S.η ω) ρ t
      let B := ballInterior ε (S.η ω) ρ
      let I := {a ∈ A | δ < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) A))}
      MeanValueSurplusData m A B I (matedLeastSupersolution m ε (S.η ω) ρ t) (t / ε) ε (c ω) (C ω)}

set_option maxHeartbeats 400000 in
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
  dsimp only at hgood
  obtain ⟨hdata, hcons, hB, hAB, h0, hfirstB, hw, hboundary, hbounds⟩ := hgood
  refine ⟨hdata, ?_⟩
  intro a ha hdist
  obtain ⟨hsymm, hlf, hA, hdeg, hfirstA⟩ := hdata
  obtain ⟨hv, hq⟩ := hbounds a ⟨ha, hdist⟩
  have hcomp := obstacle_surplus_le_green_sub_exit hsymm hlf hcons hA hB hAB h0 hfirstA hfirstB
    (matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t) (t / ε) hw hboundary a
  rw [greenKernel_symm_of_firstStep hsymm hlf hA hdeg hfirstA 0 a] at hcomp
  exact normalized_meanValue_of_surplus_bounds hε (hcpos ω) (hCpos ω) hcomp hv hq

end MatedCRT
