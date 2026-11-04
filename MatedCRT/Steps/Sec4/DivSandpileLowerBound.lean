import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section4
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.ClusterComparison

/-!
# Proposition 4.2: reduction to obstacle-cluster approximation

The continuum and discrete Green-function estimates are used to approximate the interior of
the continuum cluster by the discrete obstacle cluster. The final passage to the sandpile cluster
uses the lower odometer bound and complementarity.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The geometric and analytic part of Proposition 4.2: the inner neighbourhood of the
continuum cluster is covered by cells in the discrete obstacle cluster with high probability.
Its proof is the portion of lines 1621–1670 using Green-function convergence and cell size. -/
def ObstacleClusterInnerApproximationStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ConvergenceDivisibleStmt 𝒮 → ConeHarmonicBallsStmt → MaximumPrincipleStmt 𝒮 →
  UniformConvergenceGreenKernelStmt 𝒮 → CellSizeEstimateStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε =>
      {ω | innerNbhd δ (Λ ω t) ⊆
        fillCells ε (S.η ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t)}

/-- Local finiteness, absence of loops, positive degrees, an admissible stabilizing function,
and the lower odometer bound of equation (lower-bound-odometer), for every positive mesh. -/
def DivSandpileOdometerComparisonStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ᵐ ω ∂S.P, ∀ t ε : ℝ, 0 < t → 0 < ε →
    IsLocallyFiniteMult (S.mult ε ω) ∧ (∀ a, S.mult ε ω a a = 0) ∧
    (∀ a, 0 < mdeg (S.mult ε ω) a) ∧
    (Sandpile.admissible (S.mult ε ω) (t / ε)).Nonempty ∧
    ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a -
        matedObstacle (S.mult ε ω) ε (S.η ω) ρ t a ≤
        sandpileNormOdometer (S.mult ε ω) (t / ε) a

/-- Proposition 4.2 follows from inner approximation by the obstacle cluster and the lower
odometer comparison. -/
theorem divSandpileLowerBound_of_steps (𝒮 : SpaceFillingSLEModel)
    (h41 : ConvergenceDivisibleStmt 𝒮) (h23 : ConeHarmonicBallsStmt)
    (h213 : MaximumPrincipleStmt 𝒮) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (happrox : ObstacleClusterInnerApproximationStep 𝒮)
    (hodo : DivSandpileOdometerComparisonStep 𝒮) : DivSandpileLowerBoundStmt 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have happ := happrox h41 h23 h213 h33 h28 γ hγ hγ' ρ hρ hρ' Ω S hS Λ hΛ δ t hδ hδρ ht
  have hcompare := hodo γ hγ hγ' ρ hρ hρ' Ω S hS
  unfold TendsToOneOn at happ ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds happ
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply measure_mono_ae
  filter_upwards [hcompare] with ω hω
  intro hbad
  refine ⟨hbad.1, ?_⟩
  intro hgood
  obtain ⟨hlf, hloop, hdeg, hne, hlower⟩ := hω t ε ht hε
  have hsubset := matedDiscreteCluster_subset_sandpileCluster hlf hloop hdeg hne hlower
  exact hbad.2 (hgood.trans (fillCells_matedDiscreteCluster_subset_sandpileCluster hsubset))

end MatedCRT
