import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.PotentialBoundaryProbability
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.OfSteps

/-! Reduction of the boundary estimate to the discrete exit time. -/

namespace MatedCRT

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- The discrete part of the boundary estimate for normalized exit times. -/
def DiscreteExitBoundaryStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ExpectedExitTimeExplicitBoundStmt 𝒮 → CellSizeEstimateStmt 𝒮 → BoundedExitTimeRVStmt →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ δ : ℝ, 0 < δ → ∀ e : ℝ≥0∞, 0 < e → ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
        δ < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x|} ≤ e

/-- Separate continuum and discrete boundary bounds combine on their common
thinner boundary layer. -/
theorem normalizedExit_boundary_of_discrete
    (𝒮 : SpaceFillingSLEModel) (h33 : UniformConvergenceGreenKernelStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt)
    (hdisc : DiscreteExitBoundaryStep 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    {δ : ℝ} (hδ : 0 < δ) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        S.P {ω | ∃ x ∈ closedBall z r \ closedBall z r',
          δ < |rescale (S.mε ε) ε (S.η ω)
            (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x| ∨
          δ < |normalizedExitGreenPotential S r z ω x|} ≤ e := by
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨r₁, hr₁0, hr₁r, h₁⟩ := hdisc h219 h28 h217 γ hγ hγ2 ρ hρ hρ1 Ω S hS
    r z hr hball δ hδ (e / 2) he2
  obtain ⟨r₂, hr₂0, hr₂r, h₂⟩ := normalizedExitGreenPotential_boundary_small_of_statements
    𝒮 h33 h217 hγ hγ2 hρ hρ1 S hS hr hball hδ he2
  refine ⟨max r₁ r₂, lt_of_lt_of_le hr₁0 (le_max_left _ _), max_lt hr₁r hr₂r, ?_⟩
  filter_upwards [h₁] with ε hε
  calc
    S.P {ω | ∃ x ∈ closedBall z r \ closedBall z (max r₁ r₂),
        δ < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x| ∨
        δ < |normalizedExitGreenPotential S r z ω x|} ≤
      S.P ({ω | ∃ x ∈ closedBall z r \ closedBall z r₁,
        δ < |rescale (S.mε ε) ε (S.η ω)
          (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))) x|} ∪
      {ω | ∃ x ∈ closedBall z r \ closedBall z r₂,
        δ < |normalizedExitGreenPotential S r z ω x|}) := by
          apply measure_mono
          rintro ω ⟨x, ⟨hx, hxout⟩, h⟩
          have hx₁ : x ∉ closedBall z r₁ := fun hx' => hxout (closedBall_subset_closedBall (le_max_left _ _) hx')
          have hx₂ : x ∉ closedBall z r₂ := fun hx' => hxout (closedBall_subset_closedBall (le_max_right _ _) hx')
          rcases h with h | h
          · exact Or.inl ⟨x, ⟨hx, hx₁⟩, h⟩
          · exact Or.inr ⟨x, ⟨hx, hx₂⟩, h⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hε h₂
    _ = e := ENNReal.add_halves e

/-- Lemma 3.7 reduced to potential identification, interior convergence,
and the discrete boundary estimate. -/
theorem convergenceNormalizedExitTime_of_discrete_boundary (𝒮 : SpaceFillingSLEModel)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮)
    (h219 : ExpectedExitTimeExplicitBoundStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (h31 : DiscretePotentialTightnessStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h217 : BoundedExitTimeRVStmt) (hpot : NormalizedExitPotentialStep 𝒮)
    (hinterior : NormalizedExitInteriorStep 𝒮) (hdisc : DiscreteExitBoundaryStep 𝒮) :
    ConvergenceNormalizedExitTimeStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball
  refine ⟨normalizedExitGreenPotential S r z, hpot γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball, ?_⟩
  apply uniformOn_closedBall_of_interior_boundary
  · exact hinterior h33 h29 h219 h35 h31 h28 h217 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball
  · intro δ hδ e he
    exact normalizedExit_boundary_of_discrete 𝒮 h33 h219 h28 h217 hdisc
      hγ hγ2 hρ hρ1 S hS hr hball hδ he

end MatedCRT
