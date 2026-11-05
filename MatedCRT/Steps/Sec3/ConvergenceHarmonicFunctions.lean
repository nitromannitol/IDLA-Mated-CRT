import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3

/-!
# Lemma 3.6: convergence of harmonic functions

The proof separates the continuous-path exit functional from the comparison
with the discrete exit cell. Both are open steps: the exit functional is not
globally continuous, and the boundary data are only controlled near the ball.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The radial retraction `x ↦ z + (r / max(r, |x - z|)) (x - z)` of `ℂ` onto `cl(B_r(z))`.
Boundary data `ψ` are only given near `cl(B_r(z))`; composing with the retraction gives a
continuous function on `ℂ` with the same values on `cl(B_r(z))`. -/
noncomputable def ballRetraction (z : ℂ) (r : ℝ) (x : ℂ) : ℂ :=
  z + ((r / max r (dist x z) : ℝ) : ℂ) * (x - z)

/-- The expectation of boundary data at the first exit of the interpolated walk
(the data being read through `ballRetraction`, which changes nothing when the walk
starts in `B_r(z)`, since the interpolated path is continuous). -/
noncomputable def interpolatedExitExpectation {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (r : ℝ) (z y : ℂ) (ψ : ℂ → ℝ) (ε : ℝ) (ω : Ω) : ℝ :=
  ∫ x, ψ (ballRetraction z r
      (pathExitPosition (ball z r) (interpolatedWalk ε (S.η ω) (S.mε ε) x)))
    ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)

/-- Regular exit of planar Brownian motion from a disk: immediately after the exit
time, the Brownian path makes an outward radial excursion. Source: the strong Markov
property of Brownian motion at the exit time and Blumenthal's 0-1 law (Mörters--Peres,
*Brownian Motion*, Theorem 2.16 and Theorem 2.7; equivalently, regularity of the
points of a circle for the Dirichlet problem via the Poincaré cone condition).
Neither the strong Markov property nor the 0-1 law is available in `MarkovProcess`. -/
def BrownianOutwardExcursionAtExitStep : Prop :=
  ∀ (y z : ℂ) (r : ℝ), y ∈ ball z r → ∀ᵐ b ∂planarBrownianMotion y,
    ∃ᶠ t in 𝓝[>] (MarkovProcess.ContinuousPath.exitTime (ball z r) b).toNNReal,
      0 < inner ℝ (b (MarkovProcess.ContinuousPath.exitTime (ball z r) b).toNNReal - z)
        (b t - b (MarkovProcess.ContinuousPath.exitTime (ball z r) b).toNNReal)

/-- Measurability of bounded Lipschitz functionals of rescaled Liouville Brownian
motion: in the Brownian path for almost every environment, and of their
conditional expectations in the environment (joint measurability of the LQG clock). -/
def LBMPathFunctionalMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ → ∀ y : ℂ,
  ∀ F : (ℝ≥0 → ℂ) → ℝ, IsBoundedLipschitzPathFunctional F →
    (∀ᵐ ω ∂S.P, AEStronglyMeasurable (fun b => F (rescaledLBMPath (S.clock ω) S.m₀ b))
      (planarBrownianMotion y)) ∧
    AEMeasurable (fun ω => ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b)
      ∂planarBrownianMotion y) S.P

/-- Measurability, for the simple random walk law, of bounded Lipschitz functionals
and of continuous functions of the exit position of the interpolated walk. -/
def InterpolatedWalkMeasurableStep : Prop :=
  ∀ (ε mε : ℝ) (η : ℝ → ℂ) (m : ℤ → ℤ → ℕ) (a : ℤ),
    (∀ F : (ℝ≥0 → ℂ) → ℝ, IsBoundedLipschitzPathFunctional F →
      AEStronglyMeasurable (fun x => F (interpolatedWalk ε η mε x)) (srwLaw m a)) ∧
    ∀ U : Set ℂ, IsOpen U → ∀ φ : ℂ → ℝ, Continuous φ →
      AEStronglyMeasurable (fun x => φ (pathExitPosition U (interpolatedWalk ε η mε x)))
        (srwLaw m a)

/-- The continuous-mapping step in (3.17): the exit-position functional is
continuous at the limiting paths almost surely, and its expectation can be
approximated using the bounded Lipschitz tests in Theorem 2.11. -/
def HarmonicPathExitStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  RandomWalkToLBMStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, (∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn ψ (closedBall z (r + s))) →
  ∀ y ∈ ball z r,
    TendstoInProbability S.P (interpolatedExitExpectation S r z y ψ)
      (fun ω => ∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
        ∂planarBrownianMotion y)

/-- Cell-size control compares the expectation at the interpolated exit with
that at the marked point of the first discrete exit cell (paper, lines 1284–1291). -/
def HarmonicExitCellStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  CellSizeEstimateStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, (∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn ψ (closedBall z (r + s))) →
  ∀ y ∈ ball z r,
    TendstoInProbability S.P
      (fun ε ω => (∫ x, ψ (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
        interpolatedExitExpectation S r z y ψ ε ω) (fun _ => 0)

/-- Lemma 3.6 follows from path exit convergence and the exit-cell comparison. -/
theorem convergenceHarmonicFunctions_of_steps (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hpath : HarmonicPathExitStep 𝒮) (hcell : HarmonicExitCellStep 𝒮) :
    ConvergenceHarmonicFunctionsStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ y hy δ hδ
  have ha := hpath h211 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ hψ y hy (δ / 2) (by linarith)
  have hb := hcell h28 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z hr hball ψ hψ y hy (δ / 2) (by linarith)
  have hs := ha.add hb
  rw [add_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le) fun ε => ?_
  calc
    S.P {ω | δ < |(∫ x, ψ (vertexPoint ε (S.η ω)
        (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
      ∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
        ∂planarBrownianMotion y|} ≤
      S.P ({ω | δ / 2 < |interpolatedExitExpectation S r z y ψ ε ω -
          ∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
            ∂planarBrownianMotion y|} ∪
        {ω | δ / 2 < |((∫ x, ψ (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
          interpolatedExitExpectation S r z y ψ ε ω) - 0|}) := by
      apply measure_mono
      intro ω hω
      simp only [mem_ofPred_eq, mem_union] at *
      by_contra h
      simp only [not_or, not_lt] at h
      have ht := abs_add_le (interpolatedExitExpectation S r z y ψ ε ω -
          ∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
            ∂planarBrownianMotion y)
        ((∫ x, ψ (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
          interpolatedExitExpectation S r z y ψ ε ω)
      simp only [sub_zero] at h
      have heq : (interpolatedExitExpectation S r z y ψ ε ω -
          ∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
            ∂planarBrownianMotion y) +
          ((∫ x, ψ (vertexPoint ε (S.η ω)
            (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))
            ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
            interpolatedExitExpectation S r z y ψ ε ω) =
          (∫ x, ψ (vertexPoint ε (S.η ω)
            (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))
            ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
          ∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
            ∂planarBrownianMotion y := by ring
      rw [heq] at ht
      linarith
    _ ≤ _ := measure_union_le _ _

end MatedCRT
