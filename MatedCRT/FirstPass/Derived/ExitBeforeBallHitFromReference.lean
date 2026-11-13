import MatedCRT.FirstPass.Derived.ExitBeforeBallHitEnv
import MatedCRT.FirstPass.Derived.HarnackPairFromCoupling

/-!
# Exit before hitting a small ball in every valid environment, from a reference environment

Berestycki–Gwynne (2020), Lemma 6.13 (last assertion).  The failure bound of the disconnection event of
Lemma 3.11 in every valid environment, which `exitBeforeBallHit_polyHighProb` takes as a hypothesis, is the second
conjunct of `hPair_of_reference`: for a normalized space-filling SLE law `ν`, a model with that law that has valid
environments on `ℝ` for every `γ ∈ (0, 2)`, and a one-sided mating-rigid set `G` that is full for every correlated
Brownian law.  The result is the exit-before-hit estimate with polynomially high probability as `ε → 0`, in every
valid environment, from the cell-size estimate alone.
-/

set_option autoImplicit false

open MeasureTheory Metric Set Filter Topology _root_.HarmonicBalls
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.GMSMain MatedCRTHarmonic.GMSMain.T15A
open MatedCRT.FirstPass.Derived LatticeProb.LQG.ExplicitScale

namespace MatedCRT.ExitBeforeBallHitEnv

/-- **Lemma 6.13, last assertion, in every valid environment, from a reference environment** (Berestycki–Gwynne
(2020)): from each vertex of `V(B_ρ \ B_{ρ-δ})` the simple random walk on the mated-CRT map exits `V(B_ρ)` before
hitting `V(∂B_{√δ}(η x))` with probability at least `1 - A δ^ξ`, with polynomially high probability as `ε → 0`. -/
theorem exitBeforeBallHit_of_reference {𝒮 𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) (h28 : CellSizeEstimateStmt 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ \ ball (0 : ℂ) (ρ - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X <
            vHitTime (cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X}} := by
  refine exitBeforeBallHit_polyHighProb 𝒮 h28 fun γ hγ0 hγ2 => ?_
  obtain ⟨β₀, α₀, hβ₀, hα₀, hP⟩ := hPair_of_reference hν hνref href hGnull hG γ hγ0 hγ2
  refine ⟨β₀, α₀, hβ₀, hα₀, fun ρ' hρ'0 hρ'1 => ?_⟩
  obtain ⟨_, p₁, _, hp₁, hS⟩ := hP ρ' hρ'0 hρ'1
  refine ⟨p₁, hp₁, fun Ω _ S hSv => ?_⟩
  obtain ⟨C, hC⟩ := hS Ω S hSv
  exact ⟨C, fun ε hε0 hε1 => (hC ε hε0 hε1).2⟩

/-- **Lemma 6.13, last assertion, with the localization of the walk, in every valid environment, from a reference
environment** (Berestycki–Gwynne (2020)): the event of `exitBeforeBallHit_of_reference` is strengthened by: every
vertex visited up to the exit time from `V(B_ρ)` has its cell inside `B_{√δ}(η x)`; the probability bound
`1 - A δ^ξ` and the exponents are the same. -/
theorem exitBeforeBallHit_cells_of_reference {𝒮 𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref) {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) (h28 : CellSizeEstimateStmt 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ \ ball (0 : ℂ) (ρ - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X <
            vHitTime (cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X ∧
            ∀ n : ℕ, (n : ℕ∞) ≤ vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X →
              cell ε (S.η ω) (X n) ⊆ ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)}} := by
  refine exitBeforeBallHit_polyHighProb_cells 𝒮 h28 fun γ hγ0 hγ2 => ?_
  obtain ⟨β₀, α₀, hβ₀, hα₀, hP⟩ := hPair_of_reference hν hνref href hGnull hG γ hγ0 hγ2
  refine ⟨β₀, α₀, hβ₀, hα₀, fun ρ' hρ'0 hρ'1 => ?_⟩
  obtain ⟨_, p₁, _, hp₁, hS⟩ := hP ρ' hρ'0 hρ'1
  refine ⟨p₁, hp₁, fun Ω _ S hSv => ?_⟩
  obtain ⟨C, hC⟩ := hS Ω S hSv
  exact ⟨C, fun ε hε0 hε1 => (hC ε hε0 hε1).2⟩

end MatedCRT.ExitBeforeBallHitEnv
