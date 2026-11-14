import MatedCRT.FirstPass.Derived.HarnackPairForallGamma
import MatedCRT.FirstPass.Derived.ExitBeforeBallHitFromReference
import MatedCRT.FirstPass.Derived.ResistanceBoundOfReference

/-!
# Exit, resistance and Green kernel lower bounds with the mating-rigid set chosen for each `γ`

Berestycki–Gwynne (2020), Lemmas 4.3, 4.4 and 6.13. The theorems `exitBeforeBallHit_of_reference`,
`exitBeforeBallHit_cells_of_reference`, `hres_of_reference` and `greenKernelLowerBoundStmt_of_reference` take one
one-sided mating-rigid set `G` that is full for every `γ`-correlated two-sided Brownian law, for all `γ ∈ (0, 2)` at
once. Their proofs use the full-measure property only at the `γ` they have fixed. Here the same conclusions are
proved when, for every `γ ∈ (0, 2)`, there is a one-sided mating-rigid set `G_γ` that is full for every
`γ`-correlated two-sided Brownian law (the set may depend on `γ`).

## Main results

* `hres_of_reference_at`: the resistance bound (4.15) in every valid environment of one `γ`, from a set `G` that is
  full for the `γ`-correlated Brownian laws only.
* `hres_of_reference_of_forall_gamma`: the resistance bound (4.15) for every `γ`, with a set `G_γ` for each `γ`.
* `greenKernelLowerBoundStmt_of_reference_of_forall_gamma`: Lemma 2.16 with a set `G_γ` for each `γ`.
* `exitBeforeBallHit_of_reference_of_forall_gamma`, `exitBeforeBallHit_cells_of_reference_of_forall_gamma`:
  Lemma 6.13 (last assertion) and its localized form with a set `G_γ` for each `γ`.
-/

set_option autoImplicit false

section Resistance

open MeasureTheory Metric Set Filter Topology _root_.HarmonicBalls
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **The resistance bound (4.15) in every valid environment of one `γ`** (Berestycki–Gwynne (2020), Lemma 4.3),
from the reference environment of `γ` of a model with the same normalized space-filling SLE law and a one-sided
mating-rigid set `G` that is full for every `γ`-correlated two-sided Brownian law (at this `γ` only). -/
theorem hres_of_reference_at {𝒮 𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) :
    ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ r : ℝ,
        r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) → ∀ s : ℝ, ε ^ β ≤ s → s ≤ r / 4 →
        ∃ h : ℤ → ℝ, (∀ k ∈ cellVertices ε (S.η ω) (closedBall (vertexPoint ε (S.η ω) a) s), h k = 1) ∧
          (∀ k, k ∉ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (3 * r / 4)) → h k = 0) ∧
          ∀ T : Finset ℤ, Real.log (3 * r / 4 / s) *
            ((1 / 2) * ∑ k ∈ T, ∑ l ∈ T, (S.mult ε ω k l : ℝ) * (h k - h l) ^ 2) ≤ C₂} := by
  obtain ⟨S', hS'⟩ := href γ hγ0 hγ2
  obtain ⟨β, hβ, hρ⟩ := hres_polyHighProb_reference hγ0 hγ2 hS'
  refine ⟨β, hβ, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨C₂, hC₂, hP⟩ := hρ ρ hρ0 hρ1
  refine ⟨C₂, hC₂, fun Ω _ S hS => ?_⟩
  exact polyHighProb_of_multEq_of_valid hν hνref hγ0 hγ2 hS hS' hGnull hG
    (Q := fun ε ω η => ∀ a ∈ cellVertices ε η (ball 0 ρ), ∀ r : ℝ,
      r ≤ infDist (vertexPoint ε η a) (sphere 0 ρ) → ∀ s : ℝ, ε ^ β ≤ s → s ≤ r / 4 →
      ∃ h : ℤ → ℝ, (∀ k ∈ cellVertices ε η (closedBall (vertexPoint ε η a) s), h k = 1) ∧
        (∀ k, k ∉ cellVertices ε η (ball (vertexPoint ε η a) (3 * r / 4)) → h k = 0) ∧
        ∀ T : Finset ℤ, Real.log (3 * r / 4 / s) *
          ((1 / 2) * ∑ k ∈ T, ∑ l ∈ T,
            (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2) k l : ℝ) * (h k - h l) ^ 2) ≤ C₂)
    (fun ε ω ω' η hm => by rw [hm]) hP

/-- **The resistance bound (4.15) in every valid environment, with the mating-rigid set chosen for each `γ`**
(Berestycki–Gwynne (2020), Lemma 4.3). The conclusion of `hres_of_reference`, when for every `γ ∈ (0, 2)` there is
a one-sided mating-rigid set `G_γ` that is full for every `γ`-correlated two-sided Brownian law. -/
theorem hres_of_reference_of_forall_gamma {𝒮 𝒮ref : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ r : ℝ,
        r ≤ infDist (vertexPoint ε (S.η ω) a) (sphere 0 ρ) → ∀ s : ℝ, ε ^ β ≤ s → s ≤ r / 4 →
        ∃ h : ℤ → ℝ, (∀ k ∈ cellVertices ε (S.η ω) (closedBall (vertexPoint ε (S.η ω) a) s), h k = 1) ∧
          (∀ k, k ∉ cellVertices ε (S.η ω) (ball (vertexPoint ε (S.η ω) a) (3 * r / 4)) → h k = 0) ∧
          ∀ T : Finset ℤ, Real.log (3 * r / 4 / s) *
            ((1 / 2) * ∑ k ∈ T, ∑ l ∈ T, (S.mult ε ω k l : ℝ) * (h k - h l) ^ 2) ≤ C₂} := by
  intro γ hγ0 hγ2
  obtain ⟨G, hGnull, hG⟩ := hU γ hγ0 hγ2
  exact hres_of_reference_at hν hνref href hγ0 hγ2 hGnull hG

/-- **Lemma 2.16** (Berestycki–Gwynne (2020), Lemma 4.4) for every model with a normalized space-filling SLE law
`ν`, from the reference environments of a model with law `ν`, with the mating-rigid set chosen for each `γ`: for
every `γ ∈ (0, 2)` a one-sided mating-rigid set `G_γ` that is full for every `γ`-correlated two-sided Brownian law.
The cell size estimate is a theorem, the pair events are `hPair_of_reference_of_forall_gamma` and the resistance
bound (4.15) is `hres_of_reference_of_forall_gamma`. -/
theorem greenKernelLowerBoundStmt_of_reference_of_forall_gamma {𝒮 𝒮ref : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G) : GreenKernelLowerBoundStmt 𝒮 :=
  greenKernelLowerBoundStmt_of_pair (cellSizeEstimateStmt_holds 𝒮)
    (hPair_of_reference_of_forall_gamma hν hνref href hU) (hres_of_reference_of_forall_gamma hν hνref href hU)

end MatedCRT.FirstPass.Derived

end Resistance

section ExitBeforeBallHit

open MeasureTheory Metric Set Filter Topology _root_.HarmonicBalls
open scoped ENNReal
open MatedCRTHarmonic MatedCRTHarmonic.GMSMain MatedCRTHarmonic.GMSMain.T15A
open MatedCRT.FirstPass.Derived LatticeProb.LQG.ExplicitScale

namespace MatedCRT.ExitBeforeBallHitEnv

/-- **Lemma 6.13, last assertion, in every valid environment, from a reference environment, with the mating-rigid
set chosen for each `γ`** (Berestycki–Gwynne (2020)): the conclusion of `exitBeforeBallHit_of_reference`, when for
every `γ ∈ (0, 2)` there is a one-sided mating-rigid set `G_γ` that is full for every `γ`-correlated two-sided
Brownian law. -/
theorem exitBeforeBallHit_of_reference_of_forall_gamma {𝒮 𝒮ref : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (h28 : CellSizeEstimateStmt 𝒮) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ A : ℝ, 0 < ξ ∧ 0 < A ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
      S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ x ∈ cellVertices ε (S.η ω) (ball (0 : ℂ) ρ \ ball (0 : ℂ) (ρ - δ)),
        ENNReal.ofReal (1 - A * δ ^ ξ) ≤
          srwLaw (S.mult ε ω) x {X | vExitTime (cellVertices ε (S.η ω) (ball (0 : ℂ) ρ)) X <
            vHitTime (cellVertices ε (S.η ω) (frontier (ball (vertexPoint ε (S.η ω) x) (Real.sqrt δ)))) X}} := by
  refine exitBeforeBallHit_polyHighProb 𝒮 h28 fun γ hγ0 hγ2 => ?_
  obtain ⟨β₀, α₀, hβ₀, hα₀, hP⟩ := hPair_of_reference_of_forall_gamma hν hνref href hU γ hγ0 hγ2
  refine ⟨β₀, α₀, hβ₀, hα₀, fun ρ' hρ'0 hρ'1 => ?_⟩
  obtain ⟨_, p₁, _, hp₁, hS⟩ := hP ρ' hρ'0 hρ'1
  refine ⟨p₁, hp₁, fun Ω _ S hSv => ?_⟩
  obtain ⟨C, hC⟩ := hS Ω S hSv
  exact ⟨C, fun ε hε0 hε1 => (hC ε hε0 hε1).2⟩

/-- **Lemma 6.13, last assertion, with the localization of the walk, in every valid environment, from a reference
environment, with the mating-rigid set chosen for each `γ`** (Berestycki–Gwynne (2020)): the conclusion of
`exitBeforeBallHit_cells_of_reference`, when for every `γ ∈ (0, 2)` there is a one-sided mating-rigid set `G_γ`
that is full for every `γ`-correlated two-sided Brownian law. -/
theorem exitBeforeBallHit_cells_of_reference_of_forall_gamma {𝒮 𝒮ref : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (hνref : HasNormalizedSLELaw 𝒮ref ν)
    (href : HasReferenceEnvironments 𝒮ref)
    (hU : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ G : Set MatedCRTHarmonic.MatedCRT.Path2,
      (∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2, MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ →
        μ Gᶜ = 0) ∧ MatingRigidLEOn G)
    (h28 : CellSizeEstimateStmt 𝒮) :
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
  obtain ⟨β₀, α₀, hβ₀, hα₀, hP⟩ := hPair_of_reference_of_forall_gamma hν hνref href hU γ hγ0 hγ2
  refine ⟨β₀, α₀, hβ₀, hα₀, fun ρ' hρ'0 hρ'1 => ?_⟩
  obtain ⟨_, p₁, _, hp₁, hS⟩ := hP ρ' hρ'0 hρ'1
  refine ⟨p₁, hp₁, fun Ω _ S hSv => ?_⟩
  obtain ⟨C, hC⟩ := hS Ω S hSv
  exact ⟨C, fun ε hε0 hε1 => (hC ε hε0 hε1).2⟩

end MatedCRT.ExitBeforeBallHitEnv

end ExitBeforeBallHit
