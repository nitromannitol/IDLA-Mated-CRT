import MatedCRT.FirstPass.S5d.StoppedFirstGreenInputs
import MatedCRT.FirstPass.S5c.GreenUpper
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.MatedLeastMeasurable
import MatedCRT.Steps.Infra.MatingOfTrees
import MatedCRT.Draft.Section4

/-!
# The pathwise package of the stopped clause, discharged

`StoppedFirstGreenInputs.lean` reduces `StoppedFirstGreenStep` to the open input `StoppedFirstGreenInputsStep` and to the
almost sure deterministic package `StoppedPathwiseInputs` (the hypothesis `hdet` of `stoppedFirstGreenStep_of_inputs`).
This file discharges `hdet` from the standing facts of the environment and from the corrected Lemma 4.4
(`DiscreteLaplacianBoundCorrectedStmt`, Draft/Section4.lean), for every `t > 0`:
* symmetry of the edge multiplicities and `k ∼ k + 1`: `MatedCRTEnv.mult_symm`, `MatedCRTEnv.mult_succ_ne_zero`;
* local finiteness of the edge multiplicities: `ae_locallyFinite_mult_of_adjacentCells`;
* finiteness of `V^ε(B_ρ)` and of its interior `V^ε(B_ρ) \ V^ε(∂B_ρ)`: `MatedCRT.S5c.cellVertices_ball_finite` and
  `MatedCRT.S5c.interiorCellVertices_finite_of_ball`, from the continuity and properness of `η`
  (`IsValid.ae_tendsto_cocompact`, `IsValid.isAreaParametrized`);
* the obstacle identity on the cluster: the first conjunct of `DiscreteLaplacianBoundCorrectedStmt`;
* `0 ∈ V^ε(Λ_t)`: `0 ∈ Λ_t` (an open harmonic ball contains its centre) and `η 0 = 0 ∈ cell 0`.

The origin floor `c/ε ≤ u^ε(0)` is NOT part of this file: it stays inside the open input
`StoppedFirstGreenInputsStep`.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

/-- **The pathwise package.** For `t > 0`, almost surely for every `ε > 0`, `StoppedPathwiseInputs` holds. -/
theorem stoppedPathwiseInputs_ae (𝒮 : SpaceFillingSLEModel)
    (hcell : AdjacentCellsMeetAeStep 𝒮) (hlap : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) (t : ℝ) (ht : 0 < t) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → StoppedPathwiseInputs S Λ ρ t ε ω := by
  have hE := hS.ae_tendsto_cocompact
  have hA := hS.isAreaParametrized
  have hL := ae_locallyFinite_mult_of_adjacentCells hS hγ hγ2 hcell
  have hD := hlap γ hγ hγ2 ρ hρ hρ1 Ω S hS
  filter_upwards [hE, hA, hL, hD, hΛ] with ω hωE hωA hωL hωD hωΛ
  intro ε hε
  obtain ⟨hηc, hη0, -, -⟩ := hωA
  have hH : (0 : ℂ) ∈ Λ ω t := (hωΛ.1 t ht).2.1
  have hcell0 : S.η ω 0 ∈ cell ε (S.η ω) 0 :=
    ⟨0, ⟨by push_cast; linarith, by push_cast; linarith⟩, rfl⟩
  have hmem : S.η ω 0 ∈ Λ ω t := by rw [hη0]; exact hH
  refine ⟨fun a b => S.mult_symm ε ω a b, hωL ε hε, fun k => S.mult_succ_ne_zero hε.le ω k,
    S5c.interiorCellVertices_finite_of_ball hηc hωE hε 0 ρ, S5c.cellVertices_ball_finite hηc hωE hε 0 ρ,
    (hωD t ε ht hε).1, ?_⟩
  exact ⟨S.η ω 0, hcell0, hmem⟩

/-- **The first Green inequality of the stopped clause from the open input and the standing steps.** This is
`stoppedFirstGreenStep_of_inputs` with `hdet` discharged by `stoppedPathwiseInputs_ae`. -/
theorem stoppedFirstGreenStep_of_steps (𝒮 : SpaceFillingSLEModel) (hin : StoppedFirstGreenInputsStep 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) (hlap : DiscreteLaplacianBoundCorrectedStmt 𝒮) :
    StoppedFirstGreenStep 𝒮 :=
  stoppedFirstGreenStep_of_inputs 𝒮 hin
    (fun γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t ht =>
      stoppedPathwiseInputs_ae 𝒮 hcell hlap γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ t ht)

end MatedCRT
