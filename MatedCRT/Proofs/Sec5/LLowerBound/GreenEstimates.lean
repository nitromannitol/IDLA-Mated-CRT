import MatedCRT.Steps.Sec5.LLowerBound
import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Model

/-!
# Reduction of the Green estimates in Lemma 5.4

The diagonal bound is obtained from Lemma 2.15 by domain monotonicity.  The
remaining event step gives the Green-sum lower bound and the finite-graph data.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- The remaining Green-sum event and the graph data used to compare its
diagonal with the ambient-ball Green function. -/
def LLowerBoundSumStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  GreenKernelLowerBoundStmt 𝒮 → CountingMeasureConvergenceStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      let m := S.mult ε ω
      let A := matedDiscreteCluster m ε (S.η ω) ρ t
      let B := ballInterior ε (S.η ω) ρ
      (∀ a, {b | m a b ≠ 0}.Finite) ∧ (∀ a, m a (a + 1) ≠ 0) ∧
      A.Finite ∧ A ⊆ B ∧ A ⊆ cellVertices ε (S.η ω) (ball 0 ρ) ∧
      (∀ b, ∀ a ∈ A, mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0)) ∧
      (∀ b, ∀ a ∈ B, mLaplacian m (fun x => greenFn m B x b) a = -(if a = b then 1 else 0)) ∧
      ∀ a ∈ A, δ < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) A)) →
        ε ^ (-(3 / 4 : ℝ)) ≤ ∑' b : A, greenFn m A b a}

/-- Lemma 2.15 supplies the diagonal part of the Green estimates once the
finite-domain comparison and Green-sum event are available. -/
theorem lLowerBoundGreenEstimatesStep_of_sum (𝒮 : SpaceFillingSLEModel)
    (hsum : LLowerBoundSumStep 𝒮) : LLowerBoundGreenEstimatesStep 𝒮 := by
  intro h215 h216 h29 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have hs := hsum h216 h29 γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ t hδ hδρ ht
  have hc := MatedCRT.HarmonicBalls.PolyHighProb.probTendsToOne
    (h215 γ hγ hγ2 ρ (1 / 2) hρ hρ1 (by norm_num) (by norm_num) Ω S hS)
  unfold TendsToOneOn at hs ⊢
  unfold ProbTendsToOne at hc
  have hlim := hs.add hc
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [] with ε
  calc
    _ ≤ S.P (({ω | t < clusterExitTime (Λ ω) ρ} ∩
        {ω | let m := S.mult ε ω
              let A := matedDiscreteCluster m ε (S.η ω) ρ t
              let B := ballInterior ε (S.η ω) ρ
              (∀ a, {b | m a b ≠ 0}.Finite) ∧ (∀ a, m a (a + 1) ≠ 0) ∧
              A.Finite ∧ A ⊆ B ∧ A ⊆ cellVertices ε (S.η ω) (ball 0 ρ) ∧
              (∀ b, ∀ a ∈ A, mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0)) ∧
              (∀ b, ∀ a ∈ B, mLaplacian m (fun x => greenFn m B x b) a = -(if a = b then 1 else 0)) ∧
              ∀ a ∈ A, δ < infDist (vertexPoint ε (S.η ω) a) (frontier (fillCells ε (S.η ω) A)) →
                ε ^ (-(3 / 4 : ℝ)) ≤ ∑' b : A, greenFn m A b a}ᶜ) ∪
        {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ), ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
          greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a b ≤ ε ^ (-(1 / 2 : ℝ))}ᶜ) := by
      apply measure_mono
      intro ω hω
      by_cases hgood : ω ∈ {ω | ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
          ∀ b ∈ cellVertices ε (S.η ω) (ball 0 ρ),
          greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball 0 ρ)) a b ≤ ε ^ (-(1 / 2 : ℝ))}
      · left
        refine ⟨hω.1, ?_⟩
        intro hdata
        apply hω.2
        dsimp only at hdata
        obtain ⟨hlf, hcons, hA, hAB, hAcell, hfirstA, hfirstB, hsum⟩ := hdata
        intro a ha hdist
        refine ⟨hsum a ha hdist, greenFn_diag_pos_of_firstStep ha hfirstA, ?_⟩
        exact (greenFn_mono_of_firstStep hlf hcons hA hAB hfirstA hfirstB a a).trans
          (hgood a (hAcell ha) a (hAcell ha))
      · exact Or.inr hgood
    _ ≤ _ := measure_union_le _ _

/-- Lemma 5.4 from the Green-sum event and the cited Green estimates. -/
theorem lLowerBound_of_sum_step (𝒮 : SpaceFillingSLEModel)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) (hsum : LLowerBoundSumStep 𝒮) :
    LLowerBoundStmt 𝒮 :=
  lLowerBound_of_steps 𝒮 h215 h216 h29 (lLowerBoundGreenEstimatesStep_of_sum 𝒮 hsum)

end MatedCRT
