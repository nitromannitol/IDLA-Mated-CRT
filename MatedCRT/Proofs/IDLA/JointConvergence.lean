import MatedCRT.Steps.Sec1.Convergence
import MatedCRT.Proofs.IDLA.WalkerLawMeasurable

/-! # Scaling the constrained convergence with joint outer measure

This is the joint-law form of the IDLA part of the scaling argument in Section 8.1.
It applies without measurability assumptions on the random harmonic-ball family.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- Joint-law form of Proposition 8.1 implies the joint-law form of Theorem 1.4. -/
theorem jointConvergenceOfIDLA_of_constrained (𝒮 : SpaceFillingSLEModel)
    (h81 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
      ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
        Tendsto (fun ε => S.idlaJointMeasure ε {p | t < clusterExitTime (Λ p.1) ρ ∧
          ¬ ApproximatesWithin δ (Λ p.1 t)
            (fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊))}) (𝓝[>] 0) (𝓝 0))
    (hEnv : ConeEnvironmentScalingStep 𝒮) (hHB : HarmonicBallFamilyScalingStep)
    (hR : ConeScaleRadiusStep) (hT : ScaledClusterExitTimeStep) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
    ∀ δ t : ℝ, 0 < δ → 0 < t →
      Tendsto (fun ε => S.idlaJointMeasure ε
        {p | ¬ ApproximatesWithin δ (Λ p.1 t)
          (fillCells ε (S.η p.1) (idlaCluster p.2 ⌊t / ε⌋₊))}) (𝓝[>] 0) (𝓝 0) := by
  intro γ hγ hγ2 Ω _ S hS Λ hΛ δ t hδ ht
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨b, S', Λ', δ', B, hb, hS', hP, hΛ', hδ', hδ'ρ, hB, hgood⟩ :=
    Sec1.exists_rescaled_environment 𝒮 hEnv hHB hR hT hγ hγ2 hS hΛ hδ ht he
  have he3 : 0 < e / 3 := ENNReal.div_pos_iff.2 ⟨he.ne', by norm_num⟩
  have h8 := h81 γ hγ hγ2 (1 / 2) (by norm_num) (by norm_num) Ω S' hS' Λ' hΛ' δ' (t / b)
    hδ' hδ'ρ (div_pos ht hb)
  have hlim := h8.comp (Sec1.tendsto_div_const_nhdsGT hb)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim (e / 3) he3] with ε hgε
  refine le_trans ?_ ((add_le_add hgε hB).trans_eq ?_)
  · refine hS.idlaJointMeasure_le_of_graph_eq_off_sharp hS' ε (ε / b) _ _ B hP.symm ?_ ?_
    · intro ω hω
      exact (hgood ω hω).1 ε |>.symm
    · intro ω hω xs hxs
      obtain ⟨_, hTω, happrox⟩ := hgood ω hω
      refine ⟨hTω, fun hA => hxs ?_⟩
      have hidx : t / b / (ε / b) = t / ε := by field_simp
      have hA' : ApproximatesWithin δ' (Λ' ω (t / b))
          (fillCells (ε / b) (S'.η ω) (idlaCluster xs ⌊t / b / (ε / b)⌋₊)) := hA
      rw [hidx] at hA'
      exact happrox ε _ hA'
  · rw [← add_assoc, ENNReal.add_thirds]

end MatedCRT
