import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGapAssembly
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.Final
import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.VolumeGrowthSupport
import MatedCRT.Proofs.Sec4.Prop42Closure.ConePrematureNull

/-! # Strict obstacle gap for the quantum cone -/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set Metric _root_.HarmonicBalls

/-- The strict obstacle inclusion follows from the volume-growth estimates, the
whole-plane model, equality of restricted LQG laws, and equivalence of smooth
shifts of the whole-plane field's local pairings. -/
theorem harmonicBallStrictObstacleGapStep_of_restrictedLaw_and_pairingLaws
    (𝒮 : SpaceFillingSLEModel)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0}) (h27 : VolumeGrowthStmt)
    (hmodel : WholePlaneLQGModelStep) (hlaw : ConeWholePlaneRestrictedLQGLawStep)
    (hpair : ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF Q hC hcirc → ∀ (α : ℝ) (g : ℂ → ℝ), IsTestFunction univ g →
      Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ) ≪
          Q.map (localModConstPairings α hC univ) ∧
        Q.map (localModConstPairings α hC univ) ≪
          Q.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ)) :
    HarmonicBallStrictObstacleGapStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS Λ hΛ t ht
  have hcone : IsConeField γ S.P S.hC S.hcirc S.μ :=
    ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  obtain ⟨Ω', m, Q, hC, hcirc, ν, hprob, hgff, hν⟩ := hmodel γ hγ hγ2
  let : MeasurableSpace Ω' := m
  let : IsProbabilityMeasure Q := hprob
  obtain ⟨E, _, hE, hEvol⟩ := hcone.exists_measurable_volumeGrowth_support hγ hγ2 h27 hρ hρ1
  have hμvol : ∀ᵐ ω ∂S.P, IsLocallyFiniteMeasure (S.μ ω) ∧
      ∃ βm βp, VolumeGrowth (S.μ ω) ρ βm βp := hE.mono fun ω hω => hEvol _ hω
  have hα : γ < lqgQ γ := self_lt_lqgQ hγ hγ2
  obtain ⟨βm, βp, hνvol⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hgff hν
  have hνvol' : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (ν ω) ∧
      ∃ βm βp, VolumeGrowth (ν ω) ρ βm βp :=
    hνvol.mono fun ω hω => ⟨hω.1, βm, βp, hω.2 ρ hρ⟩
  have hident := hlaw γ hγ hγ2 Ω S.P S.hC S.hcirc S.μ hcone Ω' Q hC hcirc ν hprob hgff hν
  exact ae_harmonicBall_subset_cluster_of_wholePlane_identDistrib h32 h611 h82 S.P Q S.μ ν
    (hgff.aemeasurable_lqgMeasure hν) hρ hρ1 ht hγ hγ2 hα hμvol hνvol' hident hgff hν
    (hpair Ω' Q hC hcirc hgff γ) Λ hΛ

end MatedCRT
