import MatedCRT.Proofs.Sec7.OdometerBoundMass.Corrected
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.Statements
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ConditionalEventAssembly

/-! Almost-sure map properties used in the shell contraction.
The mated-CRT infrastructure includes work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric

/-- The map structure, the corrected odometer Laplacian, and the
odometer hitting estimate hold together at all positive mesh sizes. -/
theorem ae_shell_structural_data
    {𝒮 : SpaceFillingSLEModel} {γ ρ : ℝ} (hγ : 0 < γ) (hγ' : γ < 2)
    (hρ : 0 < ρ) (hρ' : ρ < 1) (hadj : AdjacentCellsMeetAeStep 𝒮)
    (hodo : OdometerBoundMassStmt 𝒮)
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) :
    ∀ᵐ ω ∂S.P,
      IsConeHarmonicBallFamily (S.μ ω) (Λ ω) ∧ IsAreaParametrized (S.μ ω) (S.η ω) ∧
      (∀ ε : ℝ, 0 < ε →
        (∀ a : ℤ, {b | S.mult ε ω a b ≠ 0}.Finite) ∧
        ∀ r : ℝ, (cellVertices ε (S.η ω) (closedBall 0 r)).Finite) ∧
      (∀ ε t : ℝ, 0 < ε → 0 < t → ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
        a ≠ 0 → matedLaplacian (S.mult ε ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) a =
          ((matedDeg (S.mult ε ω) a : ℕ) : ℝ)⁻¹) ∧
      (∀ ε : ℝ, 0 < ε → ∀ a b : ℤ, S.mult ε ω a b ≠ 0 →
        (cell ε (S.η ω) a ∩ cell ε (S.η ω) b).Nonempty) ∧
      (∀ ε t : ℝ, 0 < ε → 0 < t → ∀ U : Set ℤ,
        U ⊆ cellVertices ε (S.η ω) (ball 0 ρ) \ {0} → ∀ b ∈ U,
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b ≤
          (⨆ a : vBoundary (S.mult ε ω) U, stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a) *
            (srwLaw (S.mult ε ω) b {x | vExitTime U x <
              vHitTime (U \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) x}).toReal) := by
  have hstr := matedMapStructureStep_of_adjacentCellsMeet 𝒮 hadj
  have hlap := stoppedOdometerLaplacianStep_of_corrected
    (discreteLaplacianBoundCorrected_of_escape hadj) hadj
  filter_upwards [hΛ, hS.isAreaParametrized, hstr γ hγ hγ' Ω S hS,
    hlap γ hγ hγ' ρ hρ hρ' Ω S hS, hadj γ hγ hγ' Ω S hS,
    hodo γ hγ hγ' ρ hρ hρ' Ω S hS] with ω hfam harea hstrω hlapω hadjω hodoω
  exact ⟨hfam, harea, hstrω, hlapω, hadjω, hodoω⟩

end MatedCRT.Sec7
