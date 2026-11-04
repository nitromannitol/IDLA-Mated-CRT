import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudeCells
import MatedCRT.Proofs.Sec7.MassBoundOdometer.PolyHighProb
import MatedCRT.Steps.Infra.MatingOfTrees
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Draft.Section2

/-! The high-probability crude-path estimate in Proposition 7.1. -/

namespace MatedCRT.Sec7

open MeasureTheory Set Metric HarmonicBalls

/-- Lemmas 2.8 and 7.4 give the crude confinement bound simultaneously for every
intermediate cluster and odometer bound. The assumption that the stopped cluster's
graph closure meets the ambient ball ensures that the cell-size estimate applies. -/
theorem crude_confinement_polyHighProb (𝒮 : SpaceFillingSLEModel)
    (hcell : CellSizeEstimateStmt 𝒮) (hcrude : CrudeUpperBoundStmt 𝒮)
    (hadj : AdjacentCellsMeetAeStep 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (ζ ρ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (t : ℝ) (ht : 0 < t) :
    PolyHighProb S.P fun ε => {ω |
      let m := S.mult ε ω
      let η := S.η ω
      let A := matedDiscreteCluster m ε η ρ t
      let D := ε ^ (2 / (2 + γ) ^ 2 - ζ)
      ∀ Θ : Set ℤ, ∀ M : ℝ, (0 : ℤ) ∈ Θ → 0 ≤ M →
        vClosure m A ⊆ cellVertices ε η (ball 0 ρ) →
        (∀ c ∈ vBoundary m Θ, stoppedOdometer m ε η ρ t c ≤ M) →
        fillCells ε η (vClosure m A) ⊆
          cthickening (D + (D + M / ((Real.log ε⁻¹)⁻¹ ^ 2) * (2 * D)))
            (fillCells ε η (vClosure m Θ))} := by
  have hgood : ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧
      ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty :=
    (hS.isAreaParametrized.and (hadj γ hγ hγ2 Ω S hS)).mono fun _ h => ⟨h.1.1, h.2⟩
  apply polyHighProb_of_inter_ae (hcrude γ hγ hγ2 ρ hρ hρ1 Ω S hS t ht)
    (hcell γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω S hS) hgood (r₁ := 1) one_pos
  intro ε hε hε1 ω hpath hsize hgeom
  dsimp only
  intro Θ M hzero hM hA hbound
  have hlog : 0 < Real.log ε⁻¹ := Real.log_pos ((one_lt_inv₀ hε).2 hε1)
  have hd : 0 < (Real.log ε⁻¹)⁻¹ ^ 2 := by positivity
  apply crudeUpperBound_event_confinement (S.mult ε ω) Θ ε ρ t
    (ε ^ (2 / (2 + γ) ^ 2 - ζ)) M (S.η ω)
    (S.mult_symm ε ω) hε.le (Real.rpow_nonneg hε.le _) hM hd hgeom.1 hzero hpath
    (hgeom.2 ε hε) ?_ hbound
  intro c hc
  exact (hsize c (hA hc)).2

end MatedCRT.Sec7
