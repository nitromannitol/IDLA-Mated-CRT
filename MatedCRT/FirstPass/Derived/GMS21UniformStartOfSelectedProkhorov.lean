import MatedCRT.FirstPass.Derived.GMS21UniformStartOfSelectedCell
import MatedCRT.FirstPass.Derived.StopAtExitLevyProkhorov
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockFinite

/-!
# The uniform-start invariance principle from the Prokhorov distance of the stopped curves

The proof of Gwynne–Miller–Sheffield (arXiv:1705.11161), Theorem 3.4, case 1, establishes that the supremum over the
starting points `z` of the Prokhorov distance between the conditional law of the embedded walk from the smallest cell
containing `z`, stopped at its exit from a ball, and the law of planar Brownian motion from `z` stopped at its exit
from the same ball, for the metric on curves modulo time parametrization, tends to zero in probability. The good set
`uniformStartSelectedLPData ε ρ R κ` records this at mesh `ε`, for the ball `B_R(0)`, starts `z ∈ closedBall 0 ρ` and
distance `< κ`, together with the almost sure exit of the walk from `B_R(0)` (the stopped walk is a finite curve).
The curve classes are read in the space `BouRabeeGwynne.CurveSpace 2` of curves modulo time parametrization
(`StopAtExitLevyProkhorov.stoppedExitCurve`), and the distance is `levyProkhorovEDist`.

A Lévy–Prokhorov bound gives the one-sided bound for every set of stopped paths
(`StopAtExitLevyProkhorov.allSet_stopAtExit_le_of_levyProkhorovEDist`), so `uniformStartSelectedLPData ε ρ R κ` is
contained in `uniformStartSelectedBallData ε ρ R (2 κ)`, and the results of `GMS21UniformStartOfSelectedCell` apply.

## Main results

* `uniformStartSelectedLPData`: the Prokhorov good set at mesh `ε`.
* `uniformStartSelectedLPData_subset_ballData`: the inclusion into the fixed-radius selected-cell good set.
* `gms21UniformStartInput_of_selectedLP_reference`: `GMS21UniformStartInput 𝒮` from the normalized law, the closure
  properties and the law-level Prokhorov bound at the cell masses `1/n` on one reference environment.
-/

set_option autoImplicit false

open MeasureTheory Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

open StopAtExitLevyProkhorov

/-- The Prokhorov good set at mesh `ε` on the data space of (continuous curve, edge multiplicities): for every point
`z ∈ closedBall 0 ρ`, the walk of `d.2` from the smallest vertex whose cell contains `z`, embedded by `d.1(ε ·)` and
interpolated, leaves `B_R(0)` almost surely, and the law of its curve class stopped at that exit is at Lévy–Prokhorov
distance less than `κ` from the law of the curve class of planar Brownian motion from `z` stopped at its exit from
`B_R(0)`. -/
def uniformStartSelectedLPData (ε ρ R κ : ℝ) : Set (C(ℝ, ℂ) × (ℤ → ℤ → ℕ)) :=
  {d | ∀ z ∈ closedBall (0 : ℂ) ρ,
    (∀ᵐ w ∂srwLaw d.2 (vertexOf ε d.1 z), pathExitTime (ball (0 : ℂ) R) (interpolatedWalk ε d.1 1 w) ≠ ⊤) ∧
    levyProkhorovEDist
        ((srwLaw d.2 (vertexOf ε d.1 z)).map fun w =>
          stoppedExitCurve (ball (0 : ℂ) R) (interpPathCM (vertexPoint ε d.1) zero_le_one w))
        ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R))) < ENNReal.ofReal κ}

/-- **A Prokhorov bound gives the bound for all sets of stopped paths.** For `κ > 0`, the Prokhorov good set
`uniformStartSelectedLPData ε ρ R κ` is contained in the fixed-radius selected-cell good set
`uniformStartSelectedBallData ε ρ R (2 κ)`. -/
theorem uniformStartSelectedLPData_subset_ballData {ε ρ R κ : ℝ} (hκ : 0 < κ) :
    uniformStartSelectedLPData ε ρ R κ ⊆ uniformStartSelectedBallData ε ρ R (2 * κ) := by
  intro d hd z hz A
  obtain ⟨hfin, hlp⟩ := hd z hz
  have hF : AEMeasurable (fun w => stoppedExitCurve (ball (0 : ℂ) R)
      (interpPathCM (vertexPoint ε d.1) zero_le_one w)) (srwLaw d.2 (vertexOf ε d.1 z)) :=
    ((measurable_stoppedExitCurve _ isOpen_ball).comp
      (measurable_interpPathCM (vertexPoint ε d.1) zero_le_one)).aemeasurable
  have hfinB : ∀ᵐ b : ContinuousPath ℂ ∂(planarBrownianMotion z), pathExitTime (ball (0 : ℂ) R) ⇑b ≠ ⊤ :=
    (KilledOccupation.planar_exit_ae_lt_top z 0 R).mono fun _ h => h.ne
  have h := allSet_stopAtExit_le_of_levyProkhorovEDist (srwLaw d.2 (vertexOf ε d.1 z))
    (interpPathCM (vertexPoint ε d.1) zero_le_one) (ball (0 : ℂ) R) hF hfin (ball (0 : ℂ) R) isOpen_ball z hfinB
    hκ hκ hlp A
  refine h.trans (add_le_add (measure_mono fun b hb => ?_) (ENNReal.ofReal_le_ofReal (by linarith)))
  obtain ⟨f, hfA, hf⟩ := hb
  exact ⟨f, hfA, hf.trans_le (ENNReal.ofReal_le_ofReal (by linarith))⟩

/-- **The uniform-start invariance principle from the Prokhorov distance of the stopped curves on one reference
environment.** Let `𝒮` have normalized space-filling SLE law `ν` and the closure properties `SLEModelClosureInput 𝒮`.
Suppose that for each `0 < γ < 2` some model `𝒮₀` with the same law `ν` has a valid environment `S₀` (on any carrier)
with a measurable continuous version `η₀` of its curve, such that for all `0 < ρ < R` and `κ, θ > 0`, for all large
`n` the law of `(η₀, S₀.mult (1/n))` gives mass at most `θ` to the complement of
`uniformStartSelectedLPData (1/n) ρ R κ` (Gwynne–Miller–Sheffield, arXiv:1705.11161, proof of Theorem 3.4, case 1:
the Prokhorov distance of the walk from the smallest cell containing the start and of Brownian motion, both stopped at
their exits from a ball, tends to zero in probability uniformly in the start, at the cell masses `1/n`). Then
`GMS21UniformStartInput 𝒮`. -/
theorem gms21UniformStartInput_of_selectedLP_reference {𝒮 : SpaceFillingSLEModel}
    {ν : ℝ → Measure SLEPathCode} (h1 : HasNormalizedSLELaw 𝒮 ν) (h2 : SLEModelClosureInput 𝒮)
    (hRef : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ 𝒮₀ : SpaceFillingSLEModel, HasNormalizedSLELaw 𝒮₀ ν ∧
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (S₀ : MatedCRTEnv Ω₀), S₀.IsValid 𝒮₀ γ ∧
      ∃ η₀ : Ω₀ → C(ℝ, ℂ), Measurable η₀ ∧ (∀ᵐ ω ∂S₀.P, ⇑(η₀ ω) = S₀.η ω) ∧
      ∀ R ρ : ℝ, 0 < ρ → ρ < R → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          S₀.P.map (fun ω => (η₀ ω, S₀.mult (1 / (n : ℝ)) ω))
            (uniformStartSelectedLPData (1 / (n : ℝ)) ρ R κ)ᶜ ≤ ENNReal.ofReal θ) :
    GMS21UniformStartInput 𝒮 := by
  refine gms21UniformStartInput_of_selectedBall_reference h1 h2 fun γ hγ0 hγ2 => ?_
  obtain ⟨𝒮₀, hν₀, Ω₀, mΩ₀, S₀, hS₀, η₀, hη₀m, hη₀, hbd⟩ := hRef γ hγ0 hγ2
  refine ⟨𝒮₀, hν₀, Ω₀, mΩ₀, S₀, hS₀, η₀, hη₀m, hη₀, fun R ρ hρ hρR κ hκ θ hθ => ?_⟩
  obtain ⟨N, hN⟩ := hbd R ρ hρ hρR (κ / 2) (half_pos hκ) θ hθ
  refine ⟨N, fun n hn => le_trans (measure_mono ?_) (hN n hn)⟩
  refine compl_subset_compl.2 ?_
  have h := uniformStartSelectedLPData_subset_ballData (ε := 1 / (n : ℝ)) (ρ := ρ) (R := R) (half_pos hκ)
  have h2 : 2 * (κ / 2) = κ := by ring
  rwa [h2] at h

end MatedCRT
