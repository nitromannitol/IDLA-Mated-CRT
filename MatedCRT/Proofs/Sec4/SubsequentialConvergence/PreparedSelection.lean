import MatedCRT.Steps.Sec4.SubsequentialConvergencePrepared

/-! The measurable-selection obligation for prepared odometer sequences. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The fixed-sequence measurable-selection obligation already used for Lemma 4.6
also supplies selection from the stronger prepared compactness assertion. -/
theorem odometerPreparedSelectionStep_of_measurableSelection (𝒮 : SpaceFillingSLEModel)
    (hs : OdometerMeasurableSelectionStep 𝒮) : OdometerPreparedSelectionStep 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht e he he0 hcompact
  apply hs γ hγ hγ' ρ hρ hρ' Ω S hS t ht e he he0
  filter_upwards [hcompact] with ω hω
  obtain ⟨φ, hφ, w, hw, hconv⟩ := hω.1 id strictMono_id
  refine ⟨φ, hφ, w, hw, ?_, ?_⟩
  · exact hω.2 φ hφ w (by simpa using hconv)
  · simpa using hconv

/-- Corrected Lemma 4.6 using its prepared compactness obligation and the
existing fixed-sequence measurable-selection obligation. -/
theorem subsequentialConvergencePrepared_of_measurableSelection
    (𝒮 : SpaceFillingSLEModel) (h47 : EquiboundedStmt 𝒮)
    (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (h31 : DiscretePotentialTightnessPreparedStmt 𝒮) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hc : OdometerPreparedCompactnessStep 𝒮) (hs : OdometerMeasurableSelectionStep 𝒮) :
    SubsequentialConvergencePreparedStmt 𝒮 :=
  subsequentialConvergencePrepared_of_steps 𝒮 h47 h44 h31 h35 hc
    (odometerPreparedSelectionStep_of_measurableSelection 𝒮 hs)

end MatedCRT
