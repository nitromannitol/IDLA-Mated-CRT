import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.TripleCover
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ContinuumCover
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.NowhereMonotone
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps
import MatedCRT.FirstPass.Derived.ZeroConeEdgeCountCodeProof

/-!
# The triple points of Peanosphere curves of the correlated Brownian pair contain no continuum

The named statement `MatedCRT.GMS310Transfer.CorrelatedBMPeanosphereTriplePointsNoContinuum` (for almost every
`γ`-correlated Brownian pair, the points visited three times by any Peanosphere curve of the pair contain no continuum
of positive diameter) follows from Shimura's theorem on meandering points for the pair alone (written answer
`notes/mq-idla-triple-answer.md`, FINAL):

* `not_containsNondegenerateContinuum_curveTriplePoints_of_noOppositeSideMin` (deterministic): if no time is a minimum
  of one coordinate on a left neighbourhood and of the other on a right neighbourhood, and no coordinate is monotone on
  an interval, the triple points of every Peanosphere curve lie in countably many compact totally disconnected sets
  (`exists_countable_compact_cover_curveTriplePoints`, `isTotallyDisconnected_image_of_injOn`), so they contain no
  continuum of positive diameter (`not_containsNondegenerateContinuum_of_subset_biUnion`, Baire's theorem);
* almost surely no coordinate of the pair is monotone on an interval (`ae_nowhereMonotone_of_isCorrelatedBM2`);
* `correlatedBMPeanosphereTriplePointsNoContinuum_of_noOppositeSideMin`: the named statement from Shimura's theorem
  for the pair, and `correlatedBMPeanosphereTriplePointsNoContinuum_of_shimuraSteps` from the steps of Shimura's
  theorem (`ShimuraSteps.lean`).
-/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2)
open MatedCRTHarmonic.RouteM (Peanosphere)

namespace MatedCRT.PeanosphereTriplePoints

/-- **No continuum among the triple points** of a Peanosphere curve of a pair without opposite-side minima and without
monotone intervals. -/
theorem not_containsNondegenerateContinuum_curveTriplePoints_of_noOppositeSideMin {p : Path2} {η : ℝ → ℂ}
    (hη : Peanosphere p η)
    (hLR : NoOppositeSideMin (fun t => (p t).1) (fun t => (p t).2))
    (hRL : NoOppositeSideMin (fun t => (p t).2) (fun t => (p t).1))
    (hL : NowhereMonotone (fun t => (p t).1)) (hR : NowhereMonotone (fun t => (p t).2)) :
    ¬ ContainsNondegenerateContinuum (curveTriplePoints η) := by
  obtain ⟨S, hSc, hSE, hcov⟩ := exists_countable_compact_cover_curveTriplePoints hη hLR hRL hL hR
  refine not_containsNondegenerateContinuum_of_subset_biUnion (S := (fun E => η '' E) '' S)
    (hSc.image _) ?_ ?_
  · rintro F ⟨E, hE, rfl⟩
    obtain ⟨hEc, hEi, hinj⟩ := hSE E hE
    exact ⟨hEc.image_of_continuousOn hη.cont.continuousOn,
      isTotallyDisconnected_image_of_injOn hEc (isTotallyDisconnected_of_interior_eq_empty hEi)
        hη.cont.continuousOn hinj⟩
  · intro z hz
    obtain ⟨E, hE, hzE⟩ := mem_iUnion₂.1 (hcov hz)
    exact mem_iUnion₂.2 ⟨η '' E, ⟨E, hE, rfl⟩, hzE⟩

/-- **The triple points of every Peanosphere curve of the correlated pair contain no continuum**, from Shimura's
theorem for the pair (no opposite-side minima, both orders). -/
theorem correlatedBMPeanosphereTriplePointsNoContinuum_of_noOppositeSideMin
    (hS : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ →
      ∀ᵐ p ∂μ, NoOppositeSideMin (fun t => (p t).1) (fun t => (p t).2) ∧
        NoOppositeSideMin (fun t => (p t).2) (fun t => (p t).1)) :
    GMS310Transfer.CorrelatedBMPeanosphereTriplePointsNoContinuum := by
  intro γ hγ0 hγ2 μ hμ
  filter_upwards [hS γ hγ0 hγ2 μ hμ, ae_nowhereMonotone_of_isCorrelatedBM2 hμ] with p hp hm η hη
  exact not_containsNondegenerateContinuum_curveTriplePoints_of_noOppositeSideMin hη hp.1 hp.2 hm.1 hm.2

/-- **The triple points of every Peanosphere curve of the correlated pair contain no continuum**, from the steps of
Shimura's theorem (`ShimuraSteps.lean`). -/
theorem correlatedBMPeanosphereTriplePointsNoContinuum_of_shimuraSteps
    (hsteps : ∀ γ : ℝ, 0 < γ → γ < 2 → ShimuraLocalization γ ∧ ShimuraSummation γ ∧
      ShimuraCellBounds γ ∧ ShimuraOccupancy γ) :
    GMS310Transfer.CorrelatedBMPeanosphereTriplePointsNoContinuum :=
  correlatedBMPeanosphereTriplePointsNoContinuum_of_noOppositeSideMin fun γ hγ0 hγ2 _ hμ =>
    let h := hsteps γ hγ0 hγ2
    ae_noOppositeSideMin_of_shimuraSteps h.1 h.2.1 h.2.2.1 h.2.2.2 hμ

end MatedCRT.PeanosphereTriplePoints
