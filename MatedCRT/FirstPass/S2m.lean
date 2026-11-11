import MatedCRT.Proofs.Sec4.Prop42Closure.ConeWholePlaneSteps
import MatedCRT.Proofs.Field.WholePlaneExistence
import MatedCRT.FirstPass.Frozen.S2m

/-! # FIRST PASS S2m: the whole-plane LQG model exists

`firstPass_wholePlaneLQGModel_of_existence` proves `WholePlaneLQGModelStep` (`ConeWholePlaneSteps.lean:57`): for every
`γ ∈ (0,2)` there are a probability space, a whole-plane GFF and its `γ`-insertion LQG measure. The whole-plane GFF is
the proved `MatedCRT.Field.wholePlaneGFF_exists` (`Proofs/Field/WholePlaneExistence.lean:46`); the LQG measure is the
single frozen input `FrozenLQGMeasureExistenceInsertion` (`FirstPass/Frozen/S2m.lean`), applied on that space.

Checked against the other frozen Props:
* `FPWholePlaneLQGModel` (`FirstPass/Frozen/S4S5b.lean:34`) is by definition `WholePlaneLQGModelStep` itself, so it is the
  target frozen, not a route to it.
* `FPWholePlaneLQGExistence` (`FirstPass/Frozen/S5S6S7.lean:17`) is `WholePlaneLQGExistenceStep`
  (`Steps/Sec6/AnnulusHit.lean:38`): its LQG measure is `IsLQGMeasure P' γ hcirc' μ'`, the measure of the field `h^ℂ` itself
  (insertion `α₀ = 0`), not `IsLQGMeasureOfField P γ γ`. It does not give the insertion-`γ` measure. -/

namespace MatedCRT.FirstPass.S2m

open MeasureTheory HarmonicBalls

/-- **Derived: `WholePlaneLQGModelStep` (FIRST-PASS).** From the frozen insertion-`γ` LQG existence
`FrozenLQGMeasureExistenceInsertion` and the proved whole-plane GFF existence, for each `γ ∈ (0,2)` there are a probability
space `(Ω, P)`, a whole-plane GFF `(hC, hcirc)` and a random measure `μ` with `IsLQGMeasureOfField P γ γ hcirc μ`. -/
theorem firstPass_wholePlaneLQGModel_of_existence
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion) : MatedCRT.WholePlaneLQGModelStep := by
  intro γ hγ0 hγ2
  obtain ⟨Ω, mΩ, P, hC, hcirc, hP, hG⟩ := MatedCRT.Field.wholePlaneGFF_exists
  obtain ⟨μ, hμ⟩ := hE γ hγ0 hγ2 Ω P hP hC hcirc hG
  exact ⟨Ω, mΩ, P, hC, hcirc, μ, hP, hG, hμ⟩

end MatedCRT.FirstPass.S2m
