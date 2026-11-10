import MatedCRT.FirstPass.Frozen.S1c
import MatedCRT.Proposed.PrestonAnalytic2008
import MatedCRT.Proofs.Sec5.ConeOriginNullMeasurableProof
import MatedCRT.Proofs.Sec5.SupersolutionSectionIdentity

/-!
# FirstPass S5i: null-measurability of the origin inclusion event (Prop 5.1 ceiling)

Target: `ConeOriginNullMeasurableStep 𝒮` (defined in `Proofs/Sec5/StoppedExterior.lean`, namespace `MatedCRT`), the
hypothesis `hmeas` of `stoppedMaxOutside_proved` (`FirstPass/S5h.lean`).

Route (no new mathematics; every input is reused or is a frozen external fact):
* Preston input `PrestonAnalyticUniversallyMeasurableStmt` (`Proposed/PrestonAnalytic2008.lean`): it has the same content as
  the first-pass frozen statement `FrozenUniversalMeasurabilityOfAnalytic` (`FirstPass/Frozen/S1c.lean`), with the arguments
  in another order. It is derived from the frozen input, which is the single hypothesis of this file.
* Borel obstacle code `CodeSectionStmt 𝒮` (`Proofs/Sec5/ConeOriginNullMeasurableProof.lean`): proved as
  `ConeOriginNull.codeSectionStmt_holds` (`Proofs/Sec5/SupersolutionSectionIdentity.lean`), reused and not reproved.
* `ConeOriginNull.coneOriginNullMeasurableStep_of_inputs` (`ConeOriginNullMeasurableProof.lean`) closes the step.
-/

namespace MatedCRT

open MeasureTheory

/-- The Preston input `PrestonAnalyticUniversallyMeasurableStmt` follows from the first-pass frozen statement
`FrozenUniversalMeasurabilityOfAnalytic` (Lusin 1917; Kechris, *Classical Descriptive Set Theory* (1995), Theorem 21.10):
both say that every analytic subset of a Polish space is null-measurable for every finite Borel measure. Only the order of
the arguments differs. -/
theorem prestonAnalyticUniversallyMeasurable_of_frozen (hU : FrozenUniversalMeasurabilityOfAnalytic) :
    PrestonAnalyticUniversallyMeasurableStmt := by
  intro X _ _ _ _ S hS μ hμ
  exact hU X μ hμ S hS

/-- **Origin null-measurability (Prop 5.1 ceiling input).** For every space-filling SLE model, the inclusion events
`{ω | ¬ B_s(0) ⊆ Λ_t(ω)}` are null-measurable for `S.P`, for all `t, s > 0`. The only hypothesis is the frozen
measure-theoretic fact `FrozenUniversalMeasurabilityOfAnalytic` (analytic sets are universally measurable); the Borel
obstacle code `CodeSectionStmt` is proved in `Proofs/Sec5/SupersolutionSectionIdentity.lean`. -/
theorem coneOriginNullMeasurable_proved (𝒮 : SpaceFillingSLEModel) (hU : FrozenUniversalMeasurabilityOfAnalytic) :
    ConeOriginNullMeasurableStep 𝒮 :=
  ConeOriginNull.coneOriginNullMeasurableStep_of_inputs 𝒮 (prestonAnalyticUniversallyMeasurable_of_frozen hU)
    (ConeOriginNull.codeSectionStmt_holds 𝒮)

end MatedCRT
