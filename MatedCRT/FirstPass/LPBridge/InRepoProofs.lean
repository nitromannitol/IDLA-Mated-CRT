import MatedCRT.FirstPass.Frozen.S4S5b
import MatedCRT.FirstPass.Frozen.S4S6c
import MatedCRT.Proofs.Measurability.LQGMeasureField
import MatedCRT.Proofs.Sec4.Prop42Closure.LQGMeasureLocalityProof
import MatedCRT.FirstPass.LPBridge.MinimumPrinciples
import MatedCRT.FirstPass.LPBridge.LQGTestIntegralMeasurable
import MatedCRT.FirstPass.LPBridge.PunctureConnected
import MatedCRT.FirstPass.LPBridge.FiniteMeasureStandardBorel

/-!
# In-repository proofs of two frozen inputs of the first pass

Two inputs of the (b) class of `docs/campaign/PHASE2-INVENTORY.md` are already proved inside the repository, so they
are discharged here rather than kept as hypotheses:

* `FrozenLQGMeasureFieldMeasurable` (FirstPass/Frozen/S4S6c.lean): the LQG measure agrees almost surely with a
  `σ(h)`-measurable random measure. Proved by `MatedCRT.LQGMeasureField.lqgMeasureFieldMeasurableStep`
  (Proofs/Measurability/LQGMeasureField.lean), whose statement is `LQGMeasureFieldMeasurableStep`
  (Proofs/Measurability/GoodScale.lean). The two statements differ only in the orientation of the almost-sure equation.
* `FPLQGMeasureLocality` (FirstPass/Frozen/S4S5b.lean): the locality of the `γ`-LQG measure as a measurable functional of
  the restricted field (Duplantier-Sheffield 2011, Proposition 1.1, with local approximations). Its body is
  `LQGMeasureLocalityFunctionalStep` (Proofs/Sec4/Prop42Closure/LQGMeasureFunctional.lean), proved by
  `LQGMeasureLocalityFunctionalStep_proof` (Proofs/Sec4/Prop42Closure/LQGMeasureLocalityProof.lean).
-/

namespace MatedCRT

open MeasureTheory Filter

/-- The almost-sure `σ(h)`-measurability of the LQG measure in the field (`FrozenLQGMeasureFieldMeasurable`), from the
repository proof of `LQGMeasureFieldMeasurableStep`. -/
theorem frozenLQGMeasureFieldMeasurable_holds (𝒮 : SpaceFillingSLEModel) :
    FrozenLQGMeasureFieldMeasurable 𝒮 := by
  intro γ hγ hγ2 Ω _ S hS
  have hstep : LQGMeasureFieldMeasurableStep 𝒮 :=
    LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮
  obtain ⟨μ', hμ', hae⟩ := hstep γ hγ hγ2 Ω S hS
  exact ⟨μ', hμ', hae.mono fun ω h => h.symm⟩

/-- The locality of the `γ`-LQG measure as a measurable functional of the restricted field
(`FPLQGMeasureLocality`), from the repository proof of `LQGMeasureLocalityFunctionalStep`. -/
theorem fpLQGMeasureLocality_holds : FPLQGMeasureLocality :=
  LQGMeasureLocalityFunctionalStep_proof

/-- The frozen superharmonic minimum principle (`FrozenSuperharmonicMinimumPrinciple`), one-line bridge to the
repository theorem `frozenSuperharmonicMinimumPrinciple_holds` (FirstPass/LPBridge/MinimumPrinciples.lean). -/
theorem frozenSuperharmonicMinimumPrinciple_inRepo : FrozenSuperharmonicMinimumPrinciple :=
  frozenSuperharmonicMinimumPrinciple_holds

/-- The strong minimum principle (`FPStrongMinimumPrinciple`), one-line bridge to `fpStrongMinimumPrinciple_holds`
(FirstPass/LPBridge/MinimumPrinciples.lean). -/
theorem fpStrongMinimumPrinciple_inRepo : FPStrongMinimumPrinciple :=
  fpStrongMinimumPrinciple_holds

/-- The integral measurability input (`FrozenLQGTestIntegralMeasurable`), one-line bridge to
`frozenLQGTestIntegralMeasurable_holds` (FirstPass/LPBridge/LQGTestIntegralMeasurable.lean). -/
theorem frozenLQGTestIntegralMeasurable_inRepo : FrozenLQGTestIntegralMeasurable :=
  frozenLQGTestIntegralMeasurable_holds

/-- Connectedness of the punctured domain (`FrozenPunctureConnected`), one-line bridge to
`frozenPunctureConnected_holds` (FirstPass/LPBridge/PunctureConnected.lean). -/
theorem frozenPunctureConnected_inRepo : FrozenPunctureConnected :=
  frozenPunctureConnected_holds

/-- Standard Borel structure of the finite measures on the disk (`FrozenFiniteMeasureDiskStandardBorel`), one-line
bridge to `frozenFiniteMeasureDiskStandardBorel_holds` (FirstPass/LPBridge/FiniteMeasureStandardBorel.lean). -/
theorem frozenFiniteMeasureDiskStandardBorel_inRepo : FrozenFiniteMeasureDiskStandardBorel :=
  frozenFiniteMeasureDiskStandardBorel_holds

end MatedCRT
