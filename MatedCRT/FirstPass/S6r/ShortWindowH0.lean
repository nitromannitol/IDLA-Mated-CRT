import MatedCRT.FirstPass.S6r.ShortWindowDerived
import MatedCRT.FirstPass.S2VG.Literature
import MatedCRT.Proofs.Field.WholePlaneExistence

/-!
# The whole-plane LQG existence `h0` without a frozen Prop

The step
`h0 = WholePlaneLQGExistenceStep` (`Steps/Sec6/AnnulusHit.lean:38`, the frozen Prop `FPWholePlaneLQGExistence` of
`FirstPass/Frozen/S5S6S7.lean:17`) is derived, and the frozen Prop is retired.

Route. For `γ ∈ (0,2)`:
* the whole-plane GFF `(Ω, P, hC, hcirc)` is the proved `MatedCRT.Field.wholePlaneGFF_exists`
  (`Proofs/Field/WholePlaneExistence.lean:46`, no hypothesis);
* the LQG measure of that field at insertion `α₀ = 0` is the cited input `MatedCRT.S2VG.LitExistence`
  (Duplantier-Sheffield 2011, Theorem 1.1; `FirstPass/S2VG/Literature.lean:44`), applied on that space;
* `IsLQGMeasureOfField P γ 0 hcirc μ` is `IsLQGMeasure P γ hcirc μ`, because the circle averages at `α₀ = 0`
  are the field itself (`fieldCircleAverage 0 h = h`).

The route through `IsQuantumCone.lateral_law` is not needed: no quantum cone is assumed.
The theorem keeps the name requested by the task, `wholePlaneLQGExistenceStep_of_lateral`.

Terminology: Duplantier-Sheffield (2011) for the whole-plane GFF and the LQG measure; Berestycki-Powell for the
insertion-`γ` measure; the circle averages `h_r(z)` in the sense of Duplantier-Sheffield.
-/

namespace MatedCRT

open MeasureTheory _root_.HarmonicBalls

/-- **`WholePlaneLQGExistenceStep`, derived.** For each `γ ∈ (0,2)` there is a probability space
carrying a whole-plane GFF (`MatedCRT.Field.wholePlaneGFF_exists`) and an LQG measure of it (`S2VG.LitExistence`
at `α₀ = 0`). The only input is the cited existence `S2VG.LitExistence`; no quantum cone is assumed. -/
theorem wholePlaneLQGExistenceStep_of_lateral (hE : S2VG.LitExistence) : WholePlaneLQGExistenceStep := by
  intro γ hγ0 hγ2
  obtain ⟨Ω, mΩ, P, hC, hcirc, hP, hG⟩ := MatedCRT.Field.wholePlaneGFF_exists
  have hQ : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    positivity
  obtain ⟨μ, hμ⟩ := hE Ω P γ hC hcirc hG hγ0 hγ2 hQ
  have hfc : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := by
    funext ω r z
    simp [fieldCircleAverage]
  have hμ' : IsLQGMeasure P γ (fun ω => fieldCircleAverage 0 (hcirc ω)) μ := hμ
  rw [hfc] at hμ'
  exact ⟨Ω, mΩ, P, hC, hcirc, μ, hP, hG, hμ'⟩

#print axioms MatedCRT.wholePlaneLQGExistenceStep_of_lateral

end MatedCRT

namespace MatedCRT.Lemma68Window

open MeasureTheory Filter Topology Metric
open _root_.HarmonicBalls
open MatedCRT

/-- **`hprev_of_shortWindow_derived` with `h0` discharged.** The frozen input
`h0 : FPWholePlaneLQGExistence` of `hprev_of_shortWindow_derived` (`ShortWindowDerived.lean:153`) is replaced by
`wholePlaneLQGExistenceStep_of_lateral` applied to the cited `S2VG.LitExistence`. The remaining binders are the
binders of `hprev_of_shortWindow_derived` other than `h0`, unchanged. -/
theorem hprev_of_shortWindow_noH0 (hE : MatedCRT.S2VG.LitExistence)
    (hCC : MatedCRT.S2VG.LitCoordChange) (hV : MatedCRT.FPWholePlaneUpperVolumeTail)
    (hB1 : ConeWholePlaneFieldLawStep)
    (hμ : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsProbabilityMeasure P → IsQuantumCone γ P hC hcirc →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasure P γ hcirc μ) :
    ShortWindowGoodRadiusPrevalenceStmt :=
  hprev_of_shortWindow_derived (MatedCRT.wholePlaneLQGExistenceStep_of_lateral hE) hCC hV hB1 hμ

#print axioms MatedCRT.Lemma68Window.hprev_of_shortWindow_noH0

end MatedCRT.Lemma68Window
