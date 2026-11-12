import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.Steps.Sec11.ScalePowerBounds
import LatticeProb.LQG.GMCScaleIncrement
import MatedCRT.FirstPass.Frozen.S2m
import MatedCRT.Proofs.Field.WholePlaneExistence
import MatedCRT.Steps.Sec6.AnnulusHit

/-!
# Existence and coordinate change of the whole-plane γ-LQG measure: three inputs as theorems

* `FrozenLQGMeasureExistenceInsertion` (`FirstPass/Frozen/S2m.lean`): on every probability space carrying a
  whole-plane GFF `h^ℂ`, the γ-LQG measure of `h^ℂ - γ log |·|` exists (Duplantier-Sheffield 2011, Proposition 1.1;
  Bou-Rabee-Gwynne arXiv:2208.11795v3, Section 2.2). From `HarmonicBalls.lqgMeasureExistence_derived` at `α₀ = γ`,
  with `γ < Q_γ` for `γ ∈ (0, 2)`.
* `WholePlaneLQGExistenceStep` (`Steps/Sec6/AnnulusHit.lean`): a whole-plane GFF together with its γ-LQG measure
  exists. The field from `MatedCRT.Field.wholePlaneGFF_exists` and its measure from
  `lqgMeasureExistence_derived` at `α₀ = 0`.
* `WholePlaneLQGCoordinateChangeStep` (`Steps/Sec6/AnnulusHit.lean`): the push-forward of the γ-LQG measure of a
  whole-plane GFF under `x ↦ (x - z)/r` is a.s. a positive finite multiple of the γ-LQG measure of another whole-plane
  GFF on the same space (Duplantier-Sheffield 2011, Proposition 2.1, with the scale and translation invariance of
  `h^ℂ` modulo constants). From `LatticeProb.Gauss.IsWholePlaneGFF.exists_coordChange` through the bridges
  `isWholePlaneGFF_iff` and `isLQGMeasure_iff`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory HarmonicBalls

/-- The γ-LQG measure of `h^ℂ - α₀ log |·|` with `α₀ = 0` is the γ-LQG measure of `h^ℂ`. -/
theorem isLQGMeasure_of_isLQGMeasureOfField_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    IsLQGMeasure P γ hcirc μ := by
  have h0 : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := by
    funext ω r z
    simp [fieldCircleAverage]
  unfold IsLQGMeasureOfField at hμ
  rwa [h0] at hμ

/-- **Existence of the γ-LQG measure of the insertion-γ whole-plane field** (`FrozenLQGMeasureExistenceInsertion`)
is a theorem. -/
theorem frozenLQGMeasureExistenceInsertion_holds : S2m.FrozenLQGMeasureExistenceInsertion :=
  fun γ hγ hγ2 _ _ P _ hC hcirc hG =>
    lqgMeasureExistence_derived P γ γ hC hcirc hG hγ hγ2 (gamma_lt_lqgQ hγ hγ2)

/-- **A whole-plane GFF with its γ-LQG measure exists** (`WholePlaneLQGExistenceStep`) is a theorem. -/
theorem wholePlaneLQGExistenceStep_holds : WholePlaneLQGExistenceStep := by
  intro γ hγ hγ2
  obtain ⟨Ω, mΩ, P, hC, hcirc, hP, hG⟩ := MatedCRT.Field.wholePlaneGFF_exists
  obtain ⟨μ, hμ⟩ := lqgMeasureExistence_derived P γ 0 hC hcirc hG hγ hγ2
    (lt_trans hγ (gamma_lt_lqgQ hγ hγ2))
  exact ⟨Ω, mΩ, P, hC, hcirc, μ, hP, hG, isLQGMeasure_of_isLQGMeasureOfField_zero hμ⟩

/-- **Coordinate change of the whole-plane γ-LQG measure under `x ↦ (x - z)/r`**
(`WholePlaneLQGCoordinateChangeStep`) is a theorem. -/
theorem wholePlaneLQGCoordinateChangeStep_holds : WholePlaneLQGCoordinateChangeStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ _ hG hμ r hr z
  obtain ⟨hC'', hcirc'', μ'', c, hG'', hμ'', hc⟩ :=
    ((LPBridge.isWholePlaneGFF_iff P hC hcirc).1 hG).exists_coordChange hγ hγ2
      ((LPBridge.isLQGMeasure_iff P γ hcirc μ).1 hμ) hr z
  exact ⟨hC'', hcirc'', μ'', c, (LPBridge.isWholePlaneGFF_iff P hC'' hcirc'').2 hG'',
    (LPBridge.isLQGMeasure_iff P γ hcirc'' μ'').2 hμ'', hc⟩

end MatedCRT.FirstPass.Derived
