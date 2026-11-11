import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockAgree
import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockFun
import MatedCRT.Proofs.Sec3.KilledOccupation.ConeClockTransfer
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockExitLIntegral

/-!
# Regularized clocks against the approximating LQG clocks (Appendix B of arXiv:2211.04891)

This file collects the pointwise and measure-theoretic facts that compare the regularized clock
`regClockFun` built from circle averages (the clock of the Duplantier-Sheffield circle-average field)
with the approximating LQG clock `HarmonicBalls.lqgClockApprox` of the quantum cone field.

* `clockGapFun` is the quenched gap between the regularized clocks at two scales, taken as a supremum over
  rational times, so that it is measurable in the path variable;
* `measurable_clockGapFun` is its measurability;
* `ennDist_ofReal_le` compares `ENNReal.ofReal` values in the extended distance.

Terminology: Duplantier-Sheffield (circle averages and the LQG measure), Berestycki-Powell (LQG clocks),
Armitage-Gardiner (potential theory, harmonic balls).
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The quenched gap between the regularized clocks at the scales `ε` and `ε'`: the supremum over rational
times of the extended distance of the two clocks. Taking the supremum over `ℚ≥0` makes it a countable
supremum of measurable functions of the path. -/
noncomputable def clockGapFun (γ : ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (ε ε' : ℝ)
    (x : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) : ℝ≥0∞ :=
  ⨆ q : ℚ≥0, ennDist (regClockFun γ ε x.1 σ x.2 (q : ℝ≥0)) (regClockFun γ ε' x.1 σ x.2 (q : ℝ≥0))

/-- The gap `clockGapFun` is measurable whenever the exit time `σ` is measurable. -/
theorem measurable_clockGapFun (γ : ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (hσ : Measurable σ) (ε ε' : ℝ) :
    Measurable (clockGapFun γ σ ε ε') :=
  Measurable.iSup fun q =>
    ((measurable_regClockFun γ ε σ hσ (q : ℝ≥0)).sub (measurable_regClockFun γ ε' σ hσ (q : ℝ≥0))).add
      ((measurable_regClockFun γ ε' σ hσ (q : ℝ≥0)).sub (measurable_regClockFun γ ε σ hσ (q : ℝ≥0)))

/-- The extended distance of two `ENNReal.ofReal` values is at most the `ENNReal.ofReal` of their difference. -/
lemma ennDist_ofReal_le (a b : ℝ) :
    ennDist (ENNReal.ofReal a) (ENNReal.ofReal b) ≤ ENNReal.ofReal |a - b| := by
  have key : ∀ x y : ℝ, x ≤ y → ENNReal.ofReal y - ENNReal.ofReal x ≤ ENNReal.ofReal |x - y| := by
    intro x y hxy
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hxy), tsub_le_iff_right]
    calc ENNReal.ofReal y = ENNReal.ofReal (y - x + x) := congrArg ENNReal.ofReal (sub_add_cancel y x).symm
      _ ≤ ENNReal.ofReal (y - x) + ENNReal.ofReal x := ENNReal.ofReal_add_le
  unfold ennDist
  rcases le_total a b with hab | hab
  · rw [tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal hab), zero_add]
    exact key a b hab
  · rw [tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal hab), add_zero, abs_sub_comm a b]
    exact key b a hab

end MatedCRT.KilledOccupation
