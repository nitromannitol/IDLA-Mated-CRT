import MatedCRT.FirstPass.S2h
import MatedCRT.FirstPass.S2h.LogZero
import MatedCRT.FirstPass.S2h.ScaledField

/-!
# The two cone null-hull steps from the external inputs (fp-S2h, z1, round 20)

`coneBadNullHull_of_log` and `coneClosureGoodMeasureLaw_of_log` (`FirstPass/S2h.lean`) reduce the cone steps
`ConeBadNullHullStep` and `ConeClosureGoodMeasureLawStep` to the log-GFF code step `LogCertCodeNullStep`. This file proves
that step from the zero law at radius `1/2` (`halfPlateauNull_of_inputs`, `FirstPass/S2h/ScaledField.lean`) and the
analytic code set, and assembles the two cone steps. The inputs are the frozen Props `FrozenUniversalMeasurabilityOfAnalytic`,
`FrozenDiskGreenNonnegCont`, `FrozenSuperharmonicMinimumPrinciple`, `FrozenGreenDiscPole`, `FrozenConeLogLocalCodeLaw`,
`FrozenInsertionCoordinateRule`, `FrozenLQGTestIntegralMeasurable`, and the cited statements `LeastSupersolutionMemStmt`
(HB Lemma 3.1), `ClusterMonotoneStmt`, `ClusterCompatibilityStmt`, `VolumeGrowthStmt`, `LeastSupersolutionMemOfVolumeGrowthStmt`.
-/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls
open scoped ENNReal

/-- The log-GFF code step for every admissible exact code pair (fp-S2h, z1, round 20): from the zero law at radius `1/2`
and the measurability of the LQG measure of the whole-plane field. -/
theorem logCertCodeNull_of_inputs (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF3 : FrozenDiskGreenNonnegCont) (hHB : LeastSupersolutionMemStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hmono : ClusterMonotoneStmt.{0}) (hcomp : ClusterCompatibilityStmt.{0})
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hpole : FrozenGreenDiscPole) :
    ∀ (φs : ℕ → ℂ → ℝ) (B : Set (ℕ → ℝ)), CertTestFamily φs → CertCodeExactStep φs B →
      LogCertCodeNullStep φs B := by
  intro φs B hfam hexact
  have hcodeM : Measurable (localCode φs) :=
    Measurable.of_eval fun k => measurable_integral_measure_real (hfam k).1.measurable
  exact logCertCodeNull_of_half hF1 hmin hpole hcomp (halfPlateauNull_of_inputs hF1 hF3 hHB hK hmono hcomp)
    φs B hexact.1 hexact.2 (by
      intro γ hγ hγ2 Ω _ P hC hcirc μ hP hgff hlgm
      exact hcodeM.comp_aemeasurable (aemeasurable_lqgMeasure_of_wholePlane hgff hlgm))

/-- **The cone bad null hull step `ConeBadNullHullStep` from the external inputs (fp-S2h, z1, round 20).** -/
theorem coneBadNullHull_of_inputs (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF3 : FrozenDiskGreenNonnegCont) (hHB : LeastSupersolutionMemStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hmono : ClusterMonotoneStmt.{0}) (hcomp : ClusterCompatibilityStmt.{0})
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hpole : FrozenGreenDiscPole)
    (hlaw : FrozenConeLogLocalCodeLaw) (hmeasF : FrozenLQGTestIntegralMeasurable)
    (hV : VolumeGrowthStmt) (hL : LeastSupersolutionMemOfVolumeGrowthStmt) : ConeBadNullHullStep :=
  coneBadNullHull_of_log hpole hlaw hmeasF hV hL
    (logCertCodeNull_of_inputs hF1 hF3 hHB hK hmono hcomp hmin hpole)

/-- **The cone closure good measure law step `ConeClosureGoodMeasureLawStep` from the external inputs (fp-S2h, z1, round
20).** -/
theorem coneClosureGoodMeasureLaw_of_inputs (hF1 : FrozenUniversalMeasurabilityOfAnalytic)
    (hF3 : FrozenDiskGreenNonnegCont) (hHB : LeastSupersolutionMemStmt.{0})
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hmono : ClusterMonotoneStmt.{0}) (hcomp : ClusterCompatibilityStmt.{0})
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hpole : FrozenGreenDiscPole)
    (hlaw : FrozenConeLogLocalCodeLaw) (hmeasF : FrozenLQGTestIntegralMeasurable)
    (hV : VolumeGrowthStmt) (hL : LeastSupersolutionMemOfVolumeGrowthStmt) : ConeClosureGoodMeasureLawStep :=
  coneClosureGoodMeasureLaw_of_log hpole hlaw hmeasF hV hL
    (logCertCodeNull_of_inputs hF1 hF3 hHB hK hmono hcomp hmin hpole)

end MatedCRT
