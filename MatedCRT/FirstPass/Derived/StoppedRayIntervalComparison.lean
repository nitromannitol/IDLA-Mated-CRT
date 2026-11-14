import MatedCRT.FirstPass.Derived.LocalCurveMetricRadiusPick
import LatticeProb.Topology.IntervalReparamEDist

/-! # Finite interval and stopped ray distances -/

set_option autoImplicit false
open Set
open scoped ENNReal NNReal

namespace MatedCRT.LocalCurveMetricPick

open LatticeProb.IntervalReparamEDist

/-- A finite interval in the extended-duration convention is the corresponding closed interval. -/
def timeIntervalOrderIso (T : ℝ≥0) : TimeInterval (T : ℝ≥0∞) ≃o Icc (0 : ℝ≥0) T where
  toFun t := ⟨t.1, zero_le, ENNReal.coe_le_coe.mp t.2⟩
  invFun t := ⟨t.1, ENNReal.coe_le_coe.mpr t.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

/-- The ray distance of constant-tail extensions is bounded by the distance of their finite
intervals, including the case in which the interval time-change type is empty. -/
theorem cmpEDist_stopped_le_intervalEDist (f g : ℝ≥0 → ℂ) (T U : ℝ≥0) :
    cmpEDist (fun t => f (min t T)) (fun t => g (min t U)) ≤
      intervalEDist f g (T : ℝ≥0∞) (U : ℝ≥0∞) := by
  refine le_iInf fun φ => ?_
  let ψ : Icc (0 : ℝ≥0) T ≃o Icc (0 : ℝ≥0) U :=
    (timeIntervalOrderIso T).symm.trans (φ.trans (timeIntervalOrderIso U))
  refine iInf_le_of_le (extendIccOrderIso ψ) (iSup_le fun t => ?_)
  have ht : min (extendIccOrderIso ψ t) U = (ψ (clipIcc T t) : ℝ≥0) :=
    min_extendIccFun ψ t
  dsimp only
  rw [ht]
  have h := le_iSup (fun s : TimeInterval (T : ℝ≥0∞) =>
    edist (f s.1) (g (φ s).1)) ((timeIntervalOrderIso T).symm (clipIcc T t))
  simpa [ψ, timeIntervalOrderIso, clipIcc] using h

end MatedCRT.LocalCurveMetricPick
