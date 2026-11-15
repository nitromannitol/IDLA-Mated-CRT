import MatedCRT.FirstPass.Derived.ShiftedAreaCellConfig
import MatedCRT.FirstPass.Derived.SrwReversibleSteps
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple

/-! # Random walks on shifted Brownian area cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS MatedCRTHarmonic.MatedCRT

/-- A locally finite Brownian-edge walk, relabelled by shifted area cells, has the
corresponding cell random-walk law. -/
theorem shiftedAreaCellConfig_isSRWLaw_bmEdgeCount
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (w : Path2)
    (hlf : IsLocallyFinite ε w) (a : ℤ) :
    (shiftedAreaCellConfig h hε θ (bmEdgeCount ε (fun t => (w t).1)
      (fun t => (w t).2))).IsSRWLaw (shiftedEuclideanCellEquiv h hε θ a)
      ((srwLaw (bmEdgeCount ε (fun t => (w t).1) (fun t => (w t).2)) a).map
        (fun p n => shiftedEuclideanCellEquiv h hε θ (p n))) := by
  have hm := FirstPass.Derived.isLocallyFiniteMult_bmEdgeCount hlf hε.le
  apply shiftedAreaCellConfig_isSRWLaw h hε θ _ hm
  intro k
  exact Nat.pos_of_ne_zero (mdeg_ne_zero_of_ne_zero hm
    (bmEdgeCount_succ_ne_zero hε.le w.continuous.fst _ k))

end MatedCRT
