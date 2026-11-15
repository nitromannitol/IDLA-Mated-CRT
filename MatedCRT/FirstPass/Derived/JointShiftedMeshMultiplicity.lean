import MatedCRT.FirstPass.Derived.ShiftedMeshMultiplicity
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentGreen

/-! # Joint measurability of shifted-grid multiplicities -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory
open MatedCRTHarmonic

/-- Boundary-length edge multiplicity is jointly measurable in the continuous
path, the positive mesh size and the real grid shift. -/
theorem measurable_bmEdgeCount_shiftedMesh (j k : ℤ) :
    Measurable (fun p : MatedCRTHarmonic.MatedCRT.Path2 × {ε : ℝ // 0 < ε} × ℝ =>
      bmEdgeCount p.2.1.1 (fun t => (p.1 (t + p.2.1.1 * p.2.2)).1)
        (fun t => (p.1 (t + p.2.1.1 * p.2.2)).2) j k) := by
  have hpath : Continuous (fun p : MatedCRTHarmonic.MatedCRT.Path2 × {ε : ℝ // 0 < ε} × ℝ =>
      LatticeProb.shiftedMeshPath p.1 p.2.1.1 p.2.2) :=
    LatticeProb.continuous_shiftedMeshPath.comp
      (continuous_fst.prodMk ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd)))
  have hm := (measurable_bmEdgeCount_path 1 j k).comp hpath.measurable
  convert hm using 1
  funext p
  exact congrFun (congrFun (bmEdgeCount_shiftedMeshPath p.2.1.2 p.2.2 p.1) j) k |>.symm

/-- The full array of shifted-grid edge multiplicities is jointly measurable. -/
theorem measurable_bmEdgeCount_shiftedMesh_array :
    Measurable (fun p : MatedCRTHarmonic.MatedCRT.Path2 × {ε : ℝ // 0 < ε} × ℝ =>
      bmEdgeCount p.2.1.1 (fun t => (p.1 (t + p.2.1.1 * p.2.2)).1)
        (fun t => (p.1 (t + p.2.1.1 * p.2.2)).2)) :=
  Measurable.of_eval fun j => Measurable.of_eval fun k => measurable_bmEdgeCount_shiftedMesh j k

end MatedCRT
