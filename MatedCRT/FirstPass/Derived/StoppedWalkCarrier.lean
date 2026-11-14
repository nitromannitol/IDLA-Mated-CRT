import MatedCRT.FirstPass.Derived.StoppedWalkLawMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.CellDomainMeasurable
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentGreen

/-! # Measurability of stopped walk laws on the curve and boundary-length carrier -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set LatticeProb
open scoped NNReal ENNReal
open MatedCRT.ExitCouplingGlue

/-- The stopped walk law is measurable in the continuous curve and boundary-length pair. -/
theorem measurable_stoppedWalkLaw_curve_boundary (ε : ℝ) (D : Set ℂ)
    (hD : IsOpen D ∨ IsClosed D) (m : ℝ≥0) (a : ℤ) :
    Measurable fun p : C(ℝ, ℂ) × C(ℝ, ℝ × ℝ) =>
      (srwLaw (bmEdgeCount ε (fun t => (p.2 t).1) (fun t => (p.2 t).2)) a).map
        (stoppedInterp (vertexPoint ε p.1) m (interiorCellVertices ε p.1 D)) := by
  let V : (C(ℝ, ℂ) × C(ℝ, ℝ × ℝ)) → Set ℤ :=
    fun p => interiorCellVertices ε p.1 D
  have hV : Measurable V := by
    apply measurable_set_iff.mpr
    intro k
    have h1 : MeasurableSet {p : C(ℝ, ℂ) | k ∈ cellVertices ε p D} := by
      rcases hD with hD | hD
      · exact (isOpen_curve_cell_meets ε k D hD).measurableSet
      · exact (isClosed_curve_cell_meets ε k D hD).measurableSet
    have h2 : MeasurableSet {p : C(ℝ, ℂ) | k ∈ cellVertices ε p (frontier D)} :=
      (isClosed_curve_cell_meets ε k (frontier D) isClosed_frontier).measurableSet
    exact measurableSet_setOfPred.mp ((h1.diff h2).preimage measurable_fst)
  have hv : Measurable (fun p : C(ℝ, ℂ) × C(ℝ, ℝ × ℝ) => vertexPoint ε p.1) := by
    apply measurable_pi_iff.2
    intro k
    exact (ContinuousMap.measurable_eval _).comp measurable_fst
  have hM : ∀ j k, Measurable (fun p : C(ℝ, ℂ) × C(ℝ, ℝ × ℝ) =>
      bmEdgeCount ε (fun t => (p.2 t).1) (fun t => (p.2 t).2) j k) := by
    intro j k
    exact (measurable_bmEdgeCount_path ε j k).comp measurable_snd
  exact measurable_stoppedInterp_srwLaw V hV _ hv _ hM m a

end MatedCRT
