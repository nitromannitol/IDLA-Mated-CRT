import MatedCRT.FirstPass.Derived.SrwFinCylinder
import MatedCRT.FirstPass.Derived.SrwCellTransition
import MatedCRT.FirstPass.Derived.SrwCellDegree
import LatticeProb.Walk.CellConfigLawRelabel

/-! # Multigraph random-walk laws relabelled by cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- A conductance-preserving relabelling maps the multigraph walk to the cell walk law. -/
theorem isSRWLaw_map_srwLaw (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m)
    (hpos : ∀ a, 0 < mdeg m a) (H : CellConfig) (e : ℤ ≃ H.cells)
    (hc : ∀ a b, H.c (e a) (e b) = (m a b : ℝ)) (a : ℤ) :
    H.IsSRWLaw (e a) ((srwLaw m a).map (fun ω n => e (ω n))) := by
  classical
  let _ : Countable H.cells := Countable.of_equiv ℤ e
  apply LatticeProb.CellConfigSRW.isSRWLaw_map_of_cylinder H e a (srwLaw m a)
    (fun v w => srwStep m v {w})
  · intro n x
    by_cases h : x 0 = a <;> simpa only [h] using
      srwLaw_fin_cylinder m a n x
  · intro v w
    exact srwStep_singleton_eq_cell_transition m hlf H e v w (hpos v) (hc v w)
      (cell_pi_eq_mdeg m hlf H e v (hc v))

end MatedCRT
