import MatedCRT.FirstPass.Derived.SrwCellLaw
import MatedCRT.FirstPass.Derived.AreaCellTransition

/-! # Random-walk laws on mated-CRT curve cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- The integer random walk, relabelled by its curve cells, has the cell walk law. -/
theorem MatedCRTEnv.areaCellConfig_isSRWLaw {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) {μ : Measure ℂ}
    (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (a : ℤ) :
    (areaCellConfig h hε (S.mult ε ω)).IsSRWLaw (euclideanCellEquiv h hε a)
      ((srwLaw (S.mult ε ω) a).map (fun p n => euclideanCellEquiv h hε (p n))) :=
  isSRWLaw_map_srwLaw (S.mult ε ω) hlf (S.mult_mdeg_pos hε.le ω hlf)
    (areaCellConfig h hε (S.mult ε ω)) (euclideanCellEquiv h hε)
    (areaCellConfig_conductance h hε (S.mult ε ω)) a

end MatedCRT
