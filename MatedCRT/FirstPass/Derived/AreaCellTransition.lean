import MatedCRT.FirstPass.Derived.AreaCellConfig
import MatedCRT.FirstPass.Derived.SrwCellDegree
import MatedCRT.FirstPass.Derived.SrwCellTransition
import MatedCRT.Proofs.Infra.MatingOfTrees
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple

/-! # Transitions on the mated-CRT curve cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- Every vertex of a locally finite mated-CRT map has positive degree. -/
theorem MatedCRTEnv.mult_mdeg_pos {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (a : ℤ) :
    0 < mdeg (S.mult ε ω) a :=
  Nat.pos_of_ne_zero (mdeg_ne_zero_of_ne_zero hlf (S.mult_succ_ne_zero hε ω a))

/-- Total conductance of a curve cell equals its integer vertex degree. -/
theorem areaCellConfig_pi_eq_mdeg {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) {μ : Measure ℂ}
    (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (a : ℤ) :
    (areaCellConfig h hε (S.mult ε ω)).pi (euclideanCellEquiv h hε a) =
      (mdeg (S.mult ε ω) a : ℝ) :=
  cell_pi_eq_mdeg (S.mult ε ω) hlf _ _ a (areaCellConfig_conductance h hε _ a)

/-- Total conductance is positive at every curve cell of a locally finite map. -/
theorem areaCellConfig_pi_pos {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) {μ : Measure ℂ}
    (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (A : (areaCellConfig h hε (S.mult ε ω)).cells) :
    0 < (areaCellConfig h hε (S.mult ε ω)).pi A := by
  obtain ⟨a, rfl⟩ := (euclideanCellEquiv h hε).surjective A
  rw [areaCellConfig_pi_eq_mdeg S ω h hε hlf a]
  exact Nat.cast_pos.mpr (S.mult_mdeg_pos hε.le ω hlf a)

/-- The integer walk and curve-cell walk have the same one-step transitions. -/
theorem areaCellConfig_srwStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) {μ : Measure ℂ}
    (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (a b : ℤ) :
    srwStep (S.mult ε ω) a {b} = ENNReal.ofReal
      ((areaCellConfig h hε (S.mult ε ω)).transition
        (euclideanCellEquiv h hε a) (euclideanCellEquiv h hε b)) :=
  srwStep_singleton_eq_cell_transition (S.mult ε ω) hlf _ _ a b
    (S.mult_mdeg_pos hε.le ω hlf a) (areaCellConfig_conductance h hε _ a b)
    (areaCellConfig_pi_eq_mdeg S ω h hε hlf a)

end MatedCRT
