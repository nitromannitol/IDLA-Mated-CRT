import MatedCRT.FirstPass.Derived.AreaCellFiniteNeighbors
import MatedCRT.FirstPass.Derived.AreaCellStepSupport

/-! # Finite walk regions for curve cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- A finite family of curve cells admits a finite containing region that
retains every one-step transition from the family. -/
theorem areaCellConfig_exists_finite_walk_region {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) {μ : Measure ℂ}
    (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω))
    (A : Set (areaCellConfig h hε (S.mult ε ω)).cells) (hA : A.Finite) :
    ∃ R : Set (areaCellConfig h hε (S.mult ε ω)).cells,
      R.Finite ∧ A ⊆ R ∧
      (∀ v ∈ A, ∀ w, w ∉ R → (areaCellConfig h hε (S.mult ε ω)).c v w = 0) ∧
      ∀ a : ℤ, euclideanCellEquiv h hε a ∈ A →
        srwStep (S.mult ε ω) a {b | euclideanCellEquiv h hε b ∉ R} = 0 := by
  obtain ⟨R, hR, hAR, hretain⟩ :=
    areaCellConfig_exists_finite_conductance_region h hε (S.mult ε ω) hlf A hA
  refine ⟨R, hR, hAR, hretain, ?_⟩
  intro a ha
  apply areaCellConfig_srwStep_region_compl_null S ω h hε hlf a R
  intro b hb
  exact hretain (euclideanCellEquiv h hε a) ha (euclideanCellEquiv h hε b) hb

end MatedCRT
