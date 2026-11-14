import MatedCRT.FirstPass.Derived.AreaCellTransition

/-! # Support of multigraph steps under cell relabelling -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS
open scoped ENNReal

/-- A positive-degree step remains in any set retaining the conductance neighbors. -/
theorem srwStep_cell_region_compl_null
    (m : ℤ → ℤ → ℕ) (hlf : IsLocallyFiniteMult m) (H : CellConfig)
    (e : ℤ ≃ H.cells) (a : ℤ) (hdeg : 0 < mdeg m a)
    (hc : ∀ b, H.c (e a) (e b) = (m a b : ℝ))
    (R : Set H.cells) (hretain : ∀ b, e b ∉ R → H.c (e a) (e b) = 0) :
    srwStep m a {b | e b ∉ R} = 0 := by
  classical
  apply measure_mono_null (t := ⋃ b : ℤ, if e b ∈ R then ∅ else {b})
  · intro b hb
    change e b ∉ R at hb
    exact mem_iUnion.mpr ⟨b, by simp [hb]⟩
  · apply measure_iUnion_null
    intro b
    by_cases hb : e b ∈ R
    · simp [hb]
    · simp only [hb, ↓reduceIte]
      have hm : m a b = 0 := by
        have hh := hretain b hb
        rw [hc b] at hh
        exact_mod_cast hh
      have hp : (mdeg m a : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hdeg
      have hz := FirstPass.Derived.mdeg_mul_srwStep_singleton hlf a b
      rw [hm, Nat.cast_zero] at hz
      exact (mul_eq_zero.mp hz).resolve_left hp

/-- A mated-CRT step stays in a region retaining the current cell's neighbors. -/
theorem areaCellConfig_srwStep_region_compl_null {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ω : Ω) {μ : Measure ℂ}
    (h : IsAreaParametrized μ (S.η ω)) {ε : ℝ} (hε : 0 < ε)
    (hlf : IsLocallyFiniteMult (S.mult ε ω)) (a : ℤ)
    (R : Set (areaCellConfig h hε (S.mult ε ω)).cells)
    (hretain : ∀ b, euclideanCellEquiv h hε b ∉ R →
      (areaCellConfig h hε (S.mult ε ω)).c (euclideanCellEquiv h hε a)
        (euclideanCellEquiv h hε b) = 0) :
    srwStep (S.mult ε ω) a {b | euclideanCellEquiv h hε b ∉ R} = 0 :=
  srwStep_cell_region_compl_null (S.mult ε ω) hlf _ _ a
    (S.mult_mdeg_pos hε.le ω hlf a) (areaCellConfig_conductance h hε _ a) R hretain

end MatedCRT
