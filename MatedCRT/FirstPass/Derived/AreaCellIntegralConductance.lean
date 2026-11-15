import MatedCRT.FirstPass.Derived.ValidAreaCellGMSLaw

/-! # Integral conductances of area-cell configurations -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory ReflectedGMS.GMS

/-- Each area-cell conductance is zero or at least one, including outside the
cell configuration. -/
theorem areaCellConfig_conductance_eq_zero_or_one_le
    {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (A B : Cell) :
    (areaCellConfig h hε m).c A B = 0 ∨ 1 ≤ (areaCellConfig h hε m).c A B := by
  classical
  unfold areaCellConfig
  dsimp only
  split_ifs with ha hb
  · by_cases hz : m ((euclideanCellEquiv h hε).symm ⟨A, ha⟩)
        ((euclideanCellEquiv h hε).symm ⟨B, hb⟩) = 0
    · left
      rw [hz, Nat.cast_zero]
    · right
      exact Nat.one_le_cast_iff_ne_zero.mpr hz
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- A realization agreeing almost surely with the area-cell configuration has
conductances zero or at least one on the same event. -/
theorem ae_areaCellConfig_conductance_eq_zero_or_one_le
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {ε : ℝ} (hε : 0 < ε) (F : Ω → GMSSpace)
    (hF_eq : ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      (F ω).1 = areaCellConfig h hε (S.mult ε ω)) :
    ∀ᵐ ω ∂S.P, ∀ A B : Cell,
      (F ω).1.c A B = 0 ∨ 1 ≤ (F ω).1.c A B := by
  filter_upwards [hF_eq] with ω hω
  obtain ⟨h, hF⟩ := hω
  intro A B
  rw [hF]
  exact areaCellConfig_conductance_eq_zero_or_one_le h hε (S.mult ε ω) A B

end MatedCRT
