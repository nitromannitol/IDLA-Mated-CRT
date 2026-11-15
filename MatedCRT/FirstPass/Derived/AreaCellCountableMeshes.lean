import MatedCRT.FirstPass.Derived.AreaCellRootIndices

/-! # Local finiteness across countably many meshes -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic

/-- For any countable collection of positive meshes, almost surely every
compact set meets only finitely many integer-labelled cells at each mesh. -/
theorem MatedCRTEnv.IsValid.ae_finite_areaCell_indices_meeting_compact_countable
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ι : Type*} [Countable ι] (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∀ᵐ ω ∂S.P, ∀ i : ι, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      ∀ K : Set ReflectedGMS.Plane, IsCompact K →
        {a : ℤ | ((euclideanCell (ε i) (S.η ω) h.1 (hε i) a :
          Set ReflectedGMS.Plane) ∩ K).Nonempty}.Finite := by
  apply ae_all_iff.mpr
  intro i
  filter_upwards [hS.ae_areaCellConfig_isCellConfiguration S (hε i)] with ω hω
  obtain ⟨h, hv, _, _⟩ := hω
  exact ⟨h, fun K hK => finite_areaCell_indices_meeting_compact h (hε i)
    (S.mult (ε i) ω) hv hK⟩

end MatedCRT
