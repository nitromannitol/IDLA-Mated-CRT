import MatedCRT.FirstPass.Derived.ValidAreaCellConfiguration
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid

/-! # Integer labels of cells meeting compact sets -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set ReflectedGMS.GMS MatedCRTHarmonic

/-- Only finitely many integer-labelled curve cells meet a compact set in a
valid cell configuration. -/
theorem finite_areaCell_indices_meeting_compact {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hv : (areaCellConfig h hε m).IsCellConfiguration)
    {K : Set ReflectedGMS.Plane} (hK : IsCompact K) :
    {a : ℤ | ((euclideanCell ε η h.1 hε a : Set ReflectedGMS.Plane) ∩ K).Nonempty}.Finite := by
  have hf := CellConfig.finite_restrict_of_isCompact hv hK
  have hp := hf.preimage (euclideanCell_injective h hε).injOn
  apply hp.subset
  intro a ha
  exact ⟨⟨a, rfl⟩, ha⟩

/-- Only finitely many integer-labelled cells contain a given point. -/
theorem finite_areaCell_indices_containing {μ : Measure ℂ} {η : ℝ → ℂ}
    (h : IsAreaParametrized μ η) {ε : ℝ} (hε : 0 < ε) (m : ℤ → ℤ → ℕ)
    (hv : (areaCellConfig h hε m).IsCellConfiguration) (z : ReflectedGMS.Plane) :
    {a : ℤ | z ∈ (euclideanCell ε η h.1 hε a : Set ReflectedGMS.Plane)}.Finite := by
  apply (finite_areaCell_indices_meeting_compact h hε m hv (isCompact_singleton :
    IsCompact ({z} : Set ReflectedGMS.Plane))).subset
  intro a ha
  exact ⟨z, ha, rfl⟩

/-- At a fixed positive mesh, almost surely only finitely many curve cells
contain the origin. -/
theorem MatedCRTEnv.IsValid.ae_finite_areaCell_indices_containing_zero
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂S.P, ∃ h : IsAreaParametrized (S.μ ω) (S.η ω),
      {a : ℤ | (0 : ReflectedGMS.Plane) ∈
        (euclideanCell ε (S.η ω) h.1 hε a : Set ReflectedGMS.Plane)}.Finite := by
  filter_upwards [hS.ae_areaCellConfig_isCellConfiguration S hε] with ω hω
  obtain ⟨h, hv, _, _⟩ := hω
  exact ⟨h, finite_areaCell_indices_containing h hε (S.mult ε ω) hv 0⟩

end MatedCRT
