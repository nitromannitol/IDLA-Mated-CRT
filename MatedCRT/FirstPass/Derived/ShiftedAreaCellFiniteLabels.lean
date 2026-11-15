import MatedCRT.FirstPass.Derived.ShiftedAreaCellConfig
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid

/-! # Compact incidence of shifted area cells -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter ReflectedGMS.GMS

/-- A compact set meets only finitely many shifted integer-labelled area cells
when the shifted cells form a cell configuration. -/
theorem finite_shiftedAreaCell_indices_meeting_compact
    {μ : Measure ℂ} {η : ℝ → ℂ} (h : IsAreaParametrized μ η)
    {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (m : ℤ → ℤ → ℕ)
    (hv : (shiftedAreaCellConfig h hε θ m).IsCellConfiguration)
    {K : Set ReflectedGMS.Plane} (hK : IsCompact K) :
    {a : ℤ | ((euclideanCell ε (fun t => η (t + ε * θ))
      (h.1.comp (continuous_id.add continuous_const)) hε a :
        Set ReflectedGMS.Plane) ∩ K).Nonempty}.Finite := by
  have hf := CellConfig.finite_restrict_of_isCompact hv hK
  have hp := hf.preimage (shiftedEuclideanCell_injective h hε θ).injOn
  apply hp.subset
  intro a ha
  exact ⟨⟨a, rfl⟩, ha⟩

/-- Almost-sure validity of a shifted cell configuration gives compact
incidence for its labels on the original probability space. -/
theorem ae_finite_shiftedAreaCell_indices_meeting_compact
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {ε : ℝ} (hε : 0 < ε) (η : Ω → C(ℝ, ℂ)) (θ : Ω → ℝ)
    (μ : Ω → Measure ℂ) (H : Ω → CellConfig)
    (m : Ω → ℤ → ℤ → ℕ)
    (hH : ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
      H ω = shiftedAreaCellConfig h hε (θ ω) (m ω) ∧
        (H ω).IsCellConfiguration) :
    ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
      ∀ K : Set ReflectedGMS.Plane, IsCompact K →
        {a : ℤ | ((euclideanCell ε (fun t => η ω (t + ε * θ ω))
          (h.1.comp (continuous_id.add continuous_const)) hε a :
            Set ReflectedGMS.Plane) ∩ K).Nonempty}.Finite := by
  filter_upwards [hH] with ω ⟨h, heq, hv⟩
  refine ⟨h, fun K hK => ?_⟩
  exact finite_shiftedAreaCell_indices_meeting_compact h hε (θ ω) (m ω)
    (heq ▸ hv) hK

end MatedCRT
