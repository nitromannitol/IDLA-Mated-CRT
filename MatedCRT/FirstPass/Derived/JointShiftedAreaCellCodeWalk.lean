import MatedCRT.FirstPass.Derived.ShiftedAreaCellCode
import MatedCRT.FirstPass.Derived.JointMeshShiftedSelectedWalk
import MatedCRT.FirstPass.Derived.ConeShiftedSelectedWalkLaw

/-! # Joint measurability of shifted cell codes and selected walk laws -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set Filter Topology ReflectedGMS.GMS
open scoped NNReal

/-- A valid matching shifted configuration and its selected walk law have an
almost-everywhere measurable joint code and law. The phase is in mesh units. -/
theorem aemeasurable_shiftedAreaCellConfig_code_selectedWalkLaw
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {ε : ℝ} (hε : 0 < ε) (m : ℝ≥0)
    (η : Ω → C(ℝ, ℂ)) (w : Ω → C(ℝ, ℝ × ℝ))
    (θ : Ω → ℝ) (x : Ω → ℂ) (μ : Ω → Measure ℂ) (H : Ω → CellConfig)
    (hη : Measurable η) (hw : Measurable w) (hθ : Measurable θ) (hx : Measurable x)
    (hcurve : ∀ᵐ ω ∂P, Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      Function.Surjective (η ω))
    (hH : ∀ᵐ ω ∂P, ∃ h : IsAreaParametrized (μ ω) (η ω),
      H ω = shiftedAreaCellConfig h hε (θ ω)
        (bmEdgeCount ε (fun t => (w ω (t + ε * θ ω)).1)
          (fun t => (w ω (t + ε * θ ω)).2)) ∧ (H ω).IsCellConfiguration) :
    AEMeasurable (fun ω => ((H ω).code,
      shiftedSelectedWalkLaw ε m (ε * θ ω) (x ω) (η ω) (w ω))) P := by
  have hc := aemeasurable_shiftedAreaCellConfig_code P hε η w θ μ H hη hw hθ hH
  obtain ⟨F, hF, hFe⟩ := exists_measurable_jointMesh_shifted_selected_walk_law m
  have hf : Measurable (fun ω => F ((⟨ε, hε⟩, ((η ω, w ω), x ω)), ε * θ ω)) :=
    hF.comp ((measurable_const.prodMk ((hη.prodMk hw).prodMk hx)).prodMk
      (measurable_const.mul hθ))
  have hlaw : AEMeasurable (fun ω =>
      shiftedSelectedWalkLaw ε m (ε * θ ω) (x ω) (η ω) (w ω)) P := by
    apply hf.aemeasurable.congr
    filter_upwards [hcurve] with ω ⟨hp, hs⟩
    exact hFe ⟨ε, hε⟩ (η ω) (w ω) (x ω) (ε * θ ω) hp hs
  exact hc.prodMk hlaw

end MatedCRT
