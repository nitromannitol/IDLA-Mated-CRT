import MatedCRT.Defs.Setting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46TModel

/-! # Area parametrization for the zero-quantum cone -/

set_option autoImplicit false

namespace MatedCRT

open MeasureTheory Set
open scoped NNReal
open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b

/-- The zero-cone cell model has a surjective area-parametrized curve. -/
theorem ae_zeroCone_isAreaParametrized_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, IsAreaParametrized ((l46tZeroConeCellModel D hγ).area ω) (η₀ ω) := by
  filter_upwards [(l46tZeroConeCellModel D hγ).ae_curve_zero,
    (l46tZeroConeCellModel D hγ).ae_area_curve, D.spaceFilling, D.areaParam₀] with
    ω hzero hmass hspace hparam
  refine ⟨(η₀ ω).continuous, hzero, ?_, ?_⟩
  · obtain ⟨φ, hφ0, hη⟩ := hparam.1
    intro z
    obtain ⟨t, ht⟩ := hspace.1 z
    refine ⟨φ.symm t, ?_⟩
    rw [hη, φ.apply_symm_apply, ht]
  · intro a b hab
    exact hmass a b hab.le

end MatedCRT
