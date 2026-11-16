import MatedCRT.FirstPass.Derived.ShiftedPaperMultiplicity
import LatticeProb.LQG.CoupledAreaClockCells

/-! # Multiplicities of cells under the coupled area clock -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace MatedCRT

/-- The shifted reference-curve multiplicity counts components of the cone-curve
interval images with the endpoints transformed by the coupled area clock. -/
theorem ae_shifted_cellMult_eq_area_clock_components
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ θ : ℝ, ∀ j k : ℤ,
      cellMult ε (fun t => η₀ ω (t + ε * θ)) j k =
        let clock := CellScaling.JointScalingO.clock γ
          (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) (η₀ ω)
        let imageCell : ℤ → Set ℂ := fun i => η ω '' Icc
          (clock (ε * ((i : ℝ) - 1 + θ))) (clock (ε * ((i : ℝ) + θ)))
        if j = k then 0 else
          {C ∈ HarmonicBalls.connectedComponentsIn (imageCell j ∩ imageCell k) |
            ¬ C.Subsingleton}.ncard := by
  filter_upwards [LatticeProb.ae_shifted_cell_eq_image_area_clock hC hγ] with ω hω
  intro ε hε θ j k
  have h := shifted_cell_component_count_eq_cellMult_timeShift (η₀ ω) hε.le θ j k
  rw [hω ε hε θ j, hω ε hε θ k] at h
  exact h.symm

end MatedCRT
