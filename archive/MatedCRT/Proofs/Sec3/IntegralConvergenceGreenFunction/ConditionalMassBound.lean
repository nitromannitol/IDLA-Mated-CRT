import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Domination of conditional GMC errors -/

namespace MatedCRT

open MeasureTheory

/-- Two nonnegative integrable random masses with the same expectation `m`
have L¹ distance at most `2m`. -/
theorem integral_abs_sub_le_twice_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g : Ω → ℝ) (m : ℝ)
    (hf : Integrable f P) (hg : Integrable g P)
    (hf0 : ∀ᵐ ω ∂P, 0 ≤ f ω) (hg0 : ∀ᵐ ω ∂P, 0 ≤ g ω)
    (hfm : (∫ ω, f ω ∂P) = m) (hgm : (∫ ω, g ω ∂P) = m) :
    (∫ ω, |f ω - g ω| ∂P) ≤ 2 * m := by
  have hle : ∀ᵐ ω ∂P, |f ω - g ω| ≤ f ω + g ω := by
    filter_upwards [hf0, hg0] with ω hfω hgω
    rw [abs_le]
    constructor <;> linarith
  calc
    (∫ ω, |f ω - g ω| ∂P) ≤ ∫ ω, (f ω + g ω) ∂P :=
      integral_mono_ae (hf.sub hg).abs (hf.add hg) hle
    _ = 2 * m := by rw [integral_add hf hg, hfm, hgm]; ring

end MatedCRT
