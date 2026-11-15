import MatedCRT.FirstPass.Derived.PaperCellMultiplicityFibers

/-! # Cell multiplicity from a curve with prescribed fibers -/

set_option autoImplicit false

open Function MeasureTheory Topology

namespace MatedCRT

/-- An almost-sure reference curve with prescribed fibers and cell
multiplicities transfers its multiplicity array to any proper surjective curve
with those same fibers. The reference curve need not be measurably selected. -/
theorem ae_cellMult_eq_of_fiber_witness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Ω → ℝ → ℂ) (ε : Ω → ℝ) (R : Ω → ℝ → ℝ → Prop)
    (m : Ω → ℤ → ℤ → ℕ)
    (hg : ∀ᵐ ω ∂μ, IsProperMap (g ω) ∧ Surjective (g ω) ∧
      ∀ s t, g ω s = g ω t ↔ R ω s t)
    (hw : ∀ᵐ ω ∂μ, ∃ f : ℝ → ℂ, IsProperMap f ∧ Surjective f ∧
      (∀ s t, f s = f t ↔ R ω s t) ∧
      ∀ j k, cellMult (ε ω) f j k = m ω j k) :
    ∀ᵐ ω ∂μ, ∀ j k, cellMult (ε ω) (g ω) j k = m ω j k := by
  filter_upwards [hg, hw] with ω hgω hwω
  obtain ⟨f, hf, hfs, hfr, hfm⟩ := hwω
  intro j k
  calc
    cellMult (ε ω) (g ω) j k = cellMult (ε ω) f j k :=
      (cellMult_eq_of_proper_maps_same_fibers f (g ω) hf hgω.1 hfs hgω.2.1
        (fun s t => (hfr s t).trans (hgω.2.2 s t).symm) (ε ω) j k).symm
    _ = m ω j k := hfm j k

end MatedCRT
