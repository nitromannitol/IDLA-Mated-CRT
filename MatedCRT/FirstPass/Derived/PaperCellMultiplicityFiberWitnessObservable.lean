import MatedCRT.FirstPass.Derived.PaperCellMultiplicityFiberWitness

/-! # Measurable cell multiplicities from fiber witnesses -/

set_option autoImplicit false

open Function MeasureTheory Topology

namespace MatedCRT

/-- A measurable prescribed array transfers to a proper surjective curve when
almost every sample has a proper surjective witness with the same fibers and
prescribed cell multiplicities. No measurable choice of witness is needed. -/
theorem aemeasurable_cellMult_of_fiber_witness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Ω → ℝ → ℂ) (ε : Ω → ℝ) (R : Ω → ℝ → ℝ → Prop)
    (m : Ω → ℤ → ℤ → ℕ) (hm : AEMeasurable m μ)
    (hg : ∀ᵐ ω ∂μ, IsProperMap (g ω) ∧ Surjective (g ω) ∧
      ∀ s t, g ω s = g ω t ↔ R ω s t)
    (hw : ∀ᵐ ω ∂μ, ∃ f : ℝ → ℂ, IsProperMap f ∧ Surjective f ∧
      (∀ s t, f s = f t ↔ R ω s t) ∧
      ∀ j k, cellMult (ε ω) f j k = m ω j k) :
    AEMeasurable (fun ω (j k : ℤ) => cellMult (ε ω) (g ω) j k) μ := by
  apply hm.congr
  filter_upwards [ae_cellMult_eq_of_fiber_witness μ g ε R m hg hw] with ω hω
  funext j k
  exact (hω j k).symm

end MatedCRT
