import MatedCRT.FirstPass.Derived.PaperCellMultiplicityFiberWitnessObservable
import MatedCRT.FirstPass.Derived.JointShiftedMeshMultiplicity

/-! # Cell multiplicities from a shifted contour witness -/

set_option autoImplicit false

open Function MeasureTheory Topology

namespace MatedCRT

/-- A shifted boundary-length edge array gives measurable cell multiplicities
when proper surjective curves with the prescribed fibers and multiplicities
exist almost surely. -/
theorem aemeasurable_cellMult_of_shifted_contour_fiber_witness
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : Ω → MatedCRTHarmonic.MatedCRT.Path2)
    (ε : Ω → {e : ℝ // 0 < e}) (θ : Ω → ℝ)
    (g : Ω → ℝ → ℂ) (R : Ω → ℝ → ℝ → Prop)
    (hB : AEMeasurable B μ) (hε : AEMeasurable ε μ) (hθ : AEMeasurable θ μ)
    (hg : ∀ᵐ ω ∂μ, IsProperMap (g ω) ∧ Surjective (g ω) ∧
      ∀ s t, g ω s = g ω t ↔ R ω s t)
    (hw : ∀ᵐ ω ∂μ, ∃ f : ℝ → ℂ, IsProperMap f ∧ Surjective f ∧
      (∀ s t, f s = f t ↔ R ω s t) ∧
      ∀ j k, cellMult (ε ω).1 f j k =
        bmEdgeCount (ε ω).1 (fun t => (B ω (t + (ε ω).1 * θ ω)).1)
          (fun t => (B ω (t + (ε ω).1 * θ ω)).2) j k) :
    AEMeasurable (fun ω (j k : ℤ) => cellMult (ε ω).1 (g ω) j k) μ := by
  let m : Ω → ℤ → ℤ → ℕ := fun ω =>
    bmEdgeCount (ε ω).1 (fun t => (B ω (t + (ε ω).1 * θ ω)).1)
      (fun t => (B ω (t + (ε ω).1 * θ ω)).2)
  have hm : AEMeasurable m μ := by
    change AEMeasurable ((fun p : MatedCRTHarmonic.MatedCRT.Path2 × {e : ℝ // 0 < e} × ℝ =>
      bmEdgeCount p.2.1.1 (fun t => (p.1 (t + p.2.1.1 * p.2.2)).1)
        (fun t => (p.1 (t + p.2.1.1 * p.2.2)).2)) ∘
          (fun ω => (B ω, ε ω, θ ω))) μ
    exact measurable_bmEdgeCount_shiftedMesh_array.comp_aemeasurable (hB.prodMk (hε.prodMk hθ))
  exact aemeasurable_cellMult_of_fiber_witness μ g (fun ω => (ε ω).1) R m hm hg hw

end MatedCRT
