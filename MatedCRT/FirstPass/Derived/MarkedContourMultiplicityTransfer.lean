import MatedCRT.FirstPass.Derived.PaperCellMultiplicityFibers
import LatticeProb.Prob.AnalyticWitnessTransfer
import LatticeProb.Topology.PolishContinuousMap

/-! # Cell multiplicities from a marked contour marginal -/

set_option autoImplicit false

open Function MeasureTheory Set Topology

namespace MatedCRT

/-- A component-count identity transfers from a source law with the same joint
contour and phase marginal when the source and target curves have the same
fibers. The source event must supply the count identity for all pairs. -/
theorem ae_cellMult_eq_shifted_bmEdgeCount_of_marked_marginal
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ((C(ℝ, ℝ × ℝ) × ℝ) × C(ℝ, ℂ))) [IsFiniteMeasure μ]
    (P : Measure Ω) (mark : Ω → C(ℝ, ℝ × ℝ) × ℝ) (g : Ω → ℝ → ℂ)
    (hmark : Measurable mark) (hlaw : P.map mark = μ.map Prod.fst)
    (ε : ℝ) (R : C(ℝ, ℝ × ℝ) × ℝ → ℝ → ℝ → Prop)
    {A : Set ((C(ℝ, ℝ × ℝ) × ℝ) × C(ℝ, ℂ))}
    (hA : NullMeasurableSet A μ) (hfull : ∀ᵐ p ∂μ, p ∈ A)
    (hsource : ∀ p ∈ A, IsProperMap p.2 ∧ Surjective p.2 ∧
      (∀ s t, p.2 s = p.2 t ↔ R p.1 s t) ∧
      ∀ j k, cellMult ε p.2 j k =
        bmEdgeCount ε (fun t => (p.1.1 (t + p.1.2)).1)
          (fun t => (p.1.1 (t + p.1.2)).2) j k)
    (htarget : ∀ᵐ ω ∂P, IsProperMap (g ω) ∧ Surjective (g ω) ∧
      ∀ s t, g ω s = g ω t ↔ R (mark ω) s t) :
    ∀ᵐ ω ∂P, cellMult ε (g ω) =
      bmEdgeCount ε (fun t => ((mark ω).1 (t + (mark ω).2)).1)
        (fun t => ((mark ω).1 (t + (mark ω).2)).2) := by
  have : PolishSpace C(ℝ, ℝ × ℝ) := LatticeProb.polishSpace_continuousMap ℝ (ℝ × ℝ)
  have : PolishSpace C(ℝ, ℂ) := LatticeProb.polishSpace_continuousMap ℝ ℂ
  filter_upwards [LatticeProb.ae_exists_witness_of_marginal_law μ P mark hmark
    hlaw hA hfull, htarget] with ω hw ht
  obtain ⟨f, hf⟩ := hw
  obtain ⟨hp, hs, hrel, hcount⟩ := hsource (mark ω, f) hf
  funext j k
  calc
    cellMult ε (g ω) j k = cellMult ε f j k :=
      (cellMult_eq_of_proper_maps_same_fibers f (g ω) hp ht.1 hs ht.2.1
        (fun s t => (hrel s t).trans (ht.2.2 s t).symm) ε j k).symm
    _ = _ := hcount j k

end MatedCRT
