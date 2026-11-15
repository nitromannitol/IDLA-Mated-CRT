import MatedCRT.FirstPass.Derived.MatingConePairDimension
import LatticeProb.Prob.ConeVectorPairDimension

/-! # Cone triple-point dimension from cone-vector bounds -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal
open MatedCRTHarmonic.MatedCRT (lrCoord Path2 IsCorrelatedBM2)

namespace MatedCRT

/-- Bounds for forward and backward cone vectors in both time orientations
bound the dimension of the cone triple points. -/
theorem ae_dimH_coneTriplePoints_le_of_coneVectors
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {d : ℝ≥0∞}
    (hf : ∀ᵐ ω ∂μ, dimH (LatticeProb.forwardConeVectors
      (lrCoord 0 · ω) (lrCoord 1 · ω)) ≤ d)
    (hb : ∀ᵐ ω ∂μ, dimH (LatticeProb.backwardConeVectors
      (lrCoord 0 · ω) (lrCoord 1 · ω)) ≤ d)
    (hfr : ∀ᵐ ω ∂μ, dimH (LatticeProb.forwardConeVectors
      (fun t => lrCoord 0 (-t) ω) (fun t => lrCoord 1 (-t) ω)) ≤ d)
    (hbr : ∀ᵐ ω ∂μ, dimH (LatticeProb.backwardConeVectors
      (fun t => lrCoord 0 (-t) ω) (fun t => lrCoord 1 (-t) ω)) ≤ d) :
    ∀ᵐ ω ∂μ, dimH (coneTriplePoints ω) ≤ d := by
  have hp := LatticeProb.CorrelatedBM.ae_dimH_direct_excursion_pairs_le_of_coneVectors
    hμ hf hb hfr hbr
  filter_upwards [hp] with ω hω
  apply dimH_coneTriplePoints_le_of_pairs
  exact hω

end MatedCRT
