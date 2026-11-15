import MatedCRT.FirstPass.Derived.BrownianStoppedEndpointContinuity
import LatticeProb.Prob.FiniteDomainCellComparison

/-! Comparison of walk endpoint laws with planar Brownian exit laws. -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne
open scoped Topology

namespace MatedCRT.BrownianExitLawIdentification

/-- Uniform exit-law convergence gives a common cell-mass comparison for
nearby starting points in a finite family of compact interior sets. -/
theorem finite_uniform_nearby_stoppedBrownian_endpoint_cell_error
    {J : Type*} [Fintype J] (U K : J → Set (Euc 2))
    (hU : ∀ j, IsOpen (U j)) (hUb : ∀ j, Bornology.IsBounded (U j))
    (hK : ∀ j, IsCompact (K j)) (hKU : ∀ j, K j ⊆ U j)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ)
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → K j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (Euc 2))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc 2))
        (stoppedBrownianEndpointProbability (U j) (hU j) ρ hρ (p j n v) :
          Measure (Euc 2)) < ε)
    {ι : Type*} [Fintype ι] (S : ι → Set (Euc 2))
    (hnull : ∀ j i (z : K j),
      ((stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint) (frontier (S i)) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : K j),
      dist (p j n v) z ≤ δ → ∀ i,
        |((μ j n v : Measure (Euc 2)) (S i)).toReal -
          (((stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint) (S i)).toReal| ≤ ε := by
  let (j : J) : CompactSpace (K j) := isCompact_iff_compactSpace.mp (hK j)
  have h := LatticeProb.finite_uniform_nearby_cell_mass_error
    (fun j => K j) V p μ
    (fun j z => stoppedBrownianEndpointProbability (U j) (hU j) ρ hρ z)
    (fun j => continuous_stoppedBrownianEndpointProbability_on
      (hU j) (hUb j) (hKU j) ρ hρ)
    hLP S (by simpa only [stoppedBrownianEndpointProbability, ProbabilityMeasure.coe_mk] using hnull) hε
  simpa only [stoppedBrownianEndpointProbability, ProbabilityMeasure.coe_mk] using h

end MatedCRT.BrownianExitLawIdentification
