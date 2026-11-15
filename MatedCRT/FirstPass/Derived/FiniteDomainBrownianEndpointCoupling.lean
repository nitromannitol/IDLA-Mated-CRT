import MatedCRT.FirstPass.Derived.FiniteDomainBrownianEndpointComparison
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellCouplingError

/-! Couplings of walk endpoints with planar Brownian exit distributions. -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set
open scoped Topology

namespace MatedCRT.BrownianExitLawIdentification

/-- A finite family of planar stopped Brownian endpoint laws admits uniform
nearby-start coupling bounds on common continuity-cell partitions. -/
theorem finite_uniform_nearby_stoppedBrownian_endpoint_coupling_bad_le
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
    (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hnull : ∀ j i (z : K j),
      ((stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint) (frontier (S i)) = 0)
    (hcover : ∀ j (z : K j),
      ((stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint) (⋃ i, S i) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : K j),
      dist (p j n v) z ≤ δ → ∀ B : Set (Euc 2 × Euc 2),
        (∀ i, Disjoint B (S i ×ˢ S i)) →
        finitePartitionCoupling (μ j n v : Measure (Euc 2))
          ((stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint) S S B ≤
            ENNReal.ofReal ((Fintype.card ι : ℝ) * ε) := by
  obtain ⟨δ, hδ, hcompare⟩ :=
    finite_uniform_nearby_stoppedBrownian_endpoint_cell_error U K hU hUb hK hKU
      ρ hρ V p μ hLP S hnull hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hcompare] with n hn
  intro j v z hz B hB
  let ν := stoppedBrownianEndpointProbability (U j) (hU j) ρ hρ z
  have hν : (ν : Measure (Euc 2)) =
      (stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint := rfl
  rw [← hν]
  exact finitePartitionCoupling_bad_le_of_cell_error _ _ hS hS hd hd
    (by simpa only [hν] using hcover j z) (le_of_lt hε)
    (by simpa only [hν] using hn j v z hz) B hB

end MatedCRT.BrownianExitLawIdentification
