import MatedCRT.FirstPass.Derived.FiniteDomainBrownianEndpointSelectorBudget

/-! Probability couplings of planar stopped Brownian endpoints. -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set
open scoped Topology

namespace MatedCRT.BrownianExitLawIdentification

/-- Nearby starts admit a probability coupling with the prescribed marginals
and a uniform bound on selector disagreement or endpoint separation. -/
theorem finite_uniform_nearby_stoppedBrownian_endpoint_selector_coupling
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
    {ι A : Type*} [Fintype ι] (S : ι → Set (Euc 2)) (select : ι → Option A)
    (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hnull : ∀ j i (z : K j),
      ((stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint) (frontier (S i)) = 0)
    (hcover : ∀ j (z : K j),
      ((stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint) (⋃ i, S i) = 1)
    (r : ℝ) (hdiam : ∀ i, ∀ x ∈ S i, ∀ y ∈ S i, dist x y < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ j (v : V j n) (z : K j),
      dist (p j n v) z ≤ δ →
        ∃ π : Measure (Euc 2 × Euc 2), IsProbabilityMeasure π ∧
          π.fst = (μ j n v : Measure (Euc 2)) ∧
          π.snd = (stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint ∧
          π {q | cellSelector S select q.1 ≠ cellSelector S select q.2 ∨
            r ≤ dist q.1 q.2} ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hbound⟩ :=
    finite_uniform_nearby_stoppedBrownian_endpoint_selector_error_le_budget
      U K hU hUb hK hKU ρ hρ V p μ hLP S select hS hd hnull hcover r hdiam hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hbound] with n hn
  intro j v z hz
  let ν : Measure (Euc 2) := (stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint
  have : IsProbabilityMeasure ν := by
    change IsProbabilityMeasure
      (stoppedBrownianEndpointProbability (U j) (hU j) ρ hρ z : Measure (Euc 2))
    infer_instance
  have hspec := finitePartitionCoupling_spec (μ j n v : Measure (Euc 2)) ν hS hS hd hd
  exact ⟨finitePartitionCoupling (μ j n v : Measure (Euc 2)) ν S S,
    hspec.1, hspec.2.1, hspec.2.2.1, hn j v z hz⟩

end MatedCRT.BrownianExitLawIdentification
