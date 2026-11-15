import MatedCRT.FirstPass.Derived.FiniteDomainBrownianEndpointSelector

/-! Prescribed error bounds for stopped Brownian endpoint selector couplings. -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set
open scoped Topology

namespace MatedCRT.BrownianExitLawIdentification

/-- For any positive error budget, the selector coupling controls disagreement
and separation uniformly for nearby starts in finitely many compact sets. -/
theorem finite_uniform_nearby_stoppedBrownian_endpoint_selector_error_le_budget
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
        finitePartitionCoupling (μ j n v : Measure (Euc 2))
          ((stoppedBrownianLaw (U j) z ρ).map CurveSpace.endPoint) S S
          {q | cellSelector S select q.1 ≠ cellSelector S select q.2 ∨
            r ≤ dist q.1 q.2} ≤ ENNReal.ofReal ε := by
  have hden : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hsmall : 0 < ε / ((Fintype.card ι : ℝ) + 1) := div_pos hε hden
  obtain ⟨δ, hδ, hbound⟩ :=
    finite_uniform_nearby_stoppedBrownian_endpoint_selector_error_le U K hU hUb hK hKU
      ρ hρ V p μ hLP S select hS hd hnull hcover r hdiam hsmall
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hbound] with n hn
  intro j v z hz
  refine (hn j v z hz).trans (ENNReal.ofReal_le_ofReal ?_)
  have hnum : (Fintype.card ι : ℝ) * ε ≤ ε * ((Fintype.card ι : ℝ) + 1) := by
    nlinarith
  simpa only [mul_div_assoc] using (div_le_iff₀ hden).2 hnum

end MatedCRT.BrownianExitLawIdentification
