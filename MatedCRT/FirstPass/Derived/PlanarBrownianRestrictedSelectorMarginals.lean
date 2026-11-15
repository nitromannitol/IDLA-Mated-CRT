import LatticeProb.Prob.BrownianRestrictedSelectorMarginals
import MatedCRT.FirstPass.Derived.BrownianEndpointParameterContinuity

/-! # Restricted selector couplings with exact marginals -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set Metric
open scoped ENNReal Topology

namespace MatedCRT.BrownianExitLawIdentification

open LatticeProb.ParentBlock

/-- At sufficiently fine dyadic scales, restricted Brownian endpoint selectors
give exact-marginal probability couplings with prescribed positive error. -/
theorem eventually_planar_brownian_ball_restricted_selector_coupling_with_marginals
    {J : Type*} [Fintype J]
    (center : J → Euc 2) (radius : J → ℝ)
    (c : ℂ) {S : ℝ} (hS : 0 < S)
    (hcenter : ∀ j, Complex.orthonormalBasisOneI.repr.symm (center j) ∈ closedSquare c S)
    (hradius : ∀ j, radius j ≤ S)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ)
    (P : J → Type*) [∀ j, PseudoMetricSpace (P j)] [∀ j, CompactSpace (P j)]
    (x : ∀ j, P j → Euc 2) (hxcont : ∀ j, Continuous (x j))
    (hx : ∀ j z, x j z ∈ ball (center j) (radius j))
    (V : ∀ _j, ℕ → Type*) (p : ∀ j n, V j n → P j)
    (μ : ∀ j n, V j n → ProbabilityMeasure (Euc 2))
    (hLP : ∀ j, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ v : V j n,
      levyProkhorovDist (μ j n v : Measure (Euc 2))
        (stoppedBrownianEndpointProbability (ball (center j) (radius j))
          isOpen_ball ρ hρ (x j (p j n v)) : Measure (Euc 2)) < ε)
    (outer : Set (Euc 2)) (b : ℝ) (hb : 0 < b)
    (hnullOuter : ∀ j z, (stoppedBrownianEndpointProbability (ball (center j) (radius j))
          isOpen_ball ρ hρ (x j z) : Measure (Euc 2)) (frontier outer) = 0)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [∀ n, MeasurableSpace (Option (ParentDyadicIndex n))] :
    ∀ᶠ n : ℕ in atTop, ∃ (m : ℕ) (E : Fin m → Set (Euc 2)) (choice : Fin m → Option (ParentDyadicIndex n)),
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S) ⊆ ⋃ i, E i ∧
      (∀ i, MeasurableSet (E i)) ∧ (∀ i, Bornology.IsBounded (E i)) ∧
      (∀ i, ∀ y ∈ E i, ∀ z ∈ E i, dist y z < (2 * S / (2 : ℝ) ^ n) / 2) ∧
      (∀ j i z, (stoppedBrownianEndpointProbability (ball (center j) (radius j))
          isOpen_ball ρ hρ (x j z) : Measure (Euc 2)) (frontier (E i)) = 0) ∧
      (∀ j z q, (stoppedBrownianEndpointProbability (ball (center j) (radius j))
          isOpen_ball ρ hρ (x j z) : Measure (Euc 2))
        (frontier (cellSelector E choice ⁻¹' {q})) = 0) ∧
      Measurable (cellSelector E choice) ∧
      (∀ y ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S),
        cellSelector E choice y ≠ none) ∧
      (∀ y q, cellSelector E choice y = some q →
        ball y ((2 * S / (2 : ℝ) ^ n) / 2) ⊆
          Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n q) (2 * S / (2 : ℝ) ^ n))) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop, ∀ j (v : V j k) (z : P j),
        dist (p j k v) z ≤ δ →
          ∃ π : Measure (Euc 2 × Euc 2), IsProbabilityMeasure π ∧
            π.fst = (μ j k v : Measure (Euc 2)) ∧
            π.snd = (stoppedBrownianEndpointProbability (ball (center j) (radius j))
          isOpen_ball ρ hρ (x j z) : Measure (Euc 2)) ∧
            π {q | LatticeProb.restrictSelector outer (cellSelector E choice) q.1 ≠
                LatticeProb.restrictSelector outer (cellSelector E choice) q.2 ∨
              (2 * S / (2 : ℝ) ^ n) / 2 ≤ dist q.1 q.2} ≤ ENNReal.ofReal b := by
  apply LatticeProb.ParentBlock.eventually_brownian_ball_dyadic_restricted_selector_coupling_with_marginals
    center radius c hS hcenter hradius ρ hρ P x hx V p μ
    (fun j z => stoppedBrownianEndpointProbability (ball (center j) (radius j))
      isOpen_ball ρ hρ (x j z))
  · intro j z
    rfl
  · intro j
    exact continuous_stoppedBrownianEndpointProbability_comp isOpen_ball isBounded_ball
      ρ hρ (x j) (hxcont j) (hx j)
  · exact hLP
  · exact hb
  · exact hnullOuter

end MatedCRT.BrownianExitLawIdentification
