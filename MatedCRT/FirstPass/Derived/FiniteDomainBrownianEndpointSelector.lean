import MatedCRT.FirstPass.Derived.FiniteDomainBrownianEndpointCoupling
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellSelector

/-! Coupled selectors for planar stopped Brownian endpoint laws. -/

set_option autoImplicit false

open MeasureTheory Filter BouRabeeGwynne Set
open scoped Topology

namespace MatedCRT.BrownianExitLawIdentification

/-- The finite-cell coupling controls both selector disagreement and endpoint
separation, uniformly over nearby starts in finitely many compact sets. -/
theorem finite_uniform_nearby_stoppedBrownian_endpoint_selector_error_le
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
            r ≤ dist q.1 q.2} ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * ε) := by
  obtain ⟨δ, hδ, hbound⟩ :=
    finite_uniform_nearby_stoppedBrownian_endpoint_coupling_bad_le U K hU hUb hK hKU
      ρ hρ V p μ hLP S hS hd hnull hcover hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hbound] with n hn
  intro j v z hz
  apply hn j v z hz
  intro i
  apply Set.disjoint_left.mpr
  intro q hbad hq
  have hx := (cellLabel_eq_some_iff S hd q.1 i).mpr hq.1
  have hy := (cellLabel_eq_some_iff S hd q.2 i).mpr hq.2
  rcases hbad with hne | hfar
  · exact hne ((cellSelector_of_label S select hx).trans
      (cellSelector_of_label S select hy).symm)
  · exact (not_le_of_gt (hdiam i q.1 hq.1 q.2 hq.2)) hfar

end MatedCRT.BrownianExitLawIdentification
