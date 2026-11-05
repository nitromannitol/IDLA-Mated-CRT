import MatedCRT.Proofs.IDLA.WalkerLawMeasurable
import MatedCRT.Proofs.Sec6.AbelianIDLA.Exchange

/-! # Joint measurability of IDLA cluster events

The initial domain may depend measurably on the environment; the stopping domain is fixed.
-/

namespace MatedCRT

open Set MeasureTheory ProbabilityTheory

/-- A membership event for a stopped aggregate of finitely many walkers is measurable. -/
theorem measurableSet_stoppedIDLACluster_mem (U : Set ℤ) (n : ℕ) (k : ℤ) :
    MeasurableSet {xs : ℕ → ℕ → ℤ | k ∈ stoppedIDLACluster U xs n} := by
  have h := AbelianIDLA.measurableSet_foldl_idlaStep U n (∅, []) (fun s => k ∈ s.1)
  exact h.preimage (measurable_restrictFin n)

/-- Failure of a measurable random set to be contained in a stopped cluster is a joint event. -/
theorem measurableSet_not_subset_stoppedIDLACluster {Ω : Type} [MeasurableSpace Ω]
    (O : Ω → Set ℤ) (hO : ∀ k, MeasurableSet {ω | k ∈ O ω}) (U : Set ℤ) (n : ℕ) :
    MeasurableSet {p : Ω × (ℕ → ℕ → ℤ) | ¬ O p.1 ⊆ stoppedIDLACluster U p.2 n} := by
  have h : {p : Ω × (ℕ → ℕ → ℤ) | ¬ O p.1 ⊆ stoppedIDLACluster U p.2 n} =
      ⋃ k : ℤ, ({ω | k ∈ O ω} ×ˢ {xs | k ∉ stoppedIDLACluster U xs n}) := by
    ext ⟨ω, xs⟩
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, not_subset]
  rw [h]
  exact MeasurableSet.iUnion fun k => (hO k).prod (measurableSet_stoppedIDLACluster_mem U n k).compl

/-- The corresponding event for the unstopped IDLA cluster is measurable. -/
theorem measurableSet_not_subset_idlaCluster {Ω : Type} [MeasurableSpace Ω]
    (O : Ω → Set ℤ) (hO : ∀ k, MeasurableSet {ω | k ∈ O ω}) (n : ℕ) :
    MeasurableSet {p : Ω × (ℕ → ℕ → ℤ) | ¬ O p.1 ⊆ idlaCluster p.2 n} := by
  exact measurableSet_not_subset_stoppedIDLACluster O hO univ n

end MatedCRT
