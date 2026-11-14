import MatedCRT.FirstPass.Derived.BoundaryLengthBoundaryPastVersion
import MatedCRT.Proofs.Infra.DiscretePotential
import MatedCRT.Proofs.Infra.MatingOfTrees
import LatticeProb.Graph.Boundary

/-!
# Past-measurable random inner boundary

The fixed-vertex versions assemble into a single random set which agrees almost
surely with the inner boundary in the graph of boundary-length adjacencies.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace MatedCRT

/-- A random interval's inner boundary has a past-measurable set-valued version. -/
theorem exists_past_measurable_innerBoundary_set_version
    {Ω : Type} [MeasurableSpace Ω] (mPast : MeasurableSpace Ω)
    {P : Measure Ω} {B : Ω → C(ℝ, ℝ × ℝ)} {γ : ℝ}
    (hB : AEMeasurable B P)
    (hBM : MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ (P.map B))
    (s ε : ℝ) (hε : 0 < ε) (N : ℤ) (hN : ε * N ≤ s)
    (hPast : ∀ t ≤ s, @Measurable Ω (ℝ × ℝ) mPast _ (fun ω => B ω t))
    (α β : Ω → ℝ) (hα : @Measurable Ω ℝ mPast _ α)
    (hβ : @Measurable Ω ℝ mPast _ β)
    (hβN : ∀ᵐ ω ∂P, β ω < ε * ((N : ℝ) + 1)) :
    ∃ S : Ω → Set ℤ, @Measurable Ω (Set ℤ) mPast _ S ∧
      ∀ᵐ ω ∂P, S ω = LatticeProb.Graph.innerBoundary
        (adjGraph (bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2)))
        {j : ℤ | α ω ≤ ε * j ∧ ε * j ≤ β ω} := by
  have hversions : ∀ j : ℤ, ∃ E : Set Ω, MeasurableSet[mPast] E ∧
      ∀ᵐ ω ∂P, ω ∈ E ↔
        (α ω ≤ ε * j ∧ ε * j ≤ β ω) ∧
        ∃ k : ℤ, ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
          bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2) j k ≠ 0 :=
    fun j => exists_past_measurable_innerBoundary_version mPast hB hBM s ε hε j N hN
      hPast α β hα hβ hβN
  choose E hEm hE using hversions
  refine ⟨fun ω => {j | ω ∈ E j}, ?_, ?_⟩
  · let : MeasurableSpace Ω := mPast
    exact measurable_pi_iff.2 fun j => measurableSet_setOfPred.1 (hEm j)
  · filter_upwards [ae_all_iff.2 hE] with ω hω
    ext j
    change (ω ∈ E j) ↔ j ∈ LatticeProb.Graph.innerBoundary
      (adjGraph (bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2)))
      {j : ℤ | α ω ≤ ε * j ∧ ε * j ≤ β ω}
    rw [hω j]
    change _ ↔ (α ω ≤ ε * j ∧ ε * j ≤ β ω) ∧
      ∃ k : ℤ, ¬ (α ω ≤ ε * k ∧ ε * k ≤ β ω) ∧
        (adjGraph (bmEdgeCount ε (fun t => (B ω t).1) (fun t => (B ω t).2))).Adj j k
    simp only [adjGraph_adj_iff (bmEdgeCount_symm ε _ _)]
    constructor
    · rintro ⟨hj, k, hk, he⟩
      exact ⟨hj, k, hk, fun h => hk (h ▸ hj), he⟩
    · rintro ⟨hj, k, hk, _, he⟩
      exact ⟨hj, k, hk, he⟩

end MatedCRT
