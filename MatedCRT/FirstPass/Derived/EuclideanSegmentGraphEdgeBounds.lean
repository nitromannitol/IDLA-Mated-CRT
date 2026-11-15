import MatedCRT.FirstPass.Derived.SegmentGraphEdgeBounds
import LatticeProb.Topology.ReparamDistanceIsometry

/-! # Euclidean edge bounds for segment-labelled graph walks -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology MatedCRTHarmonic.Markov

namespace MatedCRT

/-- The segment edge bounds hold in Euclidean coordinates along the same
subsequence, simultaneously for every segment. -/
theorem exists_subseq_euclidean_segment_graph_edge_bounds
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P, ∀ a b : ℝ,
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        (∀ j k : ℤ, (adjGraph (S.mult (ε (φ n)) ω)).Adj j k →
          ε (φ n) * j ∈ Icc a b →
          dist (Complex.orthonormalBasisOneI.repr (vertexPoint (ε (φ n)) (⇑(η' ω)) j))
            (Complex.orthonormalBasisOneI.repr (vertexPoint (ε (φ n)) (⇑(η' ω)) k)) ≤ δ n) ∧
        (∀ (x : ℕ → ℤ) (N : ℕ),
          hitTime {j : ℤ | ε (φ n) * j ∈ Icc a b}ᶜ x = N →
          (∀ j, x (j + 1) = x j ∨
            (adjGraph (S.mult (ε (φ n)) ω)).Adj (x j) (x (j + 1))) →
          ∀ j < N, dist
            (Complex.orthonormalBasisOneI.repr (vertexPoint (ε (φ n)) (⇑(η' ω)) (x j)))
            (Complex.orthonormalBasisOneI.repr (vertexPoint (ε (φ n)) (⇑(η' ω)) (x (j + 1)))) ≤ δ n) := by
  obtain ⟨φ, hφ, hφae⟩ := exists_subseq_segment_graph_edge_bounds hγ hγ2 hS hae hε hε0
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae] with ω hω
  intro a b
  obtain ⟨δ, hδ, hbound⟩ := hω a b
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hbound] with n hn
  simpa only [Complex.orthonormalBasisOneI.repr.isometry.dist_eq] using hn

end MatedCRT
end
