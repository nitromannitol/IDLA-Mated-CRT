import MatedCRT.FirstPass.Derived.LocalMeshSegmentGraphBounds
import LatticeProb.Topology.ReparamDistanceIsometry

/-! # Euclidean joint local mesh and segment graph bounds -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology MatedCRTHarmonic.Markov
open scoped ENNReal

namespace MatedCRT

/-- In Euclidean coordinates, the local cell diameters and segment graph
edges have the same joint subsequence and pathwise edge majorant. -/
theorem exists_subseq_local_mesh_and_euclidean_segment_graph_bounds
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {η' : Ω → C(ℝ, ℂ)} (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (R : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      Tendsto (fun n => FirstPass.Derived.maxCellDiam (ε (φ n)) (⇑(η' ω)) R)
        atTop (𝓝 0) ∧
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        ∀ a b : ℝ, (⇑(η' ω)) '' Icc a b ⊆ ball (0 : ℂ) R →
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
  obtain ⟨φ, hφ, hφae⟩ :=
    exists_subseq_local_mesh_and_segment_graph_bounds hγ hγ2 hS hae hε hε0 R
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae] with ω hω
  obtain ⟨hdiam, δ, hδ, hbound⟩ := hω
  refine ⟨hdiam, δ, hδ, ?_⟩
  filter_upwards [hbound] with n hn
  simpa only [Complex.orthonormalBasisOneI.repr.isometry.dist_eq] using hn

end MatedCRT
end
