import MatedCRT.FirstPass.Derived.EuclideanAreaCurveVersion
import MatedCRT.FirstPass.Derived.EuclideanLocalMeshSegmentBounds

/-! # Joint area curve and local mesh estimates -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology MatedCRTHarmonic.Markov
open scoped ENNReal

namespace MatedCRT

/-- A single measurable area curve and deterministic subsequence satisfy the
area identity and the local segment graph bounds simultaneously. -/
theorem exists_area_curve_and_subseq_local_mesh_segment_bounds
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (R : ℝ) :
    ∃ η : Ω → C(ℝ, ℂ), Measurable η ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ⇑(η ω) = S.η ω ∧
      (∀ a b : ℝ, a ≤ b →
        (Measure.map Complex.orthonormalBasisOneI.repr (S.μ ω))
            ((Complex.orthonormalBasisOneI.repr ∘ η ω) '' Icc a b) =
          ENNReal.ofReal (b - a)) ∧
      Tendsto (fun n => FirstPass.Derived.maxCellDiam (ε (φ n)) (⇑(η ω)) R)
        atTop (𝓝 0) ∧
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        ∀ a b : ℝ, (⇑(η ω)) '' Icc a b ⊆ ball (0 : ℂ) R →
          (∀ j k : ℤ, (adjGraph (S.mult (ε (φ n)) ω)).Adj j k →
            ε (φ n) * j ∈ Icc a b →
            dist (Complex.orthonormalBasisOneI.repr (vertexPoint (ε (φ n)) (⇑(η ω)) j))
              (Complex.orthonormalBasisOneI.repr (vertexPoint (ε (φ n)) (⇑(η ω)) k)) ≤ δ n) ∧
          (∀ (x : ℕ → ℤ) (N : ℕ),
            hitTime {j : ℤ | ε (φ n) * j ∈ Icc a b}ᶜ x = N →
            (∀ j, x (j + 1) = x j ∨
              (adjGraph (S.mult (ε (φ n)) ω)).Adj (x j) (x (j + 1))) →
            ∀ j < N, dist
              (Complex.orthonormalBasisOneI.repr (vertexPoint (ε (φ n)) (⇑(η ω)) (x j)))
              (Complex.orthonormalBasisOneI.repr (vertexPoint (ε (φ n)) (⇑(η ω)) (x (j + 1)))) ≤ δ n) := by
  obtain ⟨η, hη, harea⟩ := FirstPass.Derived.MatedCRTEnv.IsValid.exists_euclidean_area_curveVersion hS
  have hae : ∀ᵐ ω ∂S.P, ⇑(η ω) = S.η ω := harea.mono (fun _ h => h.1)
  obtain ⟨φ, hφ, hmesh⟩ :=
    exists_subseq_local_mesh_and_euclidean_segment_graph_bounds hγ hγ2 hS hae hε hε0 R
  refine ⟨η, hη, φ, hφ, ?_⟩
  filter_upwards [harea, hmesh] with ω harea hmesh
  exact ⟨harea.1, harea.2, hmesh.1, hmesh.2⟩

end MatedCRT
end
