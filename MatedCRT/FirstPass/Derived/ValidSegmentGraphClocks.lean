import MatedCRT.FirstPass.Derived.EuclideanAreaCurveJointMesh
import MatedCRT.FirstPass.Derived.PaperConstantStepInterpolation
import LatticeProb.Walk.EventuallyCompactSegmentGraphClocks

/-! # Graph clocks for segments of an area-parametrized curve -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology MatedCRTHarmonic.Markov
open scoped ENNReal NNReal
open LatticeProb LatticeProb.ConstantStepInterpolation

namespace MatedCRT

/-- The joint area and mesh estimates control both graph clocks on the same
subsequence, for every contained segment and every walk family whose Euclidean
interpolations converge to a path with regular exit. -/
theorem exists_area_curve_subseq_segment_graph_clocks
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (R : ℝ) :
    ∃ η : Ω → C(ℝ, ℂ), Measurable η ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂S.P,
      ⇑(η ω) = S.η ω ∧
      Tendsto (fun n => FirstPass.Derived.maxCellDiam (ε (φ n)) (⇑(η ω)) R)
        atTop (𝓝 0) ∧
      ∀ (a b : ℝ) (U : Set (EuclideanSpace ℝ (Fin 2))),
        a < b → (η ω) '' Icc a b ⊆ ball (0 : ℂ) R → IsOpen U →
        (Complex.orthonormalBasisOneI.repr ∘ η ω) '' Icc a b = closure U →
      ∀ (x : ℕ → ℕ → ℤ) (m : ℕ → ℝ≥0) (N : ℕ → ℕ)
        (F : ℕ → C(ℝ≥0, EuclideanSpace ℝ (Fin 2)))
        (f : C(ℝ≥0, EuclideanSpace ℝ (Fin 2))) (τ : ℝ≥0),
        (∀ n, 0 < m n) →
        (∀ n, hitTime {j : ℤ | ε (φ n) * j ∈ Icc a b}ᶜ (x n) = N n) →
        (∀ n, ε (φ n) * x n 0 ∈ Icc a b) →
        (∀ n j, x n (j + 1) = x n j ∨
          (adjGraph (S.mult (ε (φ n)) ω)).Adj (x n j) (x n (j + 1))) →
        (∀ n t, F n t = Complex.orthonormalBasisOneI.repr
          (interpolatedWalk (ε (φ n)) (η ω) (m n) (x n) t)) →
        Tendsto F atTop (𝓝 f) →
        (∀ s < τ, f s ∉ frontier U) →
        (∀ t > τ, ∃ s < t, f s ∉ closure U) →
        let c := fun n => knot (m n)
          (hitTime (Graph.innerBoundary (adjGraph (S.mult (ε (φ n)) ω))
            {j : ℤ | ε (φ n) * j ∈ Icc a b}) (x n)).toNat
        let d := fun n => knot (m n) (N n)
        Tendsto c atTop (𝓝 τ) ∧ Tendsto d atTop (𝓝 τ) ∧
          ∀ q : ℝ, 0 < q → ∀ᶠ n in atTop, ∀ s ∈ Icc (c n) (d n),
            ∀ t ∈ Icc (c n) (d n), dist (F n s) (F n t) < q := by
  obtain ⟨η, hη, φ, hφ, hgood⟩ :=
    exists_area_curve_and_subseq_local_mesh_segment_bounds hγ hγ2 hS hε hε0 R
  refine ⟨η, hη, φ, hφ, ?_⟩
  filter_upwards [hgood] with ω hω
  obtain ⟨heq, harea, hdiam, δ, hδ, hbound⟩ := hω
  refine ⟨heq, hdiam, ?_⟩
  intro a b U hab hcontained hU himage x m N F f τ hm hexit hstart hstep hpath hF hbefore hafter
  have hedge : ∀ᶠ n in atTop,
      (∀ v w, (adjGraph (S.mult (ε (φ n)) ω)).Adj v w →
        ε (φ n) * v ∈ Icc a b → ε (φ n) * w ∉ Icc a b →
        dist ((Complex.orthonormalBasisOneI.repr ∘ η ω) (ε (φ n) * v))
          ((Complex.orthonormalBasisOneI.repr ∘ η ω) (ε (φ n) * w)) ≤ δ n) ∧
      (∀ j, j < N n →
        dist ((Complex.orthonormalBasisOneI.repr ∘ η ω) (ε (φ n) * x n j))
          ((Complex.orthonormalBasisOneI.repr ∘ η ω) (ε (φ n) * x n (j + 1))) ≤ δ n) := by
    filter_upwards [hbound] with n hn
    obtain ⟨hcross, hwalk⟩ := hn a b hcontained
    constructor
    · intro v w hv hmem _
      simpa only [Function.comp_apply, vertexPoint] using hcross v w hv hmem
    · intro j hj
      simpa only [Function.comp_apply, vertexPoint] using hwalk (x n) (N n) (hexit n) (hstep n) j hj
  apply tendsto_compact_segment_graph_clocks_of_eventual_bounds
    (Complex.orthonormalBasisOneI.repr ∘ η ω)
    (Measure.map Complex.orthonormalBasisOneI.repr (S.μ ω))
    (Complex.orthonormalBasisOneI.repr.continuous.comp (η ω).continuous)
    (fun a b hab => harea a b hab.le)
    (fun n => adjGraph (S.mult (ε (φ n)) ω)) (fun n j => ε (φ n) * j)
    hU hab himage x m N F f δ δ τ hm hexit hstart hstep hedge ?_ hF hδ hδ hbefore hafter
  intro n t
  rw [hpath n t, repr_interpolatedWalk_eq_constantStep]
  rfl

end MatedCRT
end
