import MatedCRT.FirstPass.Derived.VertexSourceFailure
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells

/-! # Selected starting points and vertex score bounds -/

set_option autoImplicit false

open Set Metric MeasureTheory Filter Topology

namespace MatedCRT

/-- A selected-point score failure yields a vertex failure when cells meeting
    the small ball have controlled size and the score has the stated modulus. -/
theorem selectedScoreFailure_subset_vertex {X : Type*} {η : ℝ → ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) {ε ρ δ t a : ℝ} (hε : 0 < ε)
    (score : ℂ × X → ℝ) (q : ℤ → ℂ × X)
    (hq : ∀ k, (q k).1 = vertexPoint ε η k)
    (hcell : ∀ k, (∃ z ∈ closedBall (0 : ℂ) ρ, z ∈ cell ε η k) →
      ∀ z ∈ cell ε η k, dist z (vertexPoint ε η k) ≤ δ)
    (hmod : ∀ z v x, dist z v ≤ δ → score (z, x) ≤ score (v, x) + a) :
    (∃ z ∈ closedBall (0 : ℂ) ρ,
      t + a < score (z, (q (vertexOf ε η z)).2)) →
    ∃ k, (q k).1 ∈ closedBall (0 : ℂ) (ρ + δ) ∧ t < score (q k) := by
  rintro ⟨z, hz, hscore⟩
  let k := vertexOf ε η z
  have hzcell : z ∈ cell ε η k := Tightness.mem_cell_vertexOf hη hp hsurj hε z
  have hdist : dist z (vertexPoint ε η k) ≤ δ := hcell k ⟨z, hz, hzcell⟩ z hzcell
  refine ⟨k, ?_, ?_⟩
  · rw [hq k, mem_closedBall]
    have htri := dist_triangle (vertexPoint ε η k) z (0 : ℂ)
    have hz' := mem_closedBall.mp hz
    rw [dist_comm (vertexPoint ε η k) z] at htri
    linarith
  · have hbound := hmod z (vertexPoint ε η k) (q k).2 hdist
    have hscore' : t + a < score (z, (q k).2) := hscore
    rw [← hq k, Prod.mk.eta] at hbound
    linarith

/-- A bad-cell event and a vertex failure event control selected-point failures. -/
theorem measure_selectedScoreFailure_le_vertex_add_bad
    {Ω X : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ε : Ω → ℝ) (η : Ω → ℝ → ℂ) (q : Ω → ℤ → ℂ × X)
    (ρ δ t a : ℝ) (score : ℂ × X → ℝ) (G : Set Ω)
    (hgood : ∀ ω ∈ G, Continuous (η ω) ∧
      Tendsto (η ω) (cocompact ℝ) (cocompact ℂ) ∧
      Function.Surjective (η ω) ∧ 0 < ε ω ∧
      (∀ k, (q ω k).1 = vertexPoint (ε ω) (η ω) k) ∧
      (∀ k, (∃ z ∈ closedBall (0 : ℂ) ρ, z ∈ cell (ε ω) (η ω) k) →
        ∀ z ∈ cell (ε ω) (η ω) k, dist z (vertexPoint (ε ω) (η ω) k) ≤ δ))
    (hmod : ∀ z v x, dist z v ≤ δ → score (z, x) ≤ score (v, x) + a) :
    P {ω | ∃ z ∈ closedBall (0 : ℂ) ρ,
      t + a < score (z, (q ω (vertexOf (ε ω) (η ω) z)).2)} ≤
    P {ω | ∃ k, (q ω k).1 ∈ closedBall (0 : ℂ) (ρ + δ) ∧ t < score (q ω k)} +
      P Gᶜ := by
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hfail
  by_cases hω : ω ∈ G
  · rcases hgood ω hω with ⟨hη, hp, hs, he, hq, hc⟩
    exact Or.inl (selectedScoreFailure_subset_vertex hη hp hs he score (q ω) hq hc hmod hfail)
  · exact Or.inr hω

end MatedCRT
