import MatedCRT.FirstPass.Derived.HarnackSingleRing
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.RItinerary

/-!
# Separation of the trace of a walk by a template itinerary

Deterministic discrete side of the Brownian disconnection condition (Gwynne–Miller–Sheffield, the Tutte
embedding of the mated-CRT map, Lemma 3.14, condition 3): if a segment `ξ m₀, …, ξ (m₀ + n)` of a walk is an
`r/60`-itinerary of the moved polar template around `z` (`RouteM.IsTemplateWalk`) and the cellular embedding has
`TemplateSeparation z r`, then this segment disconnects the vertices whose cells meet `∂B_{3r/4}(z)` from those
whose cells meet `∂B_{5r/4}(z)`. If moreover the walk avoids a vertex set `I` up to time `m₀ + n` and every vertex
of `I` has a cell point outside `B_{5r/4}(z)`, the trace of the walk before its first visit to `I` separates every
vertex with a cell point in `B̄_{3r/4}(z)` from `I` (the ring argument of
`MatedCRT.graphSeparates_traceBefore_of_two_spheres`).

The last theorem takes `I` to be the vertices whose cells meet a circle `∂B_R(z)` with `5r/4 ≤ R`: the walk avoids
`I` as soon as each visited cell contains a point `q` with `dist q z + d < R`, where `d` bounds the diameters of the
cells meeting `B_R(z)`.
-/

open Set Metric
open MatedCRTHarmonic MatedCRTHarmonic.HarmonicInfinity

namespace MatedCRT.TemplateWalkSeparation

/-- Enlarging the separating set preserves separation. -/
theorem graphSeparates_mono {V : Type*} {Γ : SimpleGraph V} {U U' A B : Set V}
    (h : GraphSeparates Γ U A B) (hU : U ⊆ U') : GraphSeparates Γ U' A B := by
  intro a ha b hb w
  obtain ⟨y, hy, hyU⟩ := h a ha b hb w
  exact ⟨y, hy, hU hyU⟩

/-- A set of sources is separated from `B` iff each source is. -/
theorem graphSeparates_iff_forall_singleton {V : Type*} {Γ : SimpleGraph V} {U A B : Set V} :
    GraphSeparates Γ U A B ↔ ∀ a ∈ A, GraphSeparates Γ U {a} B := by
  constructor
  · intro h a ha a' ha' b hb w
    rw [mem_singleton_iff] at ha'
    subst ha'
    exact h _ ha b hb w
  · intro h a ha b hb w
    exact h a ha a rfl b hb w

/-- A vertex whose cell contains a point `q` with `dist q z + d < R` does not meet `∂B_R(z)`, when the cell is
bounded and has diameter at most `d` as soon as it meets `B_R(z)`. -/
theorem not_mem_verticesMeeting_sphere {V : Type*} {J : V → Set ℂ} {z q : ℂ} {R d : ℝ} {k : V}
    (hbdd : Bornology.IsBounded (J k)) (hdiam : (J k ∩ ball z R).Nonempty → diam (J k) ≤ d)
    (hd : 0 ≤ d) (hq : q ∈ J k) (hqR : dist q z + d < R) :
    k ∉ verticesMeeting J (sphere z R) := by
  rintro ⟨x, hx, hxR⟩
  rw [mem_sphere] at hxR
  have hqb : q ∈ J k ∩ ball z R := ⟨hq, mem_ball.mpr (by linarith)⟩
  have h1 : dist x q ≤ d := (dist_le_diam_of_mem hbdd hx hq).trans (hdiam ⟨q, hqb⟩)
  have h2 := dist_triangle x q z
  linarith

variable {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} {H : CellularEmbedding G o}

/-- The conclusion of `TemplateSeparation z r` for one template walk, in the separation language of the walk:
the walk disconnects the vertices whose cells meet `∂B_{3r/4}(z)` from those whose cells meet `∂B_{5r/4}(z)`. -/
theorem graphSeparates_spheres_of_isTemplateWalk {z : ℂ} {r ϑ : ℝ} (hTS : H.TemplateSeparation z r)
    {n : ℕ} {v : ℕ → ℤ} {α β : ℕ → ℝ} (hW : RouteM.IsTemplateWalk H z r ϑ n v α β) :
    GraphSeparates G.adj {y | ∃ j ≤ n, v j = y}
      (verticesMeeting H.cell (sphere z (3 * r / 4))) (verticesMeeting H.cell (sphere z (5 * r / 4))) :=
  hTS ϑ n v α β hW.adj hW.α_zero hW.β_last hW.monotone_α hW.monotone_β hW.overlap hW.bounds hW.near

/-- **Separation of the trace by a template itinerary.** If `ξ m₀, …, ξ (m₀ + n)` is a template walk of radius
`r ≥ 0` around `z`, the embedding has `TemplateSeparation z r`, the walk avoids `I` up to time `m₀ + n`, and every
vertex of `I` has a cell point outside `B_{5r/4}(z)`, then the trace of `ξ` before its first visit to `I` separates
`y` from `I` for every `y` with a cell point in `B̄_{3r/4}(z)`. -/
theorem graphSeparates_traceBefore_of_isTemplateWalk {z : ℂ} {r ϑ : ℝ} (hr : 0 ≤ r)
    (hTS : H.TemplateSeparation z r) {ξ : ℕ → ℤ} {m₀ n : ℕ} {α β : ℕ → ℝ}
    (hW : RouteM.IsTemplateWalk H z r ϑ n (fun j => ξ (m₀ + j)) α β) {I : Set ℤ}
    (hn : ∀ j < m₀ + n + 1, ξ j ∉ I) (hI : ∀ k ∈ I, ∃ x ∈ H.cell k, 5 * r / 4 ≤ dist x z)
    {y : ℤ} (hy : ∃ x ∈ H.cell y, dist x z ≤ 3 * r / 4) :
    GraphSeparates G.adj (traceBefore (id : ℤ → ℤ) I ξ) {y} I := by
  refine graphSeparates_traceBefore_of_two_spheres (fun k => (H.isConnected_cell k).isPreconnected)
    H.inter_of_adj (by linarith) (S := verticesMeeting H.cell (sphere z (3 * r / 4)))
    (T := verticesMeeting H.cell (sphere z (5 * r / 4))) ?_ ?_ hy hI hn ?_
  · intro k x hx hxd
    show (H.cell k ∩ sphere z (3 * r / 4)).Nonempty
    exact ⟨x, hx, mem_sphere.mpr hxd⟩
  · intro k x hx hxd
    show (H.cell k ∩ sphere z (5 * r / 4)).Nonempty
    exact ⟨x, hx, mem_sphere.mpr hxd⟩
  · refine graphSeparates_mono (graphSeparates_spheres_of_isTemplateWalk hTS hW) ?_
    rintro v ⟨j, hj, rfl⟩
    exact ⟨m₀ + j, by omega, rfl⟩

/-- **Set version with the outer circle `∂B_R(z)`.** Let `I` be the vertices whose cells meet `∂B_R(z)`, with
`5r/4 ≤ R`, and let `d ≥ 0` bound the diameters of the cells meeting `B_R(z)`. If `ξ m₀, …, ξ (m₀ + n)` is a
template walk of radius `r ≥ 0` around `z`, the embedding has `TemplateSeparation z r`, and the cell of each
`ξ j`, `j ≤ m₀ + n`, contains a point `q` with `dist q z + d < R`, then the trace of `ξ` before its first visit to
`I` separates every vertex with a cell point in `B̄_δ(z)`, `δ ≤ 3r/4`, from `I`. -/
theorem graphSeparates_traceBefore_sphere_of_isTemplateWalk {z : ℂ} {r ϑ R δ d : ℝ} (hr : 0 ≤ r)
    (hδ : δ ≤ 3 * r / 4) (hR : 5 * r / 4 ≤ R) (hd : 0 ≤ d)
    (hdiam : ∀ k, (H.cell k ∩ ball z R).Nonempty → diam (H.cell k) ≤ d)
    (hTS : H.TemplateSeparation z r) {ξ : ℕ → ℤ} {m₀ n : ℕ} {α β : ℕ → ℝ}
    (hW : RouteM.IsTemplateWalk H z r ϑ n (fun j => ξ (m₀ + j)) α β)
    (hq : ∀ j < m₀ + n + 1, ∃ q ∈ H.cell (ξ j), dist q z + d < R) :
    GraphSeparates G.adj (traceBefore (id : ℤ → ℤ) (verticesMeeting H.cell (sphere z R)) ξ)
      {y | ∃ x ∈ H.cell y, dist x z ≤ δ} (verticesMeeting H.cell (sphere z R)) := by
  rw [graphSeparates_iff_forall_singleton]
  rintro y ⟨x, hx, hxd⟩
  refine graphSeparates_traceBefore_of_isTemplateWalk hr hTS hW ?_ ?_ ⟨x, hx, hxd.trans hδ⟩
  · intro j hj
    obtain ⟨q, hqJ, hqR⟩ := hq j hj
    exact not_mem_verticesMeeting_sphere (H.isCompact_cell _).isBounded (hdiam _) hd hqJ hqR
  · rintro k ⟨w, hw, hwR⟩
    refine ⟨w, hw, ?_⟩
    rw [mem_sphere.mp hwR]
    exact hR

end MatedCRT.TemplateWalkSeparation
