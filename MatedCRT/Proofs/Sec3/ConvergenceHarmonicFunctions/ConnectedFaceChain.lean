import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusRadialSeparation
import Mathlib.Topology.Compactness.LocallyFinite

/-! # Face chains along connected sets -/

namespace MatedCRT

open Set Relation

/-- A connected set covered by finitely many closed faces determines a chain
of faces between any two faces it meets. Consecutive faces in the chain
intersect on the connected set itself. -/
theorem IsPreconnected.face_chain_of_finite_closed_cover
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {K : Set X} (hK : IsPreconnected K) (face : ι → Set X)
    (hclosed : ∀ i, IsClosed (face i)) (hcover : K ⊆ ⋃ i, face i)
    {first last : ι} (hfirst : (K ∩ face first).Nonempty)
    (hlast : (K ∩ face last).Nonempty) :
    ReflTransGen (fun i j => (K ∩ face i ∩ face j).Nonempty) first last := by
  classical
  let reachable : Set ι := {i | ReflTransGen (fun i j =>
    (K ∩ face i ∩ face j).Nonempty) first i}
  let left : Set X := ⋃ i ∈ reachable, face i
  let right : Set X := ⋃ i ∈ reachableᶜ, face i
  by_contra hnot
  have hfirstmem : first ∈ reachable := ReflTransGen.refl
  have hlastmem : last ∈ reachableᶜ := hnot
  have hleftclosed : IsClosed left :=
    (Set.toFinite reachable).isClosed_biUnion (fun i _ => hclosed i)
  have hrightclosed : IsClosed right :=
    (Set.toFinite reachableᶜ).isClosed_biUnion (fun i _ => hclosed i)
  have hsplit : K ⊆ left ∪ right := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    by_cases h : i ∈ reachable
    · exact Or.inl (mem_iUnion₂.mpr ⟨i, h, hi⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, h, hi⟩)
  have hleft : (K ∩ left).Nonempty := by
    obtain ⟨x, hxK, hxface⟩ := hfirst
    exact ⟨x, hxK, mem_iUnion₂.mpr ⟨first, hfirstmem, hxface⟩⟩
  have hright : (K ∩ right).Nonempty := by
    obtain ⟨x, hxK, hxface⟩ := hlast
    exact ⟨x, hxK, mem_iUnion₂.mpr ⟨last, hlastmem, hxface⟩⟩
  obtain ⟨x, hxK, hxleft, hxright⟩ :=
    isPreconnected_closed_iff.mp hK left right hleftclosed hrightclosed hsplit hleft hright
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxleft
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxright
  exact hj (hi.tail ⟨x, ⟨hxK, hxi⟩, hxj⟩)

/-- If intersecting faces can be joined in a graph, the face chain produces
a graph walk between the labels of the endpoint faces. This also applies to
an induced graph, allowing the walk to avoid a specified vertex set. -/
theorem IsPreconnected.reachable_of_finite_closed_face_cover
    {X ι V : Type*} [TopologicalSpace X] [Finite ι]
    {K : Set X} (hK : IsPreconnected K) (face : ι → Set X)
    (hclosed : ∀ i, IsClosed (face i)) (hcover : K ⊆ ⋃ i, face i)
    (G : SimpleGraph V) (vertex : ι → V)
    (hlink : ∀ i j, (K ∩ face i ∩ face j).Nonempty →
      G.Reachable (vertex i) (vertex j))
    {first last : ι} (hfirst : (K ∩ face first).Nonempty)
    (hlast : (K ∩ face last).Nonempty) :
    G.Reachable (vertex first) (vertex last) := by
  have hchain := IsPreconnected.face_chain_of_finite_closed_cover hK face hclosed hcover
    hfirst hlast
  induction hchain with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail i j hpath hedge ih =>
    exact (ih ⟨hedge.choose, hedge.choose_spec.1⟩).trans (hlink i j hedge)

/-- A finite closed face cover of a clear radial segment gives an induced
graph walk avoiding all cells that meet the disk, provided consecutive face
labels agree or are adjacent and their cells satisfy the stated bounds. -/
theorem radial_segment_reachable_avoiding_disk
    {ι : Type*} [Finite ι] {ε : ℝ} {η : ℝ → ℂ} {z x e : ℂ}
    {radius inner outer margin buffer diameter : ℝ}
    (hclear : ∀ t ∈ Icc inner outer, ∀ y ∈ Metric.ball z radius,
      margin < dist (x + t • e) y)
    (hmargin : buffer + diameter ≤ margin)
    (face : ι → Set ℂ) (hclosed : ∀ i, IsClosed (face i))
    (hcover : ((fun t : ℝ => x + t • e) '' Icc inner outer) ⊆ ⋃ i, face i)
    (G : SimpleGraph ℤ) (vertex : ι → ℤ)
    (hnear : ∀ i, ∃ t ∈ Icc inner outer, ∃ q ∈ cell ε η (vertex i),
      dist (x + t • e) q ≤ buffer)
    (hdiam : ∀ i, ∀ u ∈ cell ε η (vertex i), ∀ v ∈ cell ε η (vertex i),
      dist u v ≤ diameter)
    (hlink : ∀ i j, (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩
      face i ∩ face j).Nonempty → vertex i = vertex j ∨ G.Adj (vertex i) (vertex j))
    {first last : ι}
    (hfirst : (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ face first).Nonempty)
    (hlast : (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ face last).Nonempty) :
    ∃ hfirstSafe : vertex first ∉ cellVertices ε η (Metric.ball z radius),
    ∃ hlastSafe : vertex last ∉ cellVertices ε η (Metric.ball z radius),
      (G.induce (cellVertices ε η (Metric.ball z radius))ᶜ).Reachable
        ⟨vertex first, hfirstSafe⟩ ⟨vertex last, hlastSafe⟩ := by
  have hsafe : ∀ i, vertex i ∉ cellVertices ε η (Metric.ball z radius) := by
    intro i
    exact cell_not_mem_cellVertices_ball_of_near_clear_segment hclear (hnear i)
      (hdiam i) hmargin
  refine ⟨hsafe first, hsafe last, ?_⟩
  apply IsPreconnected.reachable_of_finite_closed_face_cover
    (outward_radial_segment_compact_preconnected x e inner outer).2 face hclosed hcover
    (G.induce (cellVertices ε η (Metric.ball z radius))ᶜ)
    (fun i => ⟨vertex i, hsafe i⟩) ?_ hfirst hlast
  intro i j hij
  rcases hlink i j hij with heq | hadj
  · have heq' : (⟨vertex i, hsafe i⟩ : {a : ℤ // a ∈ (cellVertices ε η (Metric.ball z radius))ᶜ}) =
        ⟨vertex j, hsafe j⟩ := Subtype.ext heq
    rw [heq']
  · exact SimpleGraph.Adj.reachable hadj

/-- A locally finite closed face cover of a compact connected set yields a
graph walk, provided faces meeting on the set have reachable labels. -/
theorem IsPreconnected.reachable_of_locallyFinite_closed_face_cover
    {X ι V : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsPreconnected K) (hcompact : IsCompact K)
    (face : ι → Set X) (hlocallyFinite : LocallyFinite face)
    (hclosed : ∀ i, IsClosed (face i)) (hcover : K ⊆ ⋃ i, face i)
    (G : SimpleGraph V) (vertex : ι → V)
    (hlink : ∀ i j, (K ∩ face i ∩ face j).Nonempty →
      G.Reachable (vertex i) (vertex j))
    {first last : ι} (hfirst : (K ∩ face first).Nonempty)
    (hlast : (K ∩ face last).Nonempty) :
    G.Reachable (vertex first) (vertex last) := by
  let indices : Set ι := {i | (face i ∩ K).Nonempty}
  have hfinite : indices.Finite := hlocallyFinite.finite_nonempty_inter_compact hcompact
  let : Finite indices := hfinite.to_subtype
  have hfirst' : first ∈ indices := by
    obtain ⟨point, hpK, hpface⟩ := hfirst
    exact ⟨point, hpface, hpK⟩
  have hlast' : last ∈ indices := by
    obtain ⟨point, hpK, hpface⟩ := hlast
    exact ⟨point, hpface, hpK⟩
  have hcover' : K ⊆ ⋃ i : indices, face i := by
    intro point hpK
    obtain ⟨i, hpface⟩ := mem_iUnion.mp (hcover hpK)
    exact mem_iUnion.mpr ⟨⟨i, ⟨point, hpface, hpK⟩⟩, hpface⟩
  exact IsPreconnected.reachable_of_finite_closed_face_cover hK
    (fun i : indices => face i) (fun i => hclosed i) hcover' G
    (fun i => vertex i) (fun i j hij => hlink i j hij)
    (first := ⟨first, hfirst'⟩) (last := ⟨last, hlast'⟩) hfirst hlast

end MatedCRT
