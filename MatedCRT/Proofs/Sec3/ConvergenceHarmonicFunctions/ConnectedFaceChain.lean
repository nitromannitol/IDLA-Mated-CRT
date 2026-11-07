import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusRadialSeparation

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

end MatedCRT
