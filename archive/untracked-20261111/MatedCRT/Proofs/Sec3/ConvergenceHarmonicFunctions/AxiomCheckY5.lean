import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ConnectedFaceChain

/-! # Locally finite face chains along a radial segment -/

namespace MatedCRT

open Set

/-- A locally finite closed face cover yields a walk along a clear radial
segment avoiding a disk. Only faces meeting the segment need satisfy the
cell proximity and diameter estimates. -/
theorem radial_segment_reachable_avoiding_disk_of_locallyFinite
    {ι : Type*} {ε : ℝ} {η : ℝ → ℂ} {z x e : ℂ}
    {radius inner outer margin buffer diameter : ℝ}
    (hclear : ∀ t ∈ Icc inner outer, ∀ y ∈ Metric.ball z radius,
      margin < dist (x + t • e) y)
    (hmargin : buffer + diameter ≤ margin)
    (face : ι → Set ℂ) (hlocallyFinite : LocallyFinite face)
    (hclosed : ∀ i, IsClosed (face i))
    (hcover : ((fun t : ℝ => x + t • e) '' Icc inner outer) ⊆ ⋃ i, face i)
    (G : SimpleGraph ℤ) (vertex : ι → ℤ)
    (hnear : ∀ i, (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ face i).Nonempty →
      ∃ t ∈ Icc inner outer, ∃ q ∈ cell ε η (vertex i),
        dist (x + t • e) q ≤ buffer)
    (hdiam : ∀ i, (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ face i).Nonempty →
      ∀ u ∈ cell ε η (vertex i), ∀ v ∈ cell ε η (vertex i), dist u v ≤ diameter)
    (hlink : ∀ i j, (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩
      face i ∩ face j).Nonempty → vertex i = vertex j ∨ G.Adj (vertex i) (vertex j))
    {first last : ι}
    (hfirst : (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ face first).Nonempty)
    (hlast : (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ face last).Nonempty) :
    ∃ hfirstSafe : vertex first ∉ cellVertices ε η (Metric.ball z radius),
    ∃ hlastSafe : vertex last ∉ cellVertices ε η (Metric.ball z radius),
      (G.induce (cellVertices ε η (Metric.ball z radius))ᶜ).Reachable
        ⟨vertex first, hfirstSafe⟩ ⟨vertex last, hlastSafe⟩ := by
  let K := (fun t : ℝ => x + t • e) '' Icc inner outer
  let indices : Set ι := {i | (K ∩ face i).Nonempty}
  have hcompact : IsCompact K := (outward_radial_segment_compact_preconnected x e inner outer).1
  have hfinite : indices.Finite := by
    convert hlocallyFinite.finite_nonempty_inter_compact hcompact using 1
    ext i
    change (K ∩ face i).Nonempty ↔ (face i ∩ K).Nonempty
    exact ⟨fun ⟨a, ha, hb⟩ => ⟨a, hb, ha⟩,
      fun ⟨a, ha, hb⟩ => ⟨a, hb, ha⟩⟩
  let : Finite indices := hfinite.to_subtype
  have hcover' : K ⊆ ⋃ i : indices, face i := by
    intro point hpK
    obtain ⟨i, hpface⟩ := mem_iUnion.mp (hcover hpK)
    exact mem_iUnion.mpr ⟨⟨i, ⟨point, hpK, hpface⟩⟩, hpface⟩
  exact radial_segment_reachable_avoiding_disk hclear hmargin
    (fun i : indices => face i) (fun i => hclosed i) hcover' G
    (fun i => vertex i) (fun i => hnear i i.property)
    (fun i => hdiam i i.property) (fun i j hij => hlink i j hij)
    (first := ⟨first, hfirst⟩) (last := ⟨last, hlast⟩) hfirst hlast

end MatedCRT

#print axioms MatedCRT.radial_segment_reachable_avoiding_disk_of_locallyFinite
