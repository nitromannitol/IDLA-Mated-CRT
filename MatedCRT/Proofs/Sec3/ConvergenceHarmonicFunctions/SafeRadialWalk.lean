import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.SafeCellChain
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! # Radial walks avoiding a disk -/

namespace MatedCRT

open Set Filter Topology MeasureTheory

/-- An induced-graph walk gives an ambient walk supported in the inducing set. -/
theorem SimpleGraph.Reachable.exists_walk_support_subset
    {V : Type*} {G : SimpleGraph V} {U : Set V} {a b : V}
    {ha : a ∈ U} {hb : b ∈ U}
    (h : (G.induce U).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∃ w : G.Walk a b, ∀ v ∈ w.support, v ∈ U := by
  obtain ⟨w⟩ := h
  have hs : ∀ v ∈ (w.map (SimpleGraph.Embedding.induce U).toHom).support, v ∈ U := by
    intro v hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv
    exact u.property
  exact ⟨w.map (SimpleGraph.Embedding.induce U).toHom, hs⟩

/-- On a valid environment, a clear radial segment yields an ambient walk
avoiding the disk whenever all cells meeting the segment have sufficiently
small diameter. The statement holds simultaneously for all parameters. -/
theorem MatedCRTEnv.IsValid.ae_radial_walk_avoiding_disk
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (ε : ℝ), 0 < ε → ∀ (z x e : ℂ)
      (radius inner outer margin diameter : ℝ),
      (∀ t ∈ Icc inner outer, ∀ y ∈ Metric.ball z radius,
        margin < dist (x + t • e) y) →
      (∀ i, (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩
        cell ε (S.η ω) i).Nonempty → Metric.diam (cell ε (S.η ω) i) ≤ diameter) →
      diameter ≤ margin → ∀ j k : ℤ,
      (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ cell ε (S.η ω) j).Nonempty →
      (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ cell ε (S.η ω) k).Nonempty →
      ∃ w : (adjGraph (S.mult ε ω)).Walk j k,
        ∀ v ∈ w.support, v ∉ cellVertices ε (S.η ω) (Metric.ball z radius) := by
  filter_upwards [hS.ae_reachable_in_safe_cell_cover, hS.isAreaParametrized] with ω hconn harea
  intro ε hε z x e radius inner outer margin diameter hclear hdiam hmargin j k hj hk
  let K := (fun t : ℝ => x + t • e) '' Icc inner outer
  let U := (cellVertices ε (S.η ω) (Metric.ball z radius))ᶜ
  have hsafe : ∀ i, (K ∩ cell ε (S.η ω) i).Nonempty → i ∈ U := by
    intro i hi
    obtain ⟨q, ⟨t, ht, rfl⟩, hq⟩ := hi
    have hdi : Metric.diam (cell ε (S.η ω) i) ≤ diameter :=
      hdiam i ⟨x + t • e, ⟨t, ht, rfl⟩, hq⟩
    have hbounded : Bornology.IsBounded (cell ε (S.η ω) i) :=
      (isCompact_Icc.image harea.1).isBounded
    apply cell_not_mem_cellVertices_ball_of_near_clear_segment hclear
      (buffer := 0) (diameter := diameter)
      ⟨t, ht, x + t • e, hq, by simp⟩
      (fun u hu v hv => (Metric.dist_le_diam_of_mem hbounded hu hv).trans hdi)
    simpa using hmargin
  exact SimpleGraph.Reachable.exists_walk_support_subset
    (hconn ε hε K (outward_radial_segment_compact_preconnected x e inner outer).2
      (outward_radial_segment_compact_preconnected x e inner outer).1 U hsafe j k hj hk)

/-- The upper cell-size event on a ball supplies the diameter condition for
every radial segment contained in that ball. -/
theorem MatedCRTEnv.IsValid.ae_radial_walk_of_cell_size
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (ε : ℝ), 0 < ε → ∀ (z x e : ℂ)
      (radius inner outer margin bound ρ : ℝ),
      ((fun t : ℝ => x + t • e) '' Icc inner outer) ⊆ Metric.ball 0 ρ →
      (∀ i, (cell ε (S.η ω) i ∩ Metric.ball 0 ρ).Nonempty →
        Metric.diam (cell ε (S.η ω) i) ≤ bound) →
      (∀ t ∈ Icc inner outer, ∀ y ∈ Metric.ball z radius,
        margin < dist (x + t • e) y) → bound ≤ margin → ∀ j k : ℤ,
      (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ cell ε (S.η ω) j).Nonempty →
      (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ cell ε (S.η ω) k).Nonempty →
      ∃ w : (adjGraph (S.mult ε ω)).Walk j k,
        ∀ v ∈ w.support, v ∉ cellVertices ε (S.η ω) (Metric.ball z radius) := by
  filter_upwards [hS.ae_radial_walk_avoiding_disk] with ω hwalk
  intro ε hε z x e radius inner outer margin bound ρ hK hsize hclear hbound j k hj hk
  apply hwalk ε hε z x e radius inner outer margin bound hclear ?_ hbound j k hj hk
  intro i hi
  obtain ⟨q, hqK, hqcell⟩ := hi
  exact hsize i ⟨q, hqcell, hK hqK⟩

end MatedCRT
