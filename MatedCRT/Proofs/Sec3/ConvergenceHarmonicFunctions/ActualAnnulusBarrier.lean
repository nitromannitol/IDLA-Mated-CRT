import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.SafeCellChain
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusRadialSeparation
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusDisconnection

/-! # Actual annulus barrier: safe radial connection and one-stage disconnection

In a valid mated-CRT environment, an outward radial segment whose cells are clear of an
enlarged disk is joined by a walk of the actual mult graph that avoids the cells meeting
that disk. The identifications of the boundary-length coordinates and the
area-parametrization of the curve come from `MatedCRTEnv.IsValid`, through the almost-sure
lemma `MatedCRTEnv.IsValid.ae_reachable_in_safe_cell_cover` of `SafeCellChain`. No graph
path and no cell-fiber connectivity is supplied by hand.

The one-stage stay estimate is `srwLaw_stay_le_of_annulus_disconnection`. Its
successful-annulus probability is kept as an explicit hypothesis `hdisc`: that is the input
supplied by `GMSAnnulusDisconnectionStmt` (Gwynne-Miller-Sheffield, arXiv:1807.07511v3,
Lemma 3.11, (3.35), p. 31; source `notes/wpn-steps2/steps2-r3.tex` lines 692-703). The
geometric clearance and the inner and outer annulus labels stay visible in the statements.

Credit: the identification relation `MatedCRTHarmonic.MatedCRT.DirectRel` is Leonardo
Bonanno's imported module (`LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel`),
used here through `SafeCellChain`. -/

namespace MatedCRT

open Set Filter Topology MeasureTheory Metric

/-- If two vertices of `T` are joined inside the induced subgraph `G.induce T`, then some walk
of `G` joins them and every vertex of its support lies in `T`. -/
theorem exists_walk_support_mem_of_reachable_induce {V : Type*} {G : SimpleGraph V}
    {T : Set V} {a b : V} {ha : a ∈ T} {hb : b ∈ T}
    (h : (G.induce T).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∃ w : G.Walk a b, ∀ u ∈ w.support, u ∈ T := by
  obtain ⟨w⟩ := h
  have hmem : ∀ u ∈ (w.map (SimpleGraph.Embedding.induce (G := G) T).toHom).support, u ∈ T := by
    intro u hu
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hu
    obtain ⟨v, -, rfl⟩ := hu
    exact v.2
  exact ⟨w.map (SimpleGraph.Embedding.induce (G := G) T).toHom, hmem⟩

/-- Almost surely, for every mesh `ε`, every outward radial segment `x + t • e`, `t ∈ [inner, outer]`,
clear of the ball `ball z radius` by `margin`, and whose cells have diameter at most
`diameter ≤ margin`, any two cells meeting the segment are joined by a walk of
`adjGraph (S.mult ε ω)` avoiding the cells that meet `ball z radius`. -/
theorem MatedCRTEnv.IsValid.ae_outward_segment_walk
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ (z x e : ℂ) (radius inner outer margin diameter : ℝ),
      (∀ t ∈ Icc inner outer, ∀ y ∈ ball z radius, margin < dist (x + t • e) y) →
      (∀ i : ℤ, (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ cell ε (S.η ω) i).Nonempty →
        ∀ u ∈ cell ε (S.η ω) i, ∀ v ∈ cell ε (S.η ω) i, dist u v ≤ diameter) →
      diameter ≤ margin → ∀ j k : ℤ,
      (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ cell ε (S.η ω) j).Nonempty →
      (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩ cell ε (S.η ω) k).Nonempty →
      ∃ w : (adjGraph (S.mult ε ω)).Walk j k,
        ∀ u ∈ w.support, u ∉ cellVertices ε (S.η ω) (ball z radius) := by
  filter_upwards [hS.ae_reachable_in_safe_cell_cover] with ω hreach
  intro ε hε z x e radius inner outer margin diameter hclear hdiam hmargin j k hj hk
  have hsafe : ∀ i : ℤ, (((fun t : ℝ => x + t • e) '' Icc inner outer) ∩
      cell ε (S.η ω) i).Nonempty → i ∈ (cellVertices ε (S.η ω) (ball z radius))ᶜ := by
    rintro i ⟨q, ⟨t, ht, rfl⟩, hq⟩
    exact cell_not_mem_cellVertices_ball_of_near_clear_segment (buffer := 0)
      (diameter := diameter) hclear ⟨t, ht, x + t • e, hq, by simp⟩
      (hdiam i ⟨x + t • e, ⟨t, ht, rfl⟩, hq⟩) (by simpa using hmargin)
  have hK := outward_radial_segment_compact_preconnected x e inner outer
  have hr := hreach ε hε _ hK.2 hK.1 (cellVertices ε (S.η ω) (ball z radius))ᶜ hsafe j k hj hk
  obtain ⟨w, hw⟩ := exists_walk_support_mem_of_reachable_induce hr
  exact ⟨w, fun u hu => hw u hu⟩

/-- One-stage stay estimate in the actual environment. Let `D = ball z r` be the disk, `V` the
boundary-cell representative with `dist V z ≥ r - d`, and `s` the annulus scale with
`5 d < s / 2`. Let `v` be a starting vertex and `p` the successful-annulus probability supplied
for the annulus at `V` with radii `s / 2` and `2 s`. Assume the cells of mesh `ε` meeting
`closedBall V (2 s) \ ball z (r + 3 d)` have diameter at most `d` (the local cell-diameter bound).
Then the walk from `v` stays in the cells of the enlarged disk `ball z (r + 3 d)` before it
hits the outer annulus labels with probability at most `1 - p`. -/
theorem MatedCRTEnv.IsValid.ae_annulus_stay_le_of_disconnection
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, ∀ (ε : ℝ), 0 < ε → ∀ (z V : ℂ) (r s d p : ℝ) (v : ℤ),
      0 ≤ d → 0 ≤ p → r - d ≤ dist V z → 5 * d < s / 2 →
      (∀ i : ℤ, ((closedBall V (2 * s) \ ball z (r + 3 * d)) ∩ cell ε (S.η ω) i).Nonempty →
        ∀ q₁ ∈ cell ε (S.η ω) i, ∀ q₂ ∈ cell ε (S.η ω) i, dist q₁ q₂ ≤ d) →
      ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) v
        {w | ∀ y ∈ cellVertices ε (S.η ω) (sphere V (s / 2)),
          walkDisconnectsBeforeHit (S.mult ε ω)
            (cellVertices ε (S.η ω) (sphere V (2 * s))) y w} →
      srwLaw (S.mult ε ω) v
        {x | ∀ n : ℕ, (n : ℕ∞) < vHitTime (cellVertices ε (S.η ω) (sphere V (2 * s))) x →
          x n ∈ cellVertices ε (S.η ω) (ball z (r + 3 * d))} ≤
        ENNReal.ofReal (1 - p) := by
  filter_upwards [hS.ae_outward_segment_walk, hS.isAreaParametrized] with ω hwalk harea
  intro ε hε z V r s d p v hd hp hnear hscale hcell hdisc
  obtain ⟨e, -, hb₁, hb₂, hdist, hclear⟩ :=
    exists_outward_annulus_segment_avoiding_disk z V (r + 3 * d) (4 * d) d (s / 2) (2 * s)
      (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨t₀, ht₀⟩ := harea.2.2.1 (V + (s / 2) • e)
  obtain ⟨t₁, ht₁⟩ := harea.2.2.1 (V + (2 * s) • e)
  have hmem₀ : V + (s / 2) • e ∈ cell ε (S.η ω) ⌈t₀ / ε⌉ := by
    have h : S.η ω t₀ ∈ cell ε (S.η ω) ⌈t₀ / ε⌉ := Tightness.mem_cell_ceil hε t₀
    rwa [ht₀] at h
  have hmem₁ : V + (2 * s) • e ∈ cell ε (S.η ω) ⌈t₁ / ε⌉ := by
    have h : S.η ω t₁ ∈ cell ε (S.η ω) ⌈t₁ / ε⌉ := Tightness.mem_cell_ceil hε t₁
    rwa [ht₁] at h
  have hj : (((fun t : ℝ => V + t • e) '' Icc (s / 2) (2 * s)) ∩
      cell ε (S.η ω) ⌈t₀ / ε⌉).Nonempty :=
    ⟨V + (s / 2) • e, ⟨s / 2, ⟨le_rfl, by linarith⟩, rfl⟩, hmem₀⟩
  have hk : (((fun t : ℝ => V + t • e) '' Icc (s / 2) (2 * s)) ∩
      cell ε (S.η ω) ⌈t₁ / ε⌉).Nonempty :=
    ⟨V + (2 * s) • e, ⟨2 * s, ⟨by linarith, le_rfl⟩, rfl⟩, hmem₁⟩
  have hy : ⌈t₀ / ε⌉ ∈ cellVertices ε (S.η ω) (sphere V (s / 2)) :=
    ⟨V + (s / 2) • e, hmem₀, hb₁⟩
  have ha : ⌈t₁ / ε⌉ ∈ cellVertices ε (S.η ω) (sphere V (2 * s)) :=
    ⟨V + (2 * s) • e, hmem₁, hb₂⟩
  -- the cells of the segment are controlled by the local bound on the region W
  have hcellK : ∀ i : ℤ,
      (((fun t : ℝ => V + t • e) '' Icc (s / 2) (2 * s)) ∩ cell ε (S.η ω) i).Nonempty →
        ∀ q₁ ∈ cell ε (S.η ω) i, ∀ q₂ ∈ cell ε (S.η ω) i, dist q₁ q₂ ≤ d := by
    intro i hi
    obtain ⟨q, ⟨t, ht, rfl⟩, hq⟩ := hi
    refine hcell i ⟨V + t • e, ⟨?_, ?_⟩, hq⟩
    · exact Metric.mem_closedBall.2 (by rw [hdist t ht]; exact ht.2)
    · intro hball
      have h := hclear t ht _ hball
      rw [dist_self] at h
      linarith
  obtain ⟨w, hw⟩ := hwalk ε hε z V e (r + 3 * d) (s / 2) (2 * s) d d hclear hcellK le_rfl
    ⌈t₀ / ε⌉ ⌈t₁ / ε⌉ hj hk
  exact srwLaw_stay_le_of_annulus_disconnection hy ha w hw hp hdisc

end MatedCRT
