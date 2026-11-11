import MatedCRT.FirstPass.S6d.Localization

/-!
# FIRST PASS: deterministic core of the localization of Lemma 6.8

Notation: `E = fillCells Θ` (the cluster), `C = cell a` (the cell of the starting vertex `a`), `t = r/8` (the
localization radius), `W₀ = V(thickening t E)`, `W₁ = V(thickening t C)`. The cell diameters are bounded by `d < r/100`
on the relevant cells (cell-size estimate, `CellSizeEstimateStmt`, BG20 Lemma 2.4 = paper Lemma 2.8); the edges join only
vertices with intersecting cells (`adjacentCellsMeetAeStep`). Everything here is deterministic.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- The fill of `insert a Θ` is the cell of `a` union the fill of `Θ`. -/
theorem fillCells_insert_eq (ε : ℝ) (η : ℝ → ℂ) (a : ℤ) (Θ : Set ℤ) :
    fillCells ε η (insert a Θ) = cell ε η a ∪ fillCells ε η Θ := by
  unfold fillCells
  rw [Set.biUnion_insert]

/-- The vertices whose cells meet a union are the union of the vertices. -/
theorem cellVertices_union_eq (ε : ℝ) (η : ℝ → ℂ) (D D' : Set ℂ) :
    cellVertices ε η (D ∪ D') = cellVertices ε η D ∪ cellVertices ε η D' := by
  ext k
  simp only [cellVertices, mem_union, mem_ofPred_eq, Set.inter_union_distrib_left, Set.union_nonempty]

/-- The vertex point of `a` lies in the cell of `a`. -/
theorem vertexPoint_mem_cell_of_nonneg {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (a : ℤ) :
    vertexPoint ε η a ∈ cell ε η a :=
  ⟨ε * a, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩

/-- **Deterministic core of the localization** (written out). Hypotheses: the start `a` lies on the frontier of `Θ + B_{r/2}`
(`ha`), the cluster is in `B_{ρ/2}` (`hΘ`), every cell meeting `B_{(1+ρ)/2}` has diameter `≤ d` (`hdiam`), and the edges
join vertices with intersecting cells (`hadj`). Conclusions: (c1) the augmented cluster `Θ ∪ {a}` lies in `B_{(1+ρ)/4}`;
(c2) `a` is in the localized vertex set `W₁`; (c3) `W₁` lies in `V(B_r(E)) \ Θ`; (c4) no edge from `W₁` to `W₀`;
(c5) `W₁ ⊆ V(B_r(η(a)))`; (c6) the ball `B_r(η(a))` lies in `B_{(1+ρ)/2}`. -/
theorem loc_core {ε : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {ρ r d : ℝ} {Θ : Set ℤ} {a : ℤ}
    (hε : 0 ≤ ε) (hρ0 : 0 < ρ) (hr0 : 0 < r) (hr : r ≤ (1 - ρ) / 8)
    (hdr : d < r / 100)
    (hΘ : closure (fillCells ε η Θ) ⊆ ball 0 (ρ / 2))
    (hdiam : ∀ v : ℤ, (cell ε η v ∩ ball 0 ((1 + ρ) / 2)).Nonempty →
      ∀ x ∈ cell ε η v, ∀ y ∈ cell ε η v, dist x y ≤ d)
    (hadj : ∀ v w : ℤ, m v w ≠ 0 → (cell ε η v ∩ cell ε η w).Nonempty)
    (ha : a ∈ cellVertices ε η (frontier (thickening (r / 2) (fillCells ε η Θ)))) :
    closure (fillCells ε η (insert a Θ)) ⊆ ball 0 ((1 + ρ) / 4) ∧
    a ∈ cellVertices ε η (thickening (r / 8) (cell ε η a)) ∧
    (∀ v ∈ cellVertices ε η (thickening (r / 8) (cell ε η a)),
      v ∈ cellVertices ε η (thickening r (fillCells ε η Θ)) \ Θ) ∧
    (∀ v ∈ cellVertices ε η (thickening (r / 8) (cell ε η a)),
      ∀ w ∈ cellVertices ε η (thickening (r / 8) (fillCells ε η Θ)), m v w = 0) ∧
    (∀ v ∈ cellVertices ε η (thickening (r / 8) (cell ε η a)),
      v ∈ cellVertices ε η (ball (vertexPoint ε η a) r)) ∧
    ball (vertexPoint ε η a) r ⊆ ball 0 ((1 + ρ) / 2) := by
  obtain ⟨p, hpC, hpF⟩ := ha
  have hopen : IsOpen (thickening (r / 2) (fillCells ε η Θ)) := isOpen_thickening
  have hpCl : p ∈ closure (thickening (r / 2) (fillCells ε η Θ)) := hpF.1
  have hpNot : p ∉ thickening (r / 2) (fillCells ε η Θ) := fun h =>
    hpF.2 (by rw [hopen.interior_eq]; exact h)
  have hEball : fillCells ε η Θ ⊆ ball 0 (ρ / 2) := fun x hx => hΘ (subset_closure hx)
  -- norm bounds on the thickened cluster
  have hnorm : ∀ x ∈ thickening (r / 2) (fillCells ε η Θ), dist x 0 < ρ / 2 + r / 2 := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := mem_thickening_iff.1 hx
    have h1 : dist e 0 < ρ / 2 := hEball he
    have h2 : dist x 0 ≤ dist x e + dist e 0 := dist_triangle _ _ _
    linarith
  have hcl : closure (thickening (r / 2) (fillCells ε η Θ)) ⊆ closedBall 0 (ρ / 2 + r / 2) :=
    closure_minimal (fun x hx => mem_closedBall.2 (le_of_lt (hnorm x hx))) isClosed_closedBall
  have hpB : dist p 0 ≤ ρ / 2 + r / 2 := mem_closedBall.1 (hcl hpCl)
  have hpin : p ∈ ball 0 ((1 + ρ) / 2) := by
    rw [mem_ball]; linarith
  -- cells of `a`
  have hdC : ∀ y ∈ cell ε η a, dist y p ≤ d := fun y hy => hdiam a ⟨p, hpC, hpin⟩ y hy p hpC
  have hL : ∀ y ∈ cell ε η a, ∀ e ∈ fillCells ε η Θ, r / 2 - d ≤ dist y e := by
    intro y hy e he
    have h1 : r / 2 ≤ dist p e := by
      by_contra h
      push Not at h
      exact hpNot (mem_thickening_iff.2 ⟨e, he, h⟩)
    have h2 : dist p e ≤ dist p y + dist y e := dist_triangle _ _ _
    have h3 := hdC y hy
    rw [dist_comm p y] at h2
    linarith
  have hU : ∃ e ∈ fillCells ε η Θ, dist p e < 3 * r / 4 := by
    obtain ⟨x, hx, hpx⟩ := mem_closure_iff.1 hpCl (r / 4) (by positivity)
    obtain ⟨e, he, hxe⟩ := mem_thickening_iff.1 hx
    refine ⟨e, he, ?_⟩
    have h2 : dist p e ≤ dist p x + dist x e := dist_triangle _ _ _
    linarith
  obtain ⟨e0, he0, hpe0⟩ := hU
  -- the vertex point of `a`
  have hzC : vertexPoint ε η a ∈ cell ε η a := vertexPoint_mem_cell_of_nonneg hε η a
  have hzp : dist (vertexPoint ε η a) p ≤ d := hdC _ hzC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (c1) the augmented cluster
  · rw [fillCells_insert_eq, closure_union]
    refine union_subset ?_ ?_
    · have hC : closure (cell ε η a) ⊆ closedBall p d :=
        closure_minimal (fun y hy => mem_closedBall.2 (hdC y hy)) isClosed_closedBall
      intro x hx
      have h1 : dist x p ≤ d := mem_closedBall.1 (hC hx)
      have h2 : dist x 0 ≤ dist x p + dist p 0 := dist_triangle _ _ _
      rw [mem_ball]
      have h3 : dist p 0 = dist p 0 := rfl
      linarith
    · intro x hx
      rw [mem_ball]
      have h1 : dist x 0 < ρ / 2 := hΘ hx
      linarith
  -- (c2) the start lies in W₁
  · refine ⟨vertexPoint ε η a, hzC, mem_thickening_iff.2 ⟨vertexPoint ε η a, hzC, ?_⟩⟩
    rw [dist_self]
    positivity
  -- (c3) W₁ lies in V(B_r(E)) \ Θ
  · intro v hv
    obtain ⟨q, hqv, hqW⟩ := hv
    obtain ⟨y, hyC, hqy⟩ := mem_thickening_iff.1 hqW
    have hqy' : dist y q < r / 8 := by rw [dist_comm]; exact hqy
    refine ⟨⟨q, hqv, mem_thickening_iff.2 ⟨e0, he0, ?_⟩⟩, ?_⟩
    · have h2 : dist q e0 ≤ dist q y + dist y p + dist p e0 := by
        have := dist_triangle q y p
        have := dist_triangle q p e0
        linarith [dist_triangle q p e0, dist_triangle q y p, hdC y hyC]
      have h3 := hdC y hyC
      have h4 := dist_comm q y
      linarith
    · intro hvΘ
      have hqE : q ∈ fillCells ε η Θ := Set.mem_iUnion₂.2 ⟨v, hvΘ, hqv⟩
      have h1 := hL y hyC q hqE
      linarith
  -- (c4) no edge from W₁ to W₀
  · intro v hv w hw
    by_contra hne
    obtain ⟨p', hp'v, hp'w⟩ := hadj v w hne
    obtain ⟨q, hqv, hqW⟩ := hv
    obtain ⟨y, hyC, hqy⟩ := mem_thickening_iff.1 hqW
    obtain ⟨u, huw, huW⟩ := hw
    obtain ⟨e, heE, hue⟩ := mem_thickening_iff.1 huW
    have hqball : q ∈ ball 0 ((1 + ρ) / 2) := by
      rw [mem_ball]
      have h1 : dist q y < r / 8 := hqy
      have h2 : dist y 0 ≤ dist y p + dist p 0 := dist_triangle _ _ _
      have h3 := hdC y hyC
      have h4 : dist q 0 ≤ dist q y + dist y 0 := dist_triangle _ _ _
      linarith
    have huball : u ∈ ball 0 ((1 + ρ) / 2) := by
      rw [mem_ball]
      have h1 : dist e 0 < ρ / 2 := hEball heE
      have h2 : dist u 0 ≤ dist u e + dist e 0 := dist_triangle _ _ _
      linarith
    have hdv : dist q p' ≤ d := hdiam v ⟨q, hqv, hqball⟩ q hqv p' hp'v
    have hdw : dist p' u ≤ d := hdiam w ⟨u, huw, huball⟩ p' hp'w u huw
    have hye : dist y e ≤ dist y q + dist q p' + dist p' u + dist u e := by
      have h1 : dist y e ≤ dist y q + dist q e := dist_triangle _ _ _
      have h2 : dist q e ≤ dist q p' + dist p' e := dist_triangle _ _ _
      have h3 : dist p' e ≤ dist p' u + dist u e := dist_triangle _ _ _
      linarith
    have h1 := hL y hyC e heE
    have h2 : dist y q = dist q y := dist_comm _ _
    have h3 : dist u e = dist e u := dist_comm _ _
    linarith
  -- (c5) W₁ lies in the ball B_r(η(a))
  · intro v hv
    obtain ⟨q, hqv, hqW⟩ := hv
    obtain ⟨y, hyC, hqy⟩ := mem_thickening_iff.1 hqW
    refine ⟨q, hqv, ?_⟩
    rw [mem_ball]
    have h1 : dist y (vertexPoint ε η a) ≤ d := hdiam a ⟨p, hpC, hpin⟩ y hyC _ hzC
    have h2 : dist q (vertexPoint ε η a) ≤ dist q y + dist y (vertexPoint ε η a) := dist_triangle _ _ _
    have h3 : dist q y < r / 8 := hqy
    linarith
  -- (c6) the ball B_r(η(a)) lies in B_{(1+ρ)/2}
  · intro x hx
    rw [mem_ball] at hx ⊢
    have h2 : dist x 0 ≤ dist x (vertexPoint ε η a) + dist (vertexPoint ε η a) p + dist p 0 := by
      have := dist_triangle x (vertexPoint ε η a) 0
      have := dist_triangle (vertexPoint ε η a) p 0
      have := dist_triangle x (vertexPoint ε η a) p
      linarith [dist_triangle x (vertexPoint ε η a) 0, dist_triangle (vertexPoint ε η a) p 0]
    linarith

end MatedCRT
