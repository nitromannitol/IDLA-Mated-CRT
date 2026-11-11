import Mathlib
import MatedCRT.Defs.Map
import MatedCRT.FirstPass.S3t.VanishingMesh
import MatedCRT.FirstPass.S5c.CellFirstHit

/-!
# Internal cell geometry for the truncated quenched laws (Steps 9a-9d)

Deterministic facts about the cells `H^ε_a = η([ε(a-1), εa])` (`MatedCRT.cell`) used by the Riemann-sum comparison
of Step 10 (`RiemannSum.lean`).

Terminology: frontier `∂D = frontier D` (Armitage-Gardiner, potential theory on the disk `D = ball z r`).
-/

open Set Metric Topology Filter

namespace MatedCRT.TruncatedLaws

variable {ε : ℝ} {η : ℝ → ℂ}

/-- The embedded vertex `η(εk)` lies in its own cell `H^ε_k` (`ε ≥ 0`). -/
lemma vertexPoint_mem_cell_of_nonneg (hε : 0 ≤ ε) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k := by
  refine ⟨ε * k, ⟨?_, le_rfl⟩, rfl⟩
  exact mul_le_mul_of_nonneg_left (by linarith) hε

/-- A cell is bounded when `η` is continuous (`η` is compact on `Icc`). -/
lemma cell_isBounded_of_continuous (hη : Continuous η) (k : ℤ) :
    Bornology.IsBounded (cell ε η k) :=
  (isCompact_Icc.image hη).isBounded

/-- A cell is connected when `η` is continuous and `ε ≥ 0`. -/
lemma cell_isConnected_of_continuous (hε : 0 ≤ ε) (hη : Continuous η) (k : ℤ) :
    IsConnected (cell ε η k) := by
  unfold cell
  have hle : ε * ((k : ℝ) - 1) ≤ ε * k := mul_le_mul_of_nonneg_left (by linarith) hε
  exact (isConnected_Icc hle).image η hη.continuousOn

/-- Step 9a (interior cells lie inside the disk). A connected cell which meets the open set `D` but does not meet
its frontier `∂D` is contained in `D`: the cell is contained in `D ∪ (closure D)ᶜ`, a union of two disjoint open
sets, so connectedness puts it in one of them. -/
theorem cell_subset_of_mem_interiorCellVertices {D : Set ℂ} (hD : IsOpen D) {a : ℤ}
    (ha : a ∈ interiorCellVertices ε η D) (hconn : IsConnected (cell ε η a)) :
    cell ε η a ⊆ D := by
  obtain ⟨hmeet, hfront⟩ := ha
  have hsub : cell ε η a ⊆ D ∪ (closure D)ᶜ := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · refine Or.inr fun hxc => hfront ⟨x, hx, ?_⟩
      rw [frontier, hD.interior_eq]
      exact ⟨hxc, hxD⟩
  have hdisj : Disjoint D (closure D)ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 subset_closure
  exact IsPreconnected.subset_left_of_subset_union hD isClosed_closure.isOpen_compl hdisj hsub hmeet
    hconn.isPreconnected

/-- Step 9b (adjacent embedded vertices are close). If the cells of `a` and `b` meet, the embedded vertices are within
`diam H^ε_a + diam H^ε_b` of each other. -/
theorem dist_vertexPoint_le_diam_add_of_cells_meet (hε : 0 ≤ ε) (hη : Continuous η) {a b : ℤ}
    (hab : (cell ε η a ∩ cell ε η b).Nonempty) :
    dist (vertexPoint ε η a) (vertexPoint ε η b) ≤ diam (cell ε η a) + diam (cell ε η b) := by
  obtain ⟨x, hxa, hxb⟩ := hab
  have h1 : dist (vertexPoint ε η a) x ≤ diam (cell ε η a) :=
    dist_le_diam_of_mem (cell_isBounded_of_continuous hη a) (vertexPoint_mem_cell_of_nonneg hε a) hxa
  have h2 : dist x (vertexPoint ε η b) ≤ diam (cell ε η b) :=
    dist_le_diam_of_mem (cell_isBounded_of_continuous hη b) hxb (vertexPoint_mem_cell_of_nonneg hε b)
  exact (dist_triangle _ x _).trans (add_le_add h1 h2)

/-- Step 9b with a uniform cell-diameter bound `d`: adjacent embedded vertices are within `2d`. -/
theorem dist_vertexPoint_le_two_mul_of_cells_meet (hε : 0 ≤ ε) (hη : Continuous η) {a b : ℤ} {d : ℝ}
    (hab : (cell ε η a ∩ cell ε η b).Nonempty)
    (ha : diam (cell ε η a) ≤ d) (hb : diam (cell ε η b) ≤ d) :
    dist (vertexPoint ε η a) (vertexPoint ε η b) ≤ 2 * d :=
  (dist_vertexPoint_le_diam_add_of_cells_meet hε hη hab).trans (by linarith)

/-- Step 9c (deterministic form). If the cell `H^ε_k` of `k = vertexOf ε η y` contains `y`, has diameter at most `d`,
and `dist y z + d < r`, then `k` is an interior cell vertex of the disk `ball z r`. The eventual statement over
`ε ↓ 0` needs a mesh bound valid for all small `ε` on the same event, which the in-probability Lemma 2.8 does not give
(see the report). -/
theorem vertexOf_mem_interiorCellVertices (hη : Continuous η) {z y : ℂ} {r d : ℝ}
    (hy : y ∈ cell ε η (vertexOf ε η y)) (hdiam : diam (cell ε η (vertexOf ε η y)) ≤ d)
    (hmarg : dist y z + d < r) :
    vertexOf ε η y ∈ interiorCellVertices ε η (ball z r) := by
  set k := vertexOf ε η y with hk
  have hd0 : 0 ≤ d := (Metric.diam_nonneg).trans hdiam
  have hsub : cell ε η k ⊆ ball z r := by
    intro u hu
    have huy : dist u y ≤ d :=
      (dist_le_diam_of_mem (cell_isBounded_of_continuous hη k) hu hy).trans hdiam
    rw [mem_ball]
    calc dist u z ≤ dist u y + dist y z := dist_triangle _ _ _
      _ < r := by linarith
  have hyball : y ∈ ball z r := hsub hy
  have hmem : k ∈ cellVertices ε η (ball z r) := ⟨y, hy, hyball⟩
  have hnf : k ∉ cellVertices ε η (frontier (ball z r)) := by
    rintro ⟨w, hw, hwf⟩
    have hwb : w ∈ ball z r := hsub hw
    rw [isOpen_ball.frontier_eq] at hwf
    exact hwf.2 hwb
  exact ⟨hmem, hnf⟩

/-- Step 9d (first non-interior cell is near the boundary). Let `q` be a walk path whose first `k+1` vertices lie in
the interior cell set `I_ε(D)`, whose vertex `q (k+1)` does not, and whose consecutive cells meet. Then the
embedded point of `q k` lies within `2d` of the frontier `∂D`, under a diameter bound `d` on the two cells. -/
theorem exists_frontier_within_two_mul_of_first_exit {D : Set ℂ} (hD : IsOpen D) (hε : 0 ≤ ε)
    (hη : Continuous η) {q : ℕ → ℤ} {k : ℕ} {d : ℝ}
    (hk : ∀ j ≤ k, q j ∈ interiorCellVertices ε η D) (hnot : q (k + 1) ∉ interiorCellVertices ε η D)
    (hmeet : (cell ε η (q k) ∩ cell ε η (q (k + 1))).Nonempty)
    (hd0 : diam (cell ε η (q k)) ≤ d) (hd1 : diam (cell ε η (q (k + 1))) ≤ d) :
    ∃ w ∈ frontier D, dist (vertexPoint ε η (q k)) w ≤ 2 * d := by
  have hsubk : cell ε η (q k) ⊆ D :=
    cell_subset_of_mem_interiorCellVertices hD (hk k le_rfl) (cell_isConnected_of_continuous hε hη (q k))
  obtain ⟨x, hxk, hxk1⟩ := hmeet
  have hA : q (k + 1) ∈ cellVertices ε η D := ⟨x, hxk1, hsubk hxk⟩
  have hfr : q (k + 1) ∈ cellVertices ε η (frontier D) := by
    by_contra h
    exact hnot ⟨hA, h⟩
  obtain ⟨w, hw1, hwf⟩ := hfr
  refine ⟨w, hwf, ?_⟩
  have h1 : dist (vertexPoint ε η (q k)) x ≤ diam (cell ε η (q k)) :=
    dist_le_diam_of_mem (cell_isBounded_of_continuous hη (q k)) (vertexPoint_mem_cell_of_nonneg hε (q k)) hxk
  have h2 : dist x w ≤ diam (cell ε η (q (k + 1))) :=
    dist_le_diam_of_mem (cell_isBounded_of_continuous hη (q (k + 1))) hxk1 hw1
  calc dist (vertexPoint ε η (q k)) w ≤ dist (vertexPoint ε η (q k)) x + dist x w := dist_triangle _ _ _
    _ ≤ d + d := add_le_add (h1.trans hd0) (h2.trans hd1)
    _ = 2 * d := by ring

/-- Step 9d, geometric form for the disk: a point within `2d` of a point of `∂ ball z r` (with `r ≠ 0`) lies at
distance at least `r - 2d` from the centre `z`. -/
lemma sub_le_dist_center_of_near_frontier {z p w : ℂ} {r d : ℝ} (hr : r ≠ 0)
    (hw : w ∈ frontier (ball z r)) (hpw : dist p w ≤ d) :
    r - d ≤ dist p z := by
  rw [frontier_ball z hr, mem_sphere] at hw
  have h := dist_triangle w p z
  rw [dist_comm w p] at h
  linarith

/-- A proper curve visits each point at bounded-below times (the preimage of a point is compact). This is
`bddBelow_preimage_of_tendsto_cocompact` of `FirstPass/S3t.lean`, restated here because that file imports this one. -/
theorem cellGeom_bddBelow_preimage {η : ℝ → ℂ} (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (x : ℂ) :
    BddBelow {s : ℝ | η s = x} := by
  have h1 : ({x} : Set ℂ)ᶜ ∈ cocompact ℂ := isCompact_singleton.compl_mem_cocompact
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 (hp h1)
  refine hK.bddBelow.mono fun s hs => ?_
  by_contra hsK
  exact (hKs hsK : η s ∉ ({x} : Set ℂ)) (Set.mem_singleton_iff.2 hs)

/-- **Step 9c, deterministic form (truncated-laws Step 9c, Riemann-sum radius relation).** Let `η` be continuous,
surjective and proper, `ε > 0`, and let the mesh bound hold on the cells meeting the inner ball `B_{(1+ρ)/2}(0)`
(`MeshGood`). If `y ∈ B_r(z)`, `B_r(z) ⊆ B_ρ(0)`, `ρ < 1`, and `dist y z + ε^α < r`, then the vertex `a^ε_y` of `y` is an
interior cell vertex of the disk `B_r(z)`, where `α > 0` is the mesh exponent. Terminology: interior cell vertices
`V^ε(D) \ V^ε(∂D)` (Armitage-Gardiner, potential theory on `D = ball z r`). -/
theorem vertexOf_mem_interiorCellVertices_of_mesh {η : ℝ → ℂ} {ε ρ α : ℝ} {z y : ℂ} {r : ℝ}
    (hη : Continuous η) (hsurj : Function.Surjective η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (hball : ball z r ⊆ ball 0 ρ) (hρ1 : ρ < 1) (hy : y ∈ ball z r)
    (hmesh : ∀ k : ℤ, (cell ε η k ∩ ball 0 ((1 + ρ) / 2)).Nonempty → diam (cell ε η k) ≤ ε ^ α)
    (hmarg : dist y z + ε ^ α < r) :
    vertexOf ε η y ∈ interiorCellVertices ε η (ball z r) := by
  have hycell : y ∈ cell ε η (vertexOf ε η y) :=
    MatedCRT.S5c.mem_cell_vertexOf_of_first_hit hε hsurj (cellGeom_bddBelow_preimage hp) y
  have hdiam : diam (cell ε η (vertexOf ε η y)) ≤ ε ^ α := by
    apply hmesh
    refine ⟨y, hycell, ?_⟩
    exact Metric.ball_subset_ball (by linarith : ρ ≤ (1 + ρ) / 2) (hball hy)
  exact vertexOf_mem_interiorCellVertices hη hycell hdiam hmarg

/-- **Step 9c, corrected good-event form**.
For a fixed point `y` of the disk `ball z r`, eventually as `ε ↓ 0`, almost surely on the mesh-good event `MeshGood`
together with the almost-sure properties of `η ω` used by the walk (continuous, surjective and proper; these are the
first three conjuncts of `WalkEnvAe S ω`), the vertex `vertexOf ε (S.η ω) y` is an interior cell vertex of
`ball z r`. The quantifiers are reversed: the mesh estimate holds in probability, so the conclusion is stated on the
good event. The exponent `2/(2+γ)^2 - ζ` is positive by `hζγ`. -/
theorem eventually_ae_vertexOf_mem_interiorCellVertices {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {γ ζ ρ : ℝ} {z y : ℂ} {r : ℝ} (hζγ : ζ < 2 / (2 + γ) ^ 2) (hball : ball z r ⊆ ball 0 ρ) (hρ1 : ρ < 1)
    (hy : y ∈ ball z r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂S.P,
      (MeshGood S γ ζ ρ ε ω ∧
          (Continuous (S.η ω) ∧ Function.Surjective (S.η ω) ∧
            Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ))) →
        vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (ball z r) := by
  have hα : 0 < 2 / (2 + γ) ^ 2 - ζ := sub_pos.2 hζγ
  have hyr : dist y z < r := Metric.mem_ball.1 hy
  have htend : Tendsto (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => ε ^ (2 / (2 + γ) ^ 2 - ζ)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr hα.le)
    have h0 : (0 : ℝ) ^ (2 / (2 + γ) ^ 2 - ζ) = 0 := Real.zero_rpow hα.ne'
    have h1 := hc.tendsto
    rw [h0] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (2 / (2 + γ) ^ 2 - ζ) < r - dist y z :=
    htend.eventually_lt_const (by linarith)
  filter_upwards [hsmall, eventually_mem_nhdsWithin] with ε hε hεpos
  refine Eventually.of_forall fun ω => ?_
  rintro ⟨hMG, hη, hsurj, hp⟩
  exact vertexOf_mem_interiorCellVertices_of_mesh hη hsurj hp (Set.mem_Ioi.1 hεpos) hball hρ1 hy hMG
    (by linarith)

/-- **Step 9c, unconditioned form.** If the almost-sure walk properties hold, then eventually as `ε ↓ 0` the mesh-good
event alone implies that the vertex of `y` is an interior cell vertex of `ball z r` (almost surely). This is the exact
form given the a.s. event `hWae`. -/
theorem eventually_ae_vertexOf_mem_interiorCellVertices_of_ae {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {γ ζ ρ : ℝ} {z y : ℂ} {r : ℝ} (hζγ : ζ < 2 / (2 + γ) ^ 2) (hball : ball z r ⊆ ball 0 ρ) (hρ1 : ρ < 1)
    (hy : y ∈ ball z r)
    (hWae : ∀ᵐ ω ∂S.P, Continuous (S.η ω) ∧ Function.Surjective (S.η ω) ∧
      Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂S.P,
      MeshGood S γ ζ ρ ε ω → vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (ball z r) := by
  filter_upwards [eventually_ae_vertexOf_mem_interiorCellVertices S hζγ hball hρ1 hy] with ε hε
  filter_upwards [hε, hWae] with ω h1 h2 hMG
  exact h1 ⟨hMG, h2⟩

end MatedCRT.TruncatedLaws
