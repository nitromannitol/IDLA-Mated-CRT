import MatedCRT.Defs.Map
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Deterministic core of the stopped interior geometry (`StoppedInteriorGeometryStep`)

Notation of the paper: `K = closure L`, `K^d = cthickening d K = {x | d(x, K) ≤ d}`, `B_δ(z)` the open ball,
`L^c` the complement; all distances are the real `infDist`.

Contents (proved; no hypotheses beyond those displayed):
* `exists_regularOpen_core`: the compact core of a bounded regular open set.
* `smallCells_geometry`: the small-cell consequence for the cell union `fillCells ε η (cellVertices ε η L)`.
* `GeoBad`, `geoBad_of_bad_vertex`: failure of the conclusion forces the obstruction `GeoBad`.
* `eventually_not_geoBad`: on a regular open core the obstructions at meshes `1/(n+1)` eventually vanish.
* `geoBad_mono`: monotonicity of the obstruction in the thickening radius.
* `tendsToOneOn_of_bad_null`: the outer-probability passage (`TendsToOneOn`) from a decreasing family of
  null-measurable obstructions with null intersection, a containment, and the cell-size probability input.

`smallCells_geometry` uses only the cell-diameter hypothesis `hdist`; continuity, properness and surjectivity of `η` enter only through the cell-size input that produces `hdist`.
-/

namespace MatedCRT
namespace StoppedInteriorGeometry

open Metric Set Filter Topology MeasureTheory

/-- The obstruction for `K = closure L` at thickening `d` and fixed `δ`: some `z ∈ K^d` has
`B_δ(z) ⊆ K^d` and `d(z, L^c) < 3δ/4`. -/
def GeoBad (L : Set ℂ) (δ d : ℝ) : Prop :=
  ∃ z : ℂ, z ∈ cthickening d (closure L) ∧ ball z δ ⊆ cthickening d (closure L) ∧ infDist z Lᶜ < 3 * δ / 4

/-- If `x ∈ K^d` with `d ≥ 0`, then `d(x, E) ≤ d`. -/
theorem infDist_le_of_mem_cthickening {E : Set ℂ} {x : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (h : x ∈ cthickening d E) : infDist x E ≤ d := by
  rw [Metric.mem_cthickening_iff] at h
  exact ENNReal.toReal_le_of_le_ofReal hd h

/-- **Regular-open compact core**. Let `L ⊆ ℂ` be a nonempty bounded regular open set and
`K = closure L`. For `δ > 0` there is `d₀ > 0` such that `z ∈ K^d`, `B_δ(z) ⊆ K^d` and `0 < d < d₀` imply
`d(z, L^c) ≥ 3δ/4`. Proof: a failing sequence has a convergent subsequence; the δ-ball of the limit lies in `K`,
hence in `int K = L`, which forces `d(·, L^c) ≥ δ` at the limit, contradicting the bounds along the sequence. -/
theorem exists_regularOpen_core {L : Set ℂ} (hreg : interior (closure L) = L)
    (hbdd : Bornology.IsBounded L) (hne : L.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ∃ d₀ > 0, ∀ z : ℂ, ∀ d : ℝ, 0 < d → d < d₀ → z ∈ cthickening d (closure L) →
      ball z δ ⊆ cthickening d (closure L) → 3 * δ / 4 ≤ infDist z Lᶜ := by
  by_contra hcon
  push Not at hcon
  have hKne : (closure L).Nonempty := hne.mono subset_closure
  have hLcne : Lᶜ.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hL : L = univ := by
      ext x
      simp only [mem_univ, iff_true]
      by_contra hx
      have hxc : x ∈ Lᶜ := hx
      rw [h] at hxc
      simp at hxc
    exact NormedSpace.unbounded_univ ℝ ℂ (hL ▸ hbdd)
  choose z d hd0 hdlt hz hball hlt using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have hd1 : ∀ n, d n ≤ 1 := fun n => (hdlt n).le.trans <| by
    rw [div_le_iff₀ (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcpt : IsCompact (cthickening 1 (closure L)) := hbdd.isCompact_closure.cthickening
  have hzmem : ∀ n, z n ∈ cthickening 1 (closure L) := fun n => cthickening_mono (hd1 n) _ (hz n)
  obtain ⟨w, -, φ, hφ, hlim⟩ := hcpt.tendsto_subseq hzmem
  have hdlim : Tendsto (fun n => d (φ n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hd0 (φ n)).le) (fun n => (hdlt (φ n)).le)
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop)
  -- the δ-ball of the limit lies in K
  have hball_sub : ball w δ ⊆ closure L := by
    intro y hy
    have hev : ∀ᶠ n in atTop, dist y (z (φ n)) < δ := by
      have h := Metric.tendsto_nhds.1 hlim (δ - dist y w) (by linarith [mem_ball.1 hy])
      filter_upwards [h] with n hn
      have h2 := dist_triangle y w (z (φ n))
      rw [dist_comm w (z (φ n))] at h2
      have h3 : dist (z (φ n)) w < δ - dist y w := hn
      linarith
    have hinf : ∀ᶠ n in atTop, infDist y (closure L) ≤ d (φ n) := by
      filter_upwards [hev] with n hn
      exact infDist_le_of_mem_cthickening (hd0 (φ n)).le (hball (φ n) (mem_ball.2 hn))
    have hy0 : infDist y (closure L) = 0 :=
      le_antisymm (ge_of_tendsto hdlim hinf) infDist_nonneg
    have hyy : y ∈ closure (closure L) := (mem_closure_iff_infDist_zero hKne).2 hy0
    rwa [closure_closure] at hyy
  have hball_L : ball w δ ⊆ L := by
    have h := interior_maximal hball_sub isOpen_ball
    rwa [hreg] at h
  have hδL : δ ≤ infDist w Lᶜ := by
    by_contra h
    push Not at h
    obtain ⟨q, hq, hwq⟩ := (infDist_lt_iff hLcne).1 h
    exact hq (hball_L (mem_ball.2 (by rw [dist_comm]; exact hwq)))
  have hcontL : Tendsto (fun n => infDist (z (φ n)) Lᶜ) atTop (𝓝 (infDist w Lᶜ)) :=
    ((continuous_infDist_pt (s := Lᶜ)).tendsto w).comp hlim
  have hle : infDist w Lᶜ ≤ 3 * δ / 4 :=
    le_of_tendsto hcontL (Eventually.of_forall fun n => (hlt (φ n)).le)
  linarith

/-- The vertex point `η(εa)` lies in its own cell `η([ε(a-1), εa])`. -/
theorem vertexPoint_mem_cell {ε : ℝ} (hε : 0 < ε) (η : ℝ → ℂ) (a : ℤ) :
    vertexPoint ε η a ∈ cell ε η a :=
  ⟨ε * (a : ℝ), ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_refl _⟩, rfl⟩

/-- Cell-by-cell pointwise bound from a diameter bound on a compact cell (`η` continuous). -/
theorem dist_le_of_diam_le {η : ℝ → ℂ} (hη : Continuous η) {ε d : ℝ} {k : ℤ}
    (hk : diam (cell ε η k) ≤ d) {x y : ℂ} (hx : x ∈ cell ε η k) (hy : y ∈ cell ε η k) :
    dist x y ≤ d := by
  have hb : Bornology.IsBounded (cell ε η k) := (isCompact_Icc.image hη).isBounded
  exact (dist_le_diam_of_mem hb hx hy).trans hk

/-- A ball around `z ∈ U` of radius `δ` whose centre lies at distance `> δ` from `∂U` lies in `U`
(a segment from `z` to `U^c` would first cross `∂U`). -/
theorem ball_subset_of_infDist_frontier {U : Set ℂ} {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hz : z ∈ U)
    (hfr : δ < infDist z (frontier U)) : ball z δ ⊆ U := by
  have hz_int : z ∈ interior U := by
    by_contra h
    have hzf : z ∈ frontier U := ⟨subset_closure hz, h⟩
    have h0 := infDist_zero_of_mem hzf
    linarith
  have hsub : ball z δ ⊆ interior U ∪ interior Uᶜ := by
    intro y hy
    by_contra h
    simp only [mem_union, not_or] at h
    have hyc : y ∈ closure U := by
      by_contra hc
      exact h.2 (by rw [interior_compl]; exact hc)
    have hyf : y ∈ frontier U := ⟨hyc, h.1⟩
    have h1 : infDist z (frontier U) ≤ dist z y := infDist_le_dist_of_mem hyf
    have h2 : dist z y < δ := by rw [dist_comm]; exact mem_ball.1 hy
    linarith
  have hdisj : Disjoint (interior U) (interior Uᶜ) := by
    rw [Set.disjoint_left]
    intro y h1 h2
    exact (interior_subset h2 : y ∈ Uᶜ) (interior_subset h1)
  have hconn : IsPreconnected (ball z δ) := (convex_ball z δ).isPreconnected
  have hsub' := hconn.subset_left_of_subset_union isOpen_interior isOpen_interior hdisj hsub
    ⟨z, mem_ball_self hδ, hz_int⟩
  exact hsub'.trans interior_subset

/-- Every point of a cell meeting `L` lies within `d` of that cell's meeting point, so `U = fillCells` lies in `K^d`
(the inclusion `U ⊆ K^d`). -/
theorem fillCells_subset_cthickening {η : ℝ → ℂ} {ε d : ℝ} {L : Set ℂ}
    (hdist : ∀ k ∈ cellVertices ε η L, ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d) :
    fillCells ε η (cellVertices ε η L) ⊆ cthickening d (closure L) := by
  intro y hy
  unfold fillCells at hy
  obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.1 hy
  obtain ⟨x, hxc, hxL⟩ := id hk
  exact mem_cthickening_of_dist_le y x d (closure L) (subset_closure hxL) (hdist k hk y hyk x hxc)

/-- **Small-cell geometry** (deterministic). Let `L` be a bounded regular open set and `ε`,
`δ`, `r` positive reals. There is `d₀ > 0` such that for `0 < d < min(d₀, δ/4, r)`, provided every cell meeting `L`
has pointwise diameter at most `d`, each selected vertex `a` (cell meets `L`) whose point `z_a = η(εa)` satisfies
`d(z_a, ∂U) > δ`, where `U = ⋃_{k ∈ V^ε(L)} H_k`, has `d(x, L^c) ≥ δ/2` and `|x − z_a| < r` for every `x ∈ H_a`. -/
theorem smallCells_geometry {η : ℝ → ℂ} {ε : ℝ} {L : Set ℂ} (hε : 0 < ε) (hreg : interior (closure L) = L)
    (hbdd : Bornology.IsBounded L) {δ r : ℝ} (hδ : 0 < δ) :
    ∃ d₀ > 0, ∀ d : ℝ, 0 < d → d < d₀ → d < δ / 4 → d < r →
      (∀ k ∈ cellVertices ε η L, ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d) →
      ∀ a ∈ cellVertices ε η L,
        δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η (cellVertices ε η L))) →
        ∀ x ∈ cell ε η a, δ / 2 ≤ infDist x Lᶜ ∧ dist x (vertexPoint ε η a) < r := by
  rcases L.eq_empty_or_nonempty with rfl | hne
  · refine ⟨1, one_pos, fun d _ _ _ _ _ a ha => ?_⟩
    simp [cellVertices] at ha
  · obtain ⟨d₀, hd₀, hcore⟩ := exists_regularOpen_core hreg hbdd hne hδ
    refine ⟨d₀, hd₀, fun d hd hdd₀ hdδ hdr hdist a ha hfr x hx => ?_⟩
    have hzU : vertexPoint ε η a ∈ fillCells ε η (cellVertices ε η L) := by
      unfold fillCells
      exact mem_iUnion₂.2 ⟨a, ha, vertexPoint_mem_cell hε η a⟩
    have hdistz : dist x (vertexPoint ε η a) ≤ d :=
      hdist a ha x hx _ (vertexPoint_mem_cell hε η a)
    have hUK := fillCells_subset_cthickening hdist
    have hballU := ball_subset_of_infDist_frontier hδ hzU hfr
    have hcore' := hcore (vertexPoint ε η a) d hd hdd₀ (hUK hzU) (hballU.trans hUK)
    have htri : infDist (vertexPoint ε η a) Lᶜ ≤ infDist x Lᶜ + dist (vertexPoint ε η a) x :=
      infDist_le_infDist_add_dist
    rw [dist_comm] at htri
    exact ⟨by linarith, lt_of_le_of_lt hdistz hdr⟩

/-- **Failure forces the obstruction** (the deterministic containment). If the conclusion of
`smallCells_geometry` fails at a selected vertex `a` and a point `x ∈ H_a`, then `GeoBad L δ d` holds, provided
`d < δ/4`, `d < r` and the cell-diameter bound at `d`. -/
theorem geoBad_of_bad_vertex {η : ℝ → ℂ} {ε : ℝ} {L : Set ℂ} (hε : 0 < ε) {δ r d : ℝ} (hδ : 0 < δ)
    (hdδ : d < δ / 4) (hdr : d < r)
    (hdist : ∀ k ∈ cellVertices ε η L, ∀ x ∈ cell ε η k, ∀ y ∈ cell ε η k, dist x y ≤ d)
    {a : ℤ} (ha : a ∈ cellVertices ε η L)
    (hfr : δ < infDist (vertexPoint ε η a) (frontier (fillCells ε η (cellVertices ε η L))))
    {x : ℂ} (hx : x ∈ cell ε η a)
    (hfail : ¬ (δ / 2 ≤ infDist x Lᶜ ∧ dist x (vertexPoint ε η a) < r)) :
    GeoBad L δ d := by
  have hzU : vertexPoint ε η a ∈ fillCells ε η (cellVertices ε η L) := by
    unfold fillCells
    exact mem_iUnion₂.2 ⟨a, ha, vertexPoint_mem_cell hε η a⟩
  have hdistz : dist x (vertexPoint ε η a) ≤ d :=
    hdist a ha x hx _ (vertexPoint_mem_cell hε η a)
  have hUK := fillCells_subset_cthickening hdist
  unfold GeoBad
  refine ⟨vertexPoint ε η a, hUK hzU, (ball_subset_of_infDist_frontier hδ hzU hfr).trans hUK, ?_⟩
  have hlt : infDist x Lᶜ < δ / 2 := by
    by_contra h
    exact hfail ⟨not_lt.1 h, lt_of_le_of_lt hdistz hdr⟩
  have htri : infDist (vertexPoint ε η a) Lᶜ ≤ infDist x Lᶜ + dist (vertexPoint ε η a) x :=
    infDist_le_infDist_add_dist
  rw [dist_comm] at htri
  linarith

/-- The obstruction is monotone in the thickening radius. -/
theorem geoBad_mono {L : Set ℂ} {δ d d' : ℝ} (hdd : d ≤ d') (h : GeoBad L δ d) : GeoBad L δ d' := by
  unfold GeoBad at h ⊢
  obtain ⟨z, hz, hball, hlt⟩ := h
  exact ⟨z, cthickening_mono hdd _ hz, hball.trans (cthickening_mono hdd _), hlt⟩

/-- **Null intersection on a regular open core**. For a bounded regular open `L` and
`δ > 0`, the obstructions at meshes `1/(n+1)` eventually fail: this is the compact-core lemma read at `d = 1/(n+1)`. -/
theorem eventually_not_geoBad {L : Set ℂ} (hreg : interior (closure L) = L)
    (hbdd : Bornology.IsBounded L) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ¬ GeoBad L δ (1 / ((n : ℝ) + 1)) := by
  rcases L.eq_empty_or_nonempty with rfl | hne
  · refine Eventually.of_forall fun n hG => ?_
    unfold GeoBad at hG
    obtain ⟨z, hz, -⟩ := hG
    simp [cthickening_empty] at hz
  · obtain ⟨d₀, hd₀, hcore⟩ := exists_regularOpen_core hreg hbdd hne hδ
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < d₀ :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hd₀)
    filter_upwards [hev] with n hn hG
    unfold GeoBad at hG
    obtain ⟨z, hz, hball, hlt⟩ := hG
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact absurd (hcore z _ hpos hn hz hball) (not_le.2 hlt)

/-- **Outer-probability passage** (`TendsToOneOn P F E`, i.e. `P(F ∩ (E ε)ᶜ) → 0` as `ε ↓ 0`).
Inputs: `G` is a full-measure event on which the decreasing obstructions `B n` have empty intersection; `B n` are
null-measurable (the measurability input, Preston Theorem 7.1 with Theorem 6.1); `C ε n` is the cell-size failure event
whose probability tends to `0` as `ε ↓ 0` for each `n`; and off `C ε n ∪ B n` the event `F ∩ G` is contained in `E ε`
for all large `n`. Conclusion: continuity from above for null-measurable sets, then the ε-n argument. -/
theorem tendsToOneOn_of_bad_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F G : Set Ω) (E : ℝ → Set Ω) (C : ℝ → ℕ → Set Ω) (B : ℕ → Set Ω)
    (hB : ∀ n, NullMeasurableSet (B n) P) (hBanti : Antitone B)
    (hBG : (⋂ n, B n) ⊆ Gᶜ) (hG : P Gᶜ = 0)
    (hC : ∀ n, Tendsto (fun ε => P (C ε n)) (𝓝[>] 0) (𝓝 0))
    (hcont : ∀ᶠ n in atTop, ∀ ε, F ∩ G ∩ (E ε)ᶜ ⊆ C ε n ∪ B n) :
    TendsToOneOn P F E := by
  have hInter : P (⋂ n, B n) = 0 := measure_mono_null hBG hG
  have hBlim : Tendsto (fun n => P (B n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) hB hBanti ⟨0, measure_ne_top P _⟩
    rw [hInter] at h
    exact h
  unfold TendsToOneOn
  refine ENNReal.tendsto_nhds_zero.2 fun c hc => ?_
  have hc2 : (0 : ENNReal) < c / 2 := ENNReal.half_pos hc.ne'
  obtain ⟨n, hn1, hn2⟩ := (hcont.and (hBlim.eventually (gt_mem_nhds hc2))).exists
  have hCev := (hC n).eventually (gt_mem_nhds hc2)
  filter_upwards [hCev] with ε hε
  have hsub : F ∩ (E ε)ᶜ ⊆ Gᶜ ∪ (C ε n ∪ B n) := by
    intro ω hω
    by_cases hG' : ω ∈ G
    · exact Or.inr (hn1 ε ⟨⟨hω.1, hG'⟩, hω.2⟩)
    · exact Or.inl hG'
  calc P (F ∩ (E ε)ᶜ) ≤ P (Gᶜ ∪ (C ε n ∪ B n)) := measure_mono hsub
    _ ≤ P Gᶜ + P (C ε n ∪ B n) := measure_union_le _ _
    _ = P (C ε n ∪ B n) := by rw [hG, zero_add]
    _ ≤ P (C ε n) + P (B n) := measure_union_le _ _
    _ ≤ c / 2 + c / 2 := add_le_add hε.le hn2.le
    _ = c := ENNReal.add_halves c

end StoppedInteriorGeometry
end MatedCRT
