import MatedCRT.FirstPass.S3i.BoundaryCell
import MatedCRT.FirstPass.S3i.LensDefs

/-!
# Lens geometry and the local zero boundary (plan §5)

Deterministic. Plan Lemma 5, `lensGeometry_fp36`: the enlarged-disk lens `U = B_{r+4δ}(z) ∩ B_{s/4}(P)`
(`δ = ε^b`, `s = ε^(b/2)`, `P = ballRetraction z r (η(εv))`) has `v` as an interior cell, is a convex
(hence simply connected) open set inside `B_{ρ₀}`, and its boundary is at distance `≤ 6δ` from `q = η(εv)`,
while no cell meeting `B_{s/16}(q)` on `∂U` is a far cell of the sphere `∂B_{s/4}(P)`.

Uses Lemma 4 (`H4.boundaryVertexGeometry_fp36_of_ball`, `BoundaryCell.lean`). The lens hypothesis
`ball z r ⊆ ball 0 ρ₁` of Lemma 4 is derived here from `houter` and `hρ`.

The definitions `fp36LensDomain`, `fp36LensFarCells`, `FP36GoodEnv` are imported from
`MatedCRT/FirstPass/S3i/LensDefs.lean` (the plan's "Minimal internal definitions").
-/

namespace MatedCRT
namespace FirstPass36
namespace H5

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The distance from `q` to the circle `∂B_r(z)` controls `||q - z| - r|` from below. -/
lemma abs_dist_sub_le_infDist_sphere {z q : ℂ} {r : ℝ} (hr : 0 < r) :
    |dist q z - r| ≤ infDist q (sphere z r) := by
  have hne : (sphere z r).Nonempty :=
    ⟨z + (r : ℂ), by rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hr.le]⟩
  by_contra hcon
  have hcon' : infDist q (sphere z r) < |dist q z - r| := not_le.1 hcon
  obtain ⟨y, hy, hlt⟩ := (infDist_lt_iff hne).1 hcon'
  have h1 := abs_dist_sub_le q y z
  rw [mem_sphere.1 hy] at h1
  linarith

/-- A point of the enlarged circle `∂B_{r+4δ}(z)` within `5δ` of `q`, when `|dist q z - r| ≤ δ`. -/
lemma exists_point_on_enlarged_sphere {z q : ℂ} {r δ : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (habs : |dist q z - r| ≤ δ) :
    ∃ x : ℂ, dist x z = r + 4 * δ ∧ dist x q ≤ 5 * δ := by
  obtain ⟨h1, h2⟩ := abs_le.1 habs
  have hR : 0 ≤ r + 4 * δ := by linarith
  rcases eq_or_ne q z with hqz | hqz
  · have hrδ : r ≤ δ := by
      rw [hqz, dist_self] at h1
      linarith
    refine ⟨z + ((r + 4 * δ : ℝ) : ℂ), ?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hR]
    · rw [hqz, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hR]
      linarith
  · have ht : 0 < dist q z := dist_pos.2 hqz
    have hc : 0 ≤ (r + 4 * δ) / dist q z := div_nonneg hR ht.le
    have hc1 : 0 ≤ (r + 4 * δ) / dist q z - 1 := by
      have : 1 ≤ (r + 4 * δ) / dist q z := (one_le_div ht).2 (by linarith)
      linarith
    refine ⟨z + (((r + 4 * δ) / dist q z : ℝ) : ℂ) * (q - z), ?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc,
        ← dist_eq_norm, div_mul_cancel₀ _ ht.ne']
    · have e : z + (((r + 4 * δ) / dist q z : ℝ) : ℂ) * (q - z) - q
          = ((((r + 4 * δ) / dist q z - 1 : ℝ)) : ℂ) * (q - z) := by
        push_cast
        ring
      rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc1,
        ← dist_eq_norm, sub_mul, div_mul_cancel₀ _ ht.ne', one_mul]
      linarith

/-- **Lemma 5 (plan §5): lens geometry and the local zero boundary.** -/
lemma lensGeometry_fp36
    {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A r ε : ℝ} {z y : ℂ} {ω : Ω} {v : ℤ}
    (hε : 0 < ε) (_hb : 0 < b) (hr : 0 < r)
    (hρ : ρ₀ < ρ₁)
    (hscale : 64 * ε ^ b ≤ ε ^ (b / 2))
    (houter :
      closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀)
    (hgood : FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω)
    (hv : v ∈ vBoundary (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r))) :
    let δ := ε ^ b
    let s := ε ^ (b / 2)
    let η := S.η ω
    let q := vertexPoint ε η v
    let P := ballRetraction z r q
    let U := fp36LensDomain z r δ P s
    let B := fp36LensFarCells ε η P s
    v ∈ interiorCellVertices ε η U ∧
    closure U ⊆ ball 0 ρ₀ ∧
    U ⊆ ball 0 ρ₁ ∧
    IsOpen U ∧ IsConnected U ∧ SimplyConnectedSpace U ∧
    0 < infDist q (frontier U) ∧
    infDist q (frontier U) ≤ 6 * δ ∧
    ∀ k ∈ cellVertices ε η
      (frontier U ∩ ball q (s / 16)),
      k ∉ B := by
  intro δ s η q P U B
  have hδ : 0 < δ := Real.rpow_pos_of_pos hε b
  have hs : 0 < s := Real.rpow_pos_of_pos hε (b / 2)
  have hscale' : 64 * δ ≤ s := hscale
  -- the lens hypothesis of Lemma 4, from `houter` and `hρ`
  have hball : ball z r ⊆ ball 0 ρ₁ := by
    have h1 : ball z r ⊆ ball z (r + 4 * δ) := ball_subset_ball (by linarith)
    exact h1.trans (subset_closure.trans (houter.trans (ball_subset_ball hρ.le)))
  obtain ⟨-, hinf0, hqP0, -⟩ := H4.boundaryVertexGeometry_fp36_of_ball hε hr hball hgood hv
  have hqP : dist q P ≤ δ := hqP0
  have hsph : infDist q (sphere z r) ≤ δ := by
    have h := hinf0
    rw [frontier_ball z hr.ne'] at h
    exact h
  have habs : |dist q z - r| ≤ δ := (abs_dist_sub_le_infDist_sphere hr).trans hsph
  have hab := abs_le.1 habs
  obtain ⟨hA, -, hmesh, -, -, -⟩ := hgood
  have hη : Continuous η := hA.1
  -- the lens `U` and its closure
  have hqU : q ∈ ball z (r + 4 * δ) ∩ ball P (s / 4) := by
    refine ⟨mem_ball.2 ?_, mem_ball.2 ?_⟩
    · linarith [hab.2]
    · linarith
  have hUopen : IsOpen (ball z (r + 4 * δ) ∩ ball P (s / 4)) := isOpen_ball.inter isOpen_ball
  have hclU : closure (ball z (r + 4 * δ) ∩ ball P (s / 4)) ⊆ ball 0 ρ₀ :=
    (closure_mono Set.inter_subset_left).trans houter
  have hUsub : ball z (r + 4 * δ) ∩ ball P (s / 4) ⊆ ball 0 ρ₁ :=
    subset_closure.trans (hclU.trans (ball_subset_ball hρ.le))
  -- a point `x` of the enlarged circle, within `5δ` of `q`, lies on `frontier U`
  obtain ⟨x, hxz, hxq⟩ := exists_point_on_enlarged_sphere hδ.le hr.le habs
  have hxP : x ∈ ball P (s / 4) := by
    rw [mem_ball]
    linarith [dist_triangle x q P]
  have hxcl : x ∈ closure (ball z (r + 4 * δ) ∩ ball P (s / 4)) := by
    have hxz' : x ∈ closure (ball z (r + 4 * δ)) := by
      rw [closure_ball z (show (0 : ℝ) < r + 4 * δ by linarith).ne']
      exact mem_closedBall.2 hxz.le
    have h := (isOpen_ball : IsOpen (ball P (s / 4))).inter_closure ⟨hxP, hxz'⟩
    rwa [Set.inter_comm] at h
  have hxF : x ∈ frontier (ball z (r + 4 * δ) ∩ ball P (s / 4)) := by
    rw [hUopen.frontier_eq]
    refine ⟨hxcl, ?_⟩
    intro hxU
    have h := mem_ball.1 hxU.1
    rw [hxz] at h
    exact lt_irrefl _ h
  -- `q` is interior, and its distance to the frontier is positive and at most `6δ`
  have hqnot : q ∉ frontier (ball z (r + 4 * δ) ∩ ball P (s / 4)) := by
    intro h
    rw [hUopen.frontier_eq] at h
    exact h.2 hqU
  have hinfpos : 0 < infDist q (frontier (ball z (r + 4 * δ) ∩ ball P (s / 4))) :=
    (isClosed_frontier.notMem_iff_infDist_pos ⟨x, hxF⟩).1 hqnot
  have hinfle : infDist q (frontier (ball z (r + 4 * δ) ∩ ball P (s / 4))) ≤ 6 * δ :=
    le_trans (infDist_le_dist_of_mem hxF) (by rw [dist_comm]; linarith)
  -- points of the frontier of `U` are at distance `≥ 3δ` from `q`
  have hfar : ∀ y' ∈ frontier (ball z (r + 4 * δ) ∩ ball P (s / 4)), 3 * δ ≤ dist y' q := by
    intro y' hy'
    rcases frontier_inter_subset _ _ hy' with h | h
    · have h1 : y' ∈ frontier (ball z (r + 4 * δ)) := h.1
      rw [frontier_ball z (show (0 : ℝ) < r + 4 * δ by linarith).ne'] at h1
      have hyz : dist y' z = r + 4 * δ := mem_sphere.1 h1
      linarith [dist_triangle y' q z]
    · have h2 : y' ∈ frontier (ball P (s / 4)) := h.2
      rw [frontier_ball P (show (0 : ℝ) < s / 4 by linarith).ne'] at h2
      have hyP : dist y' P = s / 4 := mem_sphere.1 h2
      linarith [dist_triangle y' q P]
  -- the frontier of `U` lies in the enlarged disk, so the mesh bound applies to cells meeting `U`
  have hqball : q ∈ ball 0 ρ₁ := hUsub hqU
  have hcellq : (cell ε η v ∩ ball 0 ρ₁).Nonempty :=
    ⟨q, H4.vertexPoint_mem_cell hε v, hqball⟩
  have hdiam_v : diam (cell ε η v) ≤ δ := hmesh v hcellq
  refine ⟨?_, hclU, hUsub, hUopen, ?_, ?_, hinfpos, hinfle, ?_⟩
  · -- `v` is an interior cell of `U`
    have hcellU : (cell ε η v ∩ (ball z (r + 4 * δ) ∩ ball P (s / 4))).Nonempty :=
      ⟨q, H4.vertexPoint_mem_cell hε v, hqU⟩
    refine Set.mem_sdiff_of_mem hcellU ?_
    intro hF
    obtain ⟨y', hy'v, hy'F⟩ := hF
    have hd : dist y' q ≤ δ :=
      le_trans (dist_le_diam_of_mem (H4.cell_isCompact hη v).isBounded hy'v
        (H4.vertexPoint_mem_cell hε v)) hdiam_v
    linarith [hfar y' hy'F]
  · exact ((convex_ball z _).inter (convex_ball P _)).isConnected ⟨q, hqU⟩
  · have hconv : Convex ℝ (ball z (r + 4 * δ) ∩ ball P (s / 4)) :=
      (convex_ball _ _).inter (convex_ball _ _)
    have hcontr : ContractibleSpace ↥(ball z (r + 4 * δ) ∩ ball P (s / 4)) :=
      hconv.contractibleSpace ⟨q, hqU⟩
    exact @SimplyConnectedSpace.ofContractible _ _ hcontr
  · -- no cell meeting `B_{s/16}(q)` on `∂U` is a far cell of `∂B_{s/4}(P)`
    intro k hk hkB
    obtain ⟨y', hyk, hyF, hyq⟩ := hk
    obtain ⟨y'', hy''k, hy''S⟩ := hkB
    have hy0 : y' ∈ ball 0 ρ₁ :=
      ball_subset_ball hρ.le (hclU (frontier_subset_closure hyF))
    have hdk : diam (cell ε η k) ≤ δ := hmesh k ⟨y', hyk, hy0⟩
    have hyy : dist y'' y' ≤ δ :=
      le_trans (dist_le_diam_of_mem (H4.cell_isCompact hη k).isBounded hy''k hyk) hdk
    have hyq' : dist y' q < s / 16 := mem_ball.1 hyq
    have hyP : dist y'' P = s / 4 := mem_sphere.1 hy''S
    linarith [dist_triangle y'' y' q, dist_triangle y'' q P]

end H5
end FirstPass36
end MatedCRT
