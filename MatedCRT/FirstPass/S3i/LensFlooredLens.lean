import MatedCRT.FirstPass.S3i.LensGeometry
import MatedCRT.FirstPass.S3i.LensFlooredGeom

/-!
# Lens geometry for the floored good environment

Floored copy of `H5.lensGeometry_fp36` (S3i/LensGeometry.lean:70) for the good environment `FP36GoodEnvFloored`
(S3i/LensFloored.lean). The body is that of the original, with the floored boundary-vertex lemma
`H4.boundaryVertexGeometry_fp36_of_ball_floored` (S3i/LensFlooredGeom.lean) in place of `H4.boundaryVertexGeometry_fp36_of_ball`.
-/

namespace MatedCRT
namespace FirstPass36
namespace H5

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Lens geometry, floored good environment** (copy of `lensGeometry_fp36`, S3i/LensGeometry.lean:70). -/
lemma lensGeometry_fp36_floored
    {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A β r ε : ℝ} {z y : ℂ} {ω : Ω} {v : ℤ}
    (hε : 0 < ε) (_hb : 0 < b) (hr : 0 < r)
    (hρ : ρ₀ < ρ₁)
    (hscale : 64 * ε ^ b ≤ ε ^ (b / 2))
    (houter :
      closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀)
    (hgood : FP36GoodEnvFloored S ρ₀ ρ₁ b ν A β r z y ε ω)
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
  obtain ⟨-, hinf0, hqP0, -⟩ := H4.boundaryVertexGeometry_fp36_of_ball_floored hε hr hball hgood hv
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
