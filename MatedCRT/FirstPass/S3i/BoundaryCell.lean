import MatedCRT.FirstPass.S3i.Frozen
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions

/-!
# Geometry of a graph-boundary vertex of a lens (plan `CHATGPT-221-idla-3-6-QuenchedLensStep-plan-PRO`, §4, worker H4)

Deterministic (no probability). Plan Lemma 4, `boundaryVertexGeometry_fp36`, proved as
`boundaryVertexGeometry_fp36_of_ball`.

**Deviation from the plan as typed.** The plan states Lemma 4 without the lens hypothesis
`hball : ball z r ⊆ ball 0 ρ₁`. Without it the mesh clause of `FP36GoodEnv` (cells meeting `ball 0 ρ₁`
have diameter `≤ ε ^ b`) does not control the cells of `v` and of its interior neighbours: those meet
`ball z r`, which need not lie in `ball 0 ρ₁`. Then `infDist q (frontier (ball z r)) ≤ δ` and the
`3δ` bound are not derivable from the hypotheses. The hypothesis is the one of `QuenchedLensStep`
(`MatedCRT/FirstPass/S3i/Statement.lean:43`, `ball z r ⊆ ball 0 ρ`) and of
`MatedCRT/FirstPass/S3i/LensStep.lean:122` (`hball`).

The definitions `FiniteExitData`, `FP36OneSidedBEAt`, `FP36GoodEnv` are copies of the plan's
"Minimal internal definitions", kept in the private namespace `MatedCRT.FirstPass36.H4` until the defs
file is committed; merge by renaming.
-/

namespace MatedCRT
namespace FirstPass36
namespace H4

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Finite-state data for almost-sure exit and first-step harmonicity (copy of the plan's definition). -/
def FiniteExitData (m : ℤ → ℤ → ℕ) (A : Set ℤ) : Prop :=
  A.Finite ∧
  (∀ a ∈ A, 0 < mdeg m a) ∧
  ∀ a ∈ A, ∃ b ∈ vBoundary m A, ∃ p : List ℤ,
    IsVPathIn m (vClosure m A) p a b

/-- The pointwise BE property on one fixed environment (copy of the plan's definition). -/
def FP36OneSidedBEAt
    (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ)
    (ρ ν A : ℝ) : Prop :=
  ∀ (D : Set ℂ) (f : ℤ → ℝ),
    D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
    SimplyConnectedSpace D →
    (∀ x ∈ interiorCellVertices ε η D,
      matedLaplacian m f x = 0) →
    ∀ x ∈ cellVertices ε η D, ∀ t : ℝ, 0 < t →
      f x ≤ boundarySupNear ε η D f x t
        + A * discreteSupNorm ε η D f
          * (t / infDist (vertexPoint ε η x) (frontier D)) ^ (-ν)

/-- Everything needed at one environment and mesh (copy of the plan's definition). -/
def FP36GoodEnv {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ₀ ρ₁ b ν A r : ℝ)
    (z y : ℂ) (ε : ℝ) (ω : Ω) : Prop :=
  let η := S.η ω
  let m := S.mult ε ω
  IsAreaParametrized (S.μ ω) η ∧
  (∀ j k : ℤ, m j k ≠ 0 →
    (cell ε η j ∩ cell ε η k).Nonempty) ∧
  (∀ k : ℤ, (cell ε η k ∩ ball 0 ρ₁).Nonempty →
    diam (cell ε η k) ≤ ε ^ b) ∧
  (∀ U : Set ℂ, closure U ⊆ ball 0 ρ₀ →
    FiniteExitData m (cellVertices ε η U) ∧
    FiniteExitData m (interiorCellVertices ε η U)) ∧
  vertexOf ε η y ∈
    interiorCellVertices ε η (ball z r) ∧
  FP36OneSidedBEAt m ε η ρ₁ ν A

/-- A cell is connected: the image of a compact interval under the continuous `η`. -/
lemma cell_isConnected {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (hη : Continuous η) (k : ℤ) :
    IsConnected (cell ε η k) := by
  have hle : ε * ((k : ℝ) - 1) ≤ ε * k := mul_le_mul_of_nonneg_left (by linarith) hε.le
  exact (isConnected_Icc hle).image η hη.continuousOn

/-- A cell is compact, hence bounded. -/
lemma cell_isCompact {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    IsCompact (cell ε η k) := by
  unfold cell
  exact isCompact_Icc.image_of_continuousOn hη.continuousOn

/-- The vertex point `η(εk)` lies in its own cell `η([ε(k-1), εk])`. -/
lemma vertexPoint_mem_cell {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k := by
  have hle : ε * ((k : ℝ) - 1) ≤ ε * k := mul_le_mul_of_nonneg_left (by linarith) hε.le
  exact ⟨ε * k, ⟨hle, le_rfl⟩, rfl⟩

/-- A connected cell meeting the open disk `B_r(z)` and missing its boundary circle lies in the disk
(the connectedness argument of the first non-interior cell, Armitage-Gardiner-style open/closed splitting). -/
lemma cell_subset_ball_of_not_frontier {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (hη : Continuous η)
    {z : ℂ} {r : ℝ} (hr : 0 < r) {k : ℤ}
    (hmeet : (cell ε η k ∩ ball z r).Nonempty)
    (hnf : ¬ (cell ε η k ∩ frontier (ball z r)).Nonempty) :
    cell ε η k ⊆ ball z r := by
  have hsub : cell ε η k ⊆ ball z r ∪ {x : ℂ | r < dist x z} := by
    intro x hx
    rcases lt_trichotomy (dist x z) r with h | h | h
    · exact Set.mem_union_left _ (mem_ball.2 h)
    · exact (hnf ⟨x, hx, by rw [frontier_ball z hr.ne']; exact mem_sphere.2 h⟩).elim
    · exact Set.mem_union_right _ h
  have hv : IsOpen {x : ℂ | r < dist x z} := isOpen_lt continuous_const (by fun_prop)
  have hdisj : Disjoint (ball z r) {x : ℂ | r < dist x z} := by
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have h2 : r < dist x z := hx'
    exact (not_lt.2 h2.le) (mem_ball.1 hx)
  exact (cell_isConnected hε hη k).isPreconnected.subset_left_of_subset_union
    isOpen_ball hv hdisj hsub hmeet

/-- The radial retraction `ballRetraction z r` moves `q` by at most its distance to any point `w` of the
circle `∂B_r(z)`: this is the distance from `q` to the closed disk, bounded by `dist q w`. -/
lemma dist_ballRetraction_le {z w q : ℂ} {r : ℝ} (hr : 0 < r) (hw : dist w z = r) :
    dist q (ballRetraction z r q) ≤ dist q w := by
  unfold ballRetraction
  rcases le_total (dist q z) r with h | h
  · rw [max_eq_left h, div_self hr.ne']
    simp [dist_nonneg]
  · rw [max_eq_right h]
    have hd : 0 < dist q z := lt_of_lt_of_le hr h
    have hc1 : 0 ≤ 1 - r / dist q z := by
      have : r / dist q z ≤ 1 := (div_le_one hd).2 h
      linarith
    have e : q - (z + ((r / dist q z : ℝ) : ℂ) * (q - z))
        = ((1 - r / dist q z : ℝ) : ℂ) * (q - z) := by
      push_cast
      ring
    have hn : dist q (z + ((r / dist q z : ℝ) : ℂ) * (q - z)) = dist q z - r := by
      rw [dist_eq_norm q (z + ((r / dist q z : ℝ) : ℂ) * (q - z)), e, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hc1, ← dist_eq_norm, sub_mul, one_mul,
        div_mul_cancel₀ r hd.ne']
    rw [hn]
    have h2 := abs_dist_sub_le q w z
    rw [hw] at h2
    linarith [le_abs_self (dist q z - r)]

/-- **Lemma 4 (plan §4, H4) with the lens hypothesis `hball`.** A vertex `v` of the boundary of the interior
of the lens `B_r(z)` has a cell meeting the circle `∂B_r(z)`, its representative `q = η(εv)` is within `δ = ε^b`
of the circle, its radial retraction `P` is within `δ` of `q`, and every interior neighbour `u` of `v`
has `dist(η(εu), P) ≤ 3δ`. -/
lemma boundaryVertexGeometry_fp36_of_ball
    {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A r ε : ℝ} {z y : ℂ} {ω : Ω} {v : ℤ}
    (hε : 0 < ε) (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ₁)
    (hgood : FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω)
    (hv : v ∈ vBoundary (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r))) :
    let δ := ε ^ b
    let η := S.η ω
    let m := S.mult ε ω
    let I := interiorCellVertices ε η (ball z r)
    let q := vertexPoint ε η v
    let P := ballRetraction z r q
    v ∈ cellVertices ε η (frontier (ball z r)) ∧
    infDist q (frontier (ball z r)) ≤ δ ∧
    dist q P ≤ δ ∧
    ∀ u ∈ I, m u v ≠ 0 →
      dist (vertexPoint ε η u) P ≤ 3 * δ := by
  intro δ η m I q P
  obtain ⟨hA, hadj, hmesh, -, -, -⟩ := hgood
  have hη : Continuous η := hA.1
  -- every interior cell lies in the disk
  have hint : ∀ u ∈ I, cell ε η u ⊆ ball z r := fun u hu =>
    cell_subset_ball_of_not_frontier hε hη hr hu.1 hu.2
  -- the mesh bound, on the cells meeting the disk
  have hmeshI : ∀ k : ℤ, (cell ε η k ∩ ball z r).Nonempty → diam (cell ε η k) ≤ δ := by
    intro k hk
    obtain ⟨x, hx1, hx2⟩ := hk
    exact hmesh k ⟨x, hx1, hball hx2⟩
  obtain ⟨hvI, u₀, hu₀, hmu₀⟩ := hv
  obtain ⟨x₀, hx₀u, hx₀v⟩ := hadj u₀ v hmu₀
  have hmeetv : (cell ε η v ∩ ball z r).Nonempty := ⟨x₀, hx₀v, hint u₀ hu₀ hx₀u⟩
  have hmem : v ∈ cellVertices ε η (ball z r) := hmeetv
  -- the cell of `v` meets the circle: otherwise `v` would be interior
  have hvF : v ∈ cellVertices ε η (frontier (ball z r)) := by
    by_contra hnot
    exact hvI (Set.mem_sdiff_of_mem hmem hnot)
  have hwex : ∃ w, w ∈ cell ε η v ∧ w ∈ frontier (ball z r) := hvF
  obtain ⟨w, hwv, hwF⟩ := hwex
  have hwsph : dist w z = r := by
    rw [frontier_ball z hr.ne'] at hwF
    exact mem_sphere.1 hwF
  have hq : q ∈ cell ε η v := vertexPoint_mem_cell hε v
  have hdiam_v : dist q w ≤ δ :=
    le_trans (dist_le_diam_of_mem (cell_isCompact hη v).isBounded hq hwv) (hmeshI v hmeetv)
  have hqP : dist q P ≤ δ :=
    le_trans (dist_ballRetraction_le hr hwsph) hdiam_v
  refine ⟨hvF, le_trans (infDist_le_dist_of_mem hwF) hdiam_v, hqP, ?_⟩
  intro u hu hmuv
  obtain ⟨x, hxu, hxv⟩ := hadj u v hmuv
  have hdu : dist (vertexPoint ε η u) x ≤ δ :=
    le_trans (dist_le_diam_of_mem (cell_isCompact hη u).isBounded (vertexPoint_mem_cell hε u) hxu)
      (hmeshI u hu.1)
  have hdx : dist x q ≤ δ :=
    le_trans (dist_le_diam_of_mem (cell_isCompact hη v).isBounded hxv hq) (hmeshI v hmeetv)
  have h1 := dist_triangle (vertexPoint ε η u) x q
  have h2 := dist_triangle (vertexPoint ε η u) q P
  linarith

end H4
end FirstPass36
end MatedCRT
