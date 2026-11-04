import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.CellBump
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.FixedGreenSum
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GreenRepresentation
import MatedCRT.Proofs.Sec7.OdometerBoundMass.StoppedOdometer

/-! # Near-pole Green sums and bump functions -/

namespace MatedCRT

open Set Metric Filter Topology

/-- On a finite domain the normalized exit time is a finite Green sum. -/
theorem normExitTime_eq_finset_sum (m : ℤ → ℤ → ℕ) (A : Set ℤ)
    (hA : A.Finite) (a : ℤ) :
    normExitTime m A a = ∑ b ∈ hA.toFinset, greenKernel m A a b := by
  classical
  unfold normExitTime
  rw [tsum_subtype A (fun b => greenKernel m A a b), tsum_eq_sum (s := hA.toFinset) ?_]
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [Set.indicator_of_mem (hA.mem_toFinset.1 hb)]
  · intro b hb
    exact Set.indicator_of_notMem (fun h => hb (hA.mem_toFinset.2 h)) _

/-- Splitting the finite Green sum separates the cells meeting the pole ball. -/
theorem normExitTime_eq_truncated_add_near
    {η : ℝ → ℂ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) {ε : ℝ} (hε : 0 < ε)
    (z y : ℂ) (r δ : ℝ) (m : ℤ → ℤ → ℕ) (a : ℤ) :
    ∃ F : Finset ℤ,
      (F : Set ℤ) = interiorCellVertices ε η (ball z r) ∩
        cellVertices ε η (ball y δ) ∧
      normExitTime m (interiorCellVertices ε η (ball z r)) a =
        (∑ b ∈ truncatedGreenCells ε η z y r δ,
          greenKernel m (interiorCellVertices ε η (ball z r)) a b) +
        (∑ b ∈ F, greenKernel m (interiorCellVertices ε η (ball z r)) a b) := by
  classical
  let A := interiorCellVertices ε η (ball z r)
  let C := cellVertices ε η (ball y δ)
  have hA : A.Finite := (Tightness.cellVertices_finite hη hp hε isBounded_ball).subset
    (by intro b hb; exact hb.1)
  let F := hA.toFinset.filter (fun b => b ∈ C)
  have hfar : truncatedGreenCells ε η z y r δ =
      hA.toFinset.filter (fun b => b ∉ C) := by
    apply Finset.coe_injective
    rw [coe_truncatedGreenCells hη hp hε]
    ext b
    simp [A, C]
  refine ⟨F, ?_, ?_⟩
  · ext b
    simp [F, A, C]
  · rw [normExitTime_eq_finset_sum m A hA a, hfar]
    exact (Finset.sum_filter_add_sum_filter_not hA.toFinset
      (fun b => b ∈ C) (fun b => greenKernel m A a b)).symm.trans (add_comm _ _)

/-- A nonnegative bump dominates the Green sum on a subcollection when
its values and the vertex degrees are at least one there. -/
theorem greenSum_le_degree_weighted_bump
    (m : ℤ → ℤ → ℕ) (A : Set ℤ) (F N : Finset ℤ) (a : ℤ) (φ : ℤ → ℝ)
    (hNF : N ⊆ F) (hφ0 : ∀ b ∈ F, 0 ≤ φ b)
    (hφ1 : ∀ b ∈ N, 1 ≤ φ b) (hdeg : ∀ b ∈ N, 1 ≤ (mdeg m b : ℝ)) :
    (∑ b ∈ N, greenKernel m A a b) ≤
      ∑ b ∈ F, (mdeg m b : ℝ) * φ b * greenKernel m A a b := by
  classical
  calc
    _ ≤ ∑ b ∈ N, (mdeg m b : ℝ) * φ b * greenKernel m A a b := by
      apply Finset.sum_le_sum
      intro b hb
      have hweight : 1 ≤ (mdeg m b : ℝ) * φ b := by
        nlinarith [hφ1 b hb, hdeg b hb, mul_nonneg (sub_nonneg.mpr (hdeg b hb))
          (sub_nonneg.mpr (hφ1 b hb))]
      simpa using mul_le_mul_of_nonneg_right hweight (Sec7.greenKernel_nonneg m A a b)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hNF
      intro b hb _
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hφ0 b hb))
        (Sec7.greenKernel_nonneg m A a b)

/-- A bump equal to one on the diameter-enlarged pole ball controls all
cells meeting the original pole ball. -/
theorem greenSum_near_le_bump
    {η : ℝ → ℂ} {ε δ d : ℝ} {y : ℂ} (hη : Continuous η) (hε : 0 ≤ ε)
    (m : ℤ → ℤ → ℕ) (A : Set ℤ) (F N : Finset ℤ) (a : ℤ) (φ : ℂ → ℝ)
    (hNF : N ⊆ F) (hnear : ∀ b ∈ N, b ∈ cellVertices ε η (ball y δ))
    (hdiam : ∀ b ∈ N, diam (cell ε η b) ≤ d)
    (hone : ∀ x ∈ ball y (δ + d), φ x = 1)
    (hφ0 : ∀ b ∈ F, 0 ≤ φ (vertexPoint ε η b))
    (hdeg : ∀ b ∈ N, 1 ≤ (mdeg m b : ℝ)) :
    (∑ b ∈ N, greenKernel m A a b) ≤
      ∑ b ∈ F, (mdeg m b : ℝ) * φ (vertexPoint ε η b) * greenKernel m A a b := by
  apply greenSum_le_degree_weighted_bump m A F N a (fun b => φ (vertexPoint ε η b))
    hNF hφ0 ?_ hdeg
  intro b hb
  rw [bump_eq_one_of_cell_meets hη hε (hnear b hb) (hdiam b hb) hone]

/-- The near-pole Green sum is bounded by the zero-boundary solution with
negative bump as its Laplacian. -/
theorem greenSum_near_le_dirichlet_solution
    {η : ℝ → ℂ} {ε δ d : ℝ} {y : ℂ} (hη : Continuous η) (hε : 0 ≤ ε)
    (m : ℤ → ℤ → ℕ) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (A : Set ℤ) (hA : A.Finite)
    (N : Finset ℤ) (a : ℤ) (φ : ℂ → ℝ) (u : ℤ → ℝ)
    (hNA : N ⊆ hA.toFinset) (hnear : ∀ b ∈ N, b ∈ cellVertices ε η (ball y δ))
    (hdiam : ∀ b ∈ N, diam (cell ε η b) ≤ d)
    (hone : ∀ x ∈ ball y (δ + d), φ x = 1)
    (hφ0 : ∀ b ∈ hA.toFinset, 0 ≤ φ (vertexPoint ε η b))
    (hu0 : ∀ b ∉ A, u b = 0)
    (hu : ∀ b ∈ A, mLaplacian m u b = -φ (vertexPoint ε η b)) :
    (∑ b ∈ N, greenKernel m A a b) ≤ u a := by
  classical
  have hdeg : ∀ b, 1 ≤ (mdeg m b : ℝ) := by
    intro b
    exact_mod_cast mdeg_pos_of_ne_zero hlf (hcons b)
  have hbound := greenSum_near_le_bump hη hε m A hA.toFinset N a φ
    hNA hnear hdiam hone hφ0 (fun b _ => hdeg b)
  have hrep := eq_greenPotential_of_zero_boundary hlf hcons hA
    (fun b => φ (vertexPoint ε η b)) u hu0 hu a
  rw [hrep]
  refine hbound.trans_eq ?_
  apply Finset.sum_congr rfl
  intro b hb
  have hd : (mdeg m b : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (hdeg b))
  unfold greenKernel
  field_simp

end MatedCRT
