import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.ClusterComparison
import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.Cells

/-!
# Coverage away from the coincidence set

Uniform approximation of the obstacle and the least supersolution covers every set
on which their continuum gap has a positive uniform lower bound.
-/

namespace MatedCRT

open Set Metric Filter Topology
open scoped Uniformity

/-- A continuous strictly positive obstacle gap has a uniform positive lower bound
on each compact subset of the noncoincidence set. -/
theorem exists_uniform_gap_on_compact {K : Set ℂ} {w φ : ℂ → ℝ}
    (hK : IsCompact K) (hw : ContinuousOn w K) (hφ : ContinuousOn φ K)
    (hgap : ∀ x ∈ K, φ x < w x) :
    ∃ s : ℝ, 0 < s ∧ ∀ x ∈ K, s ≤ w x - φ x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (hw.sub hφ)
    refine ⟨w x - φ x, sub_pos.mpr (hgap x hx), ?_⟩
    exact fun y hy => hmin hy
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

/-- A uniform positive continuum obstacle gap and approximation errors smaller than
half the gap imply coverage by the discrete obstacle cluster. The hypothesis on the
obstacle concerns the actual discrete obstacle, including its source vertex. -/
theorem subset_fillCells_matedDiscreteCluster_of_strict_gap
    {m : ℤ → ℤ → ℕ} {ε ρ t mε s : ℝ} {η : ℝ → ℂ}
    {K : Set ℂ} {w φ : ℂ → ℝ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : 0 < ε) (hmε : 0 ≤ mε)
    (hK : K ⊆ ball 0 ρ) (_hs : 0 < s)
    (hgap : ∀ x ∈ K, s ≤ w x - φ x)
    (hw : ∀ x ∈ K,
      |rescale mε ε η (matedLeastSupersolution m ε η ρ t) x - w x| < s / 2)
    (hφ : ∀ x ∈ K,
      |rescale mε ε η (matedObstacle m ε η ρ t) x - φ x| < s / 2) :
    K ⊆ fillCells ε η (matedDiscreteCluster m ε η ρ t) := by
  intro x hx
  have hcell : x ∈ cell ε η (vertexOf ε η x) :=
    Tightness.mem_cell_vertexOf hη hp hsurj hε x
  have hvertex : vertexOf ε η x ∈ cellVertices ε η (ball 0 ρ) :=
    ⟨x, hcell, hK hx⟩
  have hdiff : 0 < rescale mε ε η (matedLeastSupersolution m ε η ρ t) x -
      rescale mε ε η (matedObstacle m ε η ρ t) x := by
    have hw' := abs_lt.mp (hw x hx)
    have hφ' := abs_lt.mp (hφ x hx)
    have hg := hgap x hx
    linarith
  have hpositive : 0 < matedLeastSupersolution m ε η ρ t (vertexOf ε η x) -
      matedObstacle m ε η ρ t (vertexOf ε η x) := by
    simp only [rescale, ← mul_sub] at hdiff
    exact pos_of_mul_pos_right hdiff (inv_nonneg.mpr hmε)
  simp only [fillCells, mem_iUnion]
  refine ⟨vertexOf ε η x, ?_, hcell⟩
  change vertexOf ε η x ∈ cellVertices ε η (ball 0 ρ) ∧ _
  exact ⟨hvertex, sub_pos.mp hpositive⟩

/-- Uniform convergence covers a compact subset of the strict continuum
noncoincidence set eventually along any positive sequence of meshes. -/
theorem eventually_subset_fillCells_matedDiscreteCluster_of_strict_gap
    {m : ℕ → ℤ → ℤ → ℕ} {ε mε : ℕ → ℝ} {ρ t : ℝ} {η : ℝ → ℂ}
    {K : Set ℂ} {w φ : ℂ → ℝ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : ∀ n, 0 < ε n) (hmε : ∀ n, 0 ≤ mε n)
    (hK : K ⊆ ball 0 ρ) (hcompact : IsCompact K)
    (hwc : ContinuousOn w K) (hφc : ContinuousOn φ K)
    (hgap : ∀ x ∈ K, φ x < w x)
    (hw : TendstoUniformlyOn (fun n => rescale (mε n) (ε n) η
      (matedLeastSupersolution (m n) (ε n) η ρ t)) w atTop K)
    (hφ : TendstoUniformlyOn (fun n => rescale (mε n) (ε n) η
      (matedObstacle (m n) (ε n) η ρ t)) φ atTop K) :
    ∀ᶠ n in atTop, K ⊆ fillCells (ε n) η (matedDiscreteCluster (m n) (ε n) η ρ t) := by
  obtain ⟨s, hs, hsgap⟩ := exists_uniform_gap_on_compact hcompact hwc hφc hgap
  have hU : {p : ℝ × ℝ | dist p.1 p.2 < s / 2} ∈ 𝓤 ℝ :=
    Metric.mem_uniformity_dist.mpr ⟨s / 2, half_pos hs, fun _ _ h => h⟩
  filter_upwards [hw _ hU, hφ _ hU] with n hwn hφn
  apply subset_fillCells_matedDiscreteCluster_of_strict_gap hη hp hsurj (hε n) (hmε n)
    hK hs hsgap
  · intro x hx
    simpa [Real.dist_eq, abs_sub_comm] using hwn x hx
  · intro x hx
    simpa [Real.dist_eq, abs_sub_comm] using hφn x hx

end MatedCRT
