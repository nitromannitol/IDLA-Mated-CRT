import MatedCRT.Proofs.Sec4.GreenLaplacian
import MatedCRT.Proofs.Sec3.ConvergenceNormalizedExitTime.BumpDirichlet

/-!
# Discrete comparison on a disc

Deterministic discrete potential theory for Steps 2 and 3 of the proof of Lemma 4.8
(paper/idla_mated_crt-corrected.tex, l.1803-1915), on the vertex set `A = V^ε(B_r(z)) \ V^ε(∂B_r(z))`:

* `cell_subset_ball_of_mem_interiorCellVertices`: the cell of a vertex of `A` lies in `B_r(z)` (cells are connected);
* `vBoundary_interiorCellVertices_subset`: if the cells of adjacent vertices intersect, the vertex boundary of `A` lies
  in `V^ε(∂B_r(z))`;
* `dirichletData`: the solution of the discrete Dirichlet problem `Δ^ε f = 0` on `A`, `f = g` off `A` (`g` plus the
  Green solution `finitePoissonSolution` of `Δ^ε v = -Δ^ε g` on `A`);
* `le_add_of_maxPrinciple`: the comparison `W ≤ F + c` propagates from `V^ε(∂B_r(z))` to `V^ε(B_r(z))` under the
  maximum principle (Lemma 2.13) for `W - F` on `A`.
-/

namespace MatedCRT

open Set Metric Filter Topology

/-- A cell of a vertex of `V^ε(B_r(z)) \ V^ε(∂B_r(z))` lies in `B_r(z)`: it is connected, meets `B_r(z)` and misses
`∂B_r(z)`. -/
theorem cell_subset_ball_of_mem_interiorCellVertices {ε r : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ}
    (hr : 0 < r) {k : ℤ} (hk : k ∈ interiorCellVertices ε η (ball z r)) : cell ε η k ⊆ ball z r := by
  have hconn : IsPreconnected (cell ε η k) := isPreconnected_Icc.image η hη.continuousOn
  have hsub : cell ε η k ⊆ ball z r ∪ (closedBall z r)ᶜ := by
    intro y hy
    by_cases hyb : y ∈ ball z r
    · exact Or.inl hyb
    · right
      intro hyc
      apply hk.2
      refine ⟨y, hy, ?_⟩
      rw [frontier_ball z hr.ne']
      rw [mem_ball] at hyb
      exact mem_sphere.2 (le_antisymm (mem_closedBall.1 hyc) (not_lt.1 hyb))
  exact hconn.subset_left_of_subset_union isOpen_ball isClosed_closedBall.isOpen_compl
    (Disjoint.mono_left ball_subset_closedBall disjoint_compl_right) hsub hk.1

/-- If the cells of adjacent vertices intersect, the vertex boundary of `V^ε(B_r(z)) \ V^ε(∂B_r(z))` lies in
`V^ε(∂B_r(z))`. -/
theorem vBoundary_interiorCellVertices_subset {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ}
    (hr : 0 < r) (hcells : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) :
    vBoundary m (interiorCellVertices ε η (ball z r)) ⊆ cellVertices ε η (sphere z r) := by
  rintro b ⟨hbA, a, ha, hab⟩
  obtain ⟨y, hya, hyb⟩ := hcells a b hab
  have hyball : y ∈ ball z r := cell_subset_ball_of_mem_interiorCellVertices hη hr ha hya
  have hbball : b ∈ cellVertices ε η (ball z r) :=
    show (cell ε η b ∩ ball z r).Nonempty from ⟨y, hyb, hyball⟩
  by_contra hbs
  exact hbA ⟨hbball, by rwa [frontier_ball z hr.ne']⟩

/-- A vertex of `V^ε(B_r(z))` outside `V^ε(B_r(z)) \ V^ε(∂B_r(z))` lies in `V^ε(∂B_r(z))`. -/
theorem mem_cellVertices_sphere_of_not_mem_interior {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ} (hr : 0 < r) {a : ℤ}
    (ha : a ∈ cellVertices ε η (ball z r)) (haA : a ∉ interiorCellVertices ε η (ball z r)) :
    a ∈ cellVertices ε η (sphere z r) := by
  by_contra h
  exact haA ⟨ha, by rwa [frontier_ball z hr.ne']⟩

/-- `Δ(u - v) = Δu - Δv` on a locally finite multigraph. -/
theorem mLaplacian_sub_of_locallyFinite {α : Type*} {m : α → α → ℕ} (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (u v : α → ℝ) (a : α) :
    mLaplacian m (fun x => u x - v x) a = mLaplacian m u a - mLaplacian m v a := by
  have h := mLaplacian_add_of_locallyFinite hlf u (fun x => (-1 : ℝ) * v x) a
  rw [mLaplacian_const_mul] at h
  have hfun : (fun x => u x - v x) = (fun x => u x + (-1 : ℝ) * v x) := by
    funext x; ring
  rw [hfun, h]
  ring

/-- The solution of the discrete Dirichlet problem `Δf = 0` on `A`, `f = g` off `A`: `g` plus the Green solution of
`Δv = -Δg` on `A` with zero data off `A`. -/
noncomputable def dirichletData (m : ℤ → ℤ → ℕ) (A : Set ℤ) (g : ℤ → ℝ) (a : ℤ) : ℝ :=
  g a + finitePoissonSolution m A (fun b => -mLaplacian m g b) a

/-- `dirichletData` has the prescribed values off `A`. -/
theorem dirichletData_of_not_mem {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hA : A.Finite) (g : ℤ → ℝ) {a : ℤ} (ha : a ∉ A) :
    dirichletData m A g a = g a := by
  simp [dirichletData, finitePoissonSolution_zero hA _ ha]

/-- `dirichletData` is discrete harmonic on `A`. -/
theorem mLaplacian_dirichletData {m : ℤ → ℤ → ℕ} (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} (hA : A.Finite) (g : ℤ → ℝ) {a : ℤ} (ha : a ∈ A) :
    mLaplacian m (dirichletData m A g) a = 0 := by
  have hfun : dirichletData m A g =
      fun x => g x + finitePoissonSolution m A (fun b => -mLaplacian m g b) x := rfl
  rw [hfun, mLaplacian_add_of_locallyFinite hlf g (finitePoissonSolution m A fun b => -mLaplacian m g b),
    finitePoissonSolution_laplacian hlf hcons hA _ ha]
  simp

/-- **Discrete comparison on a disc.** If `W - F` satisfies the maximum principle on
`A = V^ε(B_r(z)) \ V^ε(∂B_r(z))` (Lemma 2.13), the cells of adjacent vertices intersect and `W ≤ F + c` on
`V^ε(∂B_r(z))`, then `W ≤ F + c` on `V^ε(B_r(z))`. -/
theorem le_add_of_maxPrinciple {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {z : ℂ} (hr : 0 < r)
    (hcells : ∀ j k : ℤ, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) {W F : ℤ → ℝ} {c : ℝ}
    (hmax : ∀ a ∈ interiorCellVertices ε η (ball z r),
      ∃ b ∈ vBoundary m (interiorCellVertices ε η (ball z r)), W a - F a ≤ W b - F b)
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r), W b ≤ F b + c) :
    ∀ a ∈ cellVertices ε η (ball z r), W a ≤ F a + c := by
  intro a ha
  by_cases haA : a ∈ interiorCellVertices ε η (ball z r)
  · obtain ⟨b, hb, hab⟩ := hmax a haA
    have := hbd b (vBoundary_interiorCellVertices_subset hη hr hcells hb)
    linarith
  · exact hbd a (mem_cellVertices_sphere_of_not_mem_interior hr ha haA)

end MatedCRT
