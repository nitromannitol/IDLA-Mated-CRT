import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.CellAnnulus
import MatedCRT.Proofs.Sec4.DivSandpileLowerBound.StrictGap

/-! # Discrete obstacle barrier near the pole -/

namespace MatedCRT

open Set Metric Filter Topology

/-- A nonpositive multiple of the Green kernel is subharmonic also at the
pole. A boundary upper bound therefore propagates across any finite subdomain,
whether or not it contains the pole. -/
theorem nonpositive_scaled_greenKernel_le_of_boundary_le
    {m : ℤ → ℤ → ℕ} {A B : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite) (hBA : B ⊆ A)
    {o : ℤ} (ho : o ∈ A) {c M : ℝ} (hc : c ≤ 0)
    (hbound : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∉ B → c * greenKernel m A o b ≤ M) :
    ∀ b ∈ B, c * greenKernel m A o b ≤ M := by
  have hB : B.Finite := hA.subset hBA
  have hsub : ∀ b ∈ B, 0 ≤ lapSum hlf (fun x => c * greenKernel m A o x - M) b := by
    intro b hb
    have hlap := greenKernelLaplacianStep m A hsymm hlf hcons hA o ho b (hBA hb)
    have hconst : mLaplacian m (fun _ : ℤ => -M) b = 0 := by simp [mLaplacian]
    rw [← mLaplacian_mul_mdeg hlf]
    have heq : (fun x => c * greenKernel m A o x - M) =
        (fun x => c * greenKernel m A o x + -M) := by funext x; ring
    rw [heq, mLaplacian_add_of_locallyFinite hlf, mLaplacian_const_mul, hlap, hconst]
    by_cases hb0 : b = o
    · simp only [hb0, ↓reduceIte, mul_one, add_zero]
      exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hc
        (neg_nonpos.mpr (inv_nonneg.mpr (Nat.cast_nonneg _)))) (Nat.cast_nonneg _)
    · simp [hb0]
  have h := nonpos_of_lapSum_nonneg hlf hB (escape_of_adjacent_succ hcons hB) hsub
    (fun a ha b hab hb => sub_nonpos.mpr (hbound a ha b hab hb))
  intro b hb
  exact sub_nonpos.mp (h b hb)

/-- A boundary upper bound for the discrete obstacle propagates inside an
arbitrary finite set of interior vertices, including the source vertex. -/
theorem matedObstacle_le_of_boundary_le {m : ℤ → ℤ → ℕ} {ε ρ t M : ℝ} {η : ℝ → ℂ}
    {B : Set ℤ} (hsymm : ∀ a b, m a b = m b a)
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hA : (ballInterior ε η ρ).Finite) (hBA : B ⊆ ballInterior ε η ρ)
    (ho : (0 : ℤ) ∈ ballInterior ε η ρ) (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hbound : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∉ B → matedObstacle m ε η ρ t b ≤ M) :
    ∀ b ∈ B, matedObstacle m ε η ρ t b ≤ M := by
  apply nonpositive_scaled_greenKernel_le_of_boundary_le hsymm hlf hcons hA hBA ho
    (neg_nonpos.mpr (div_nonneg ht hε))
  exact hbound

/-- If the least supersolution is larger inside a finite vertex set than a
boundary upper bound for the obstacle, then the whole set lies in the discrete
obstacle cluster. -/
theorem subset_matedDiscreteCluster_of_pole_barrier
    {m : ℤ → ℤ → ℕ} {ε ρ t M : ℝ} {η : ℝ → ℂ} {B : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : (ballInterior ε η ρ).Finite)
    (hBA : B ⊆ ballInterior ε η ρ) (ho : (0 : ℤ) ∈ ballInterior ε η ρ)
    (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hbound : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∉ B → matedObstacle m ε η ρ t b ≤ M)
    (hw : ∀ a ∈ B, M < matedLeastSupersolution m ε η ρ t a) :
    B ⊆ matedDiscreteCluster m ε η ρ t := by
  have hφ := matedObstacle_le_of_boundary_le hsymm hlf hcons hA hBA ho ht hε hbound
  intro a ha
  exact ⟨(hBA ha).1, (hφ a ha).trans_lt (hw a ha)⟩

/-- The pole barrier covers every point whose chosen cell belongs to the inner
vertex set. -/
theorem subset_fillCells_matedDiscreteCluster_of_pole_barrier
    {m : ℤ → ℤ → ℕ} {ε ρ t M : ℝ} {η : ℝ → ℂ} {B : Set ℤ} {K : Set ℂ}
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hε : 0 < ε) (ht : 0 ≤ t)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : (ballInterior ε η ρ).Finite)
    (hBA : B ⊆ ballInterior ε η ρ) (ho : (0 : ℤ) ∈ ballInterior ε η ρ)
    (hbound : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∉ B → matedObstacle m ε η ρ t b ≤ M)
    (hw : ∀ a ∈ B, M < matedLeastSupersolution m ε η ρ t a)
    (hK : ∀ x ∈ K, vertexOf ε η x ∈ B) :
    K ⊆ fillCells ε η (matedDiscreteCluster m ε η ρ t) := by
  have hB := subset_matedDiscreteCluster_of_pole_barrier hsymm hlf hcons hA hBA ho ht hε.le hbound hw
  intro x hx
  simp only [fillCells, mem_iUnion]
  exact ⟨vertexOf ε η x, hB (hK x hx), Tightness.mem_cell_vertexOf hη hp hsurj hε x⟩

/-- A boundary estimate on a continuum annulus propagates through the discrete
obstacle to the inner ball. The cell-diameter hypothesis transfers graph-boundary
vertices into the annulus. -/
theorem ball_subset_fillCells_matedDiscreteCluster_of_annular_pole_barrier
    {μ : MeasureTheory.Measure ℂ} {m : ℤ → ℤ → ℕ} {ε ρ t M r d : ℝ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : (ballInterior ε η ρ).Finite)
    (hcell : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hBA : cellVertices ε η (ball 0 r) ⊆ ballInterior ε η ρ)
    (ho : (0 : ℤ) ∈ ballInterior ε η ρ)
    (hdiam : ∀ b ∈ cellVertices ε η (ball 0 (r + d)),
      ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y ≤ d)
    (hbound : ∀ x : ℂ, r - d ≤ dist x 0 → dist x 0 < r + 2 * d →
      matedObstacle m ε η ρ t (vertexOf ε η x) ≤ M)
    (hw : ∀ a ∈ cellVertices ε η (ball 0 r), M < matedLeastSupersolution m ε η ρ t a) :
    ball (0 : ℂ) r ⊆ fillCells ε η (matedDiscreteCluster m ε η ρ t) := by
  refine subset_fillCells_matedDiscreteCluster_of_pole_barrier hη.1 hp hη.2.2.1 hε ht
    hsymm hlf hcons hA hBA ho ?_ hw ?_
  · intro a ha b hab hb
    obtain ⟨w, hwa, hwb⟩ := hcell a b hab
    obtain ⟨y, hya, hy⟩ := ha
    have ha' : a ∈ cellVertices ε η (ball 0 (r + d)) := by
      refine ⟨y, hya, ?_⟩
      change dist y 0 < r + d
      have hy' : dist y 0 < r := hy
      linarith
    have hwlow : r ≤ dist w 0 := by
      have : w ∉ ball (0 : ℂ) r := fun hw => hb ⟨w, hwb, hw⟩
      exact le_of_not_gt this
    have hwupp : dist w 0 < r + d := by
      have hwy := hdiam a ha' w hwa y hya
      have hy' : dist y 0 < r := hy
      have htri := dist_triangle w y 0
      linarith
    have hb' : b ∈ cellVertices ε η (ball 0 (r + d)) := ⟨w, hwb, hwupp⟩
    obtain ⟨x, hxb, hvertex⟩ := exists_vertexOf_eq_of_area_parametrized hη hp hε b
    have hxw := hdiam b hb' x hxb w hwb
    have hwx := hdiam b hb' w hwb x hxb
    have htri₁ := dist_triangle w x 0
    have htri₂ := dist_triangle x w 0
    have hlo : r - d ≤ dist x 0 := by linarith
    have hhi : dist x 0 < r + 2 * d := by linarith
    simpa only [hvertex] using hbound x hlo hhi
  · intro x hx
    exact ⟨x, Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε x, hx⟩

/-- Small cells meeting an inner ball do not meet the boundary of a larger
ball when their diameter is below the separation of the two radii. -/
theorem cellVertices_ball_subset_ballInterior_of_diameter
    {ε ρ r d : ℝ} {η : ℝ → ℂ} (hρ : r + d < ρ)
    (hdiam : ∀ b ∈ cellVertices ε η (ball 0 r),
      ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y ≤ d) :
    cellVertices ε η (ball 0 r) ⊆ ballInterior ε η ρ := by
  intro a ha
  obtain ⟨y, hya, hy⟩ := ha
  have hinside : cell ε η a ⊆ ball 0 ρ := by
    intro x hx
    have hxy := hdiam a ⟨y, hya, hy⟩ x hx y hya
    have htri := dist_triangle x y (0 : ℂ)
    have hy' : dist y 0 < r := hy
    change dist x 0 < ρ
    linarith
  refine ⟨⟨y, hya, hinside hya⟩, ?_⟩
  rintro ⟨x, hx, hfront⟩
  rw [isOpen_ball.frontier_eq] at hfront
  exact hfront.2 (hinside hx)

/-- With small cells and the source-cell identification, annular control of the
obstacle and an inner lower bound for the least supersolution imply coverage of
the inner ball. -/
theorem ball_subset_fillCells_of_small_cells_and_annular_barrier
    {μ : MeasureTheory.Measure ℂ} {m : ℤ → ℤ → ℕ} {ε ρ t M r d : ℝ} {η : ℝ → ℂ}
    (hη : IsAreaParametrized μ η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) (ht : 0 ≤ t) (hr : 0 < r) (hd : 0 ≤ d) (hρ : r + d < ρ)
    (hsource : vertexOf ε η 0 = 0)
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0)
    (hcell : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ b ∈ cellVertices ε η (ball 0 (r + d)),
      ∀ x ∈ cell ε η b, ∀ y ∈ cell ε η b, dist x y ≤ d)
    (hbound : ∀ x : ℂ, r - d ≤ dist x 0 → dist x 0 < r + 2 * d →
      matedObstacle m ε η ρ t (vertexOf ε η x) ≤ M)
    (hw : ∀ a ∈ cellVertices ε η (ball 0 r), M < matedLeastSupersolution m ε η ρ t a) :
    ball (0 : ℂ) r ⊆ fillCells ε η (matedDiscreteCluster m ε η ρ t) := by
  have hBA : cellVertices ε η (ball 0 r) ⊆ ballInterior ε η ρ := by
    apply cellVertices_ball_subset_ballInterior_of_diameter hρ
    intro b hb
    apply hdiam b
    obtain ⟨x, hxb, hx⟩ := hb
    refine ⟨x, hxb, ?_⟩
    change dist x 0 < r + d
    have hx' : dist x 0 < r := hx
    linarith
  have ho : (0 : ℤ) ∈ ballInterior ε η ρ := by
    apply hBA
    rw [← hsource]
    exact ⟨0, Tightness.mem_cell_vertexOf hη.1 hp hη.2.2.1 hε 0, by simpa using hr⟩
  have hA : (ballInterior ε η ρ).Finite := by
    apply (Tightness.cellVertices_finite hη.1 hp hε
      (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) ρ))).subset
    exact sdiff_subset
  exact ball_subset_fillCells_matedDiscreteCluster_of_annular_pole_barrier hη hp hε ht hd
    hsymm hlf hcons hA hcell hBA ho hdiam hbound hw

end MatedCRT
