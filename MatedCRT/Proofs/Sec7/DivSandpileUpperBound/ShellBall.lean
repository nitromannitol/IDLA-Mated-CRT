import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellGeometry
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellStep
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Ball bounds for the shells from their cumulative radius budget. -/

namespace MatedCRT.Sec7

open Set Metric

/-- The filled graph closure of an iterated shell lies in the requested open
ball when its initial ball and cumulative growth have a strict margin. -/
theorem fill_iterated_shells_closure_subset_ball
    {m : ℤ → ℤ → ℕ} {ε D R₀ R : ℝ} {η : ℝ → ℂ}
    (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ)
    (hη : Continuous η) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀)
    (hr : ∀ k < n, 0 ≤ r k)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (h0 : Θ 0 ⊆ cellVertices ε η (closedBall 0 R₀))
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hdiam : ∀ k ≤ n, ∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D)
    (hmargin : ((∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D)) + R₀ < R) :
    fillCells ε η (vClosure m (Θ n)) ⊆ ball 0 R := by
  have hstep' : ∀ k < n, Θ (k + 1) ⊆ cellVertices ε η
      (thickening (r k) (fillCells ε η (vClosure m (Θ k)))) := by
    intro k hk
    rw [hstep k hk]
    apply cellVertices_mono
    apply thickening_subset_of_subset
    intro z hz
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨a, Or.inl ha, hza⟩
  have hfill := fill_iterated_shells_subset_cthickening Θ r n hη hD hr hadj h0 hstep' hdiam
  have hnonneg : 0 ≤ (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D) := by
    apply add_nonneg
    · exact Finset.sum_nonneg fun k hk => hr k (Finset.mem_range.mp hk)
    · positivity
  rw [cthickening_closedBall hnonneg hR₀] at hfill
  exact hfill.trans (closedBall_subset_ball hmargin)

/-- The next shell is finite when its own radius also fits within the
cumulative ambient margin. -/
theorem iterated_shell_next_finite
    {m : ℤ → ℤ → ℕ} {ε D R₀ ρ : ℝ} {η : ℝ → ℂ}
    (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ)
    (hη : Continuous η) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀)
    (hr : ∀ k < n, 0 ≤ r k)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (h0 : Θ 0 ⊆ cellVertices ε η (closedBall 0 R₀))
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hdiam : ∀ k ≤ n, ∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D)
    (hmargin : ((∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D)) + R₀ + r n < ρ)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite) :
    (cellVertices ε η (thickening (r n) (fillCells ε η (Θ n)))).Finite := by
  have hclosure := fill_iterated_shells_closure_subset_ball Θ r n hη hD hR₀ hr hadj h0
    hstep hdiam (R := ρ - r n) (by linarith)
  have hfill : fillCells ε η (Θ n) ⊆ ball 0 (ρ - r n) := by
    intro z hz
    apply hclosure
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨a, Or.inl ha, hza⟩
  exact finite_cellVertices_thickening_fill_of_ball hfill (by linarith) hfin

/-- When adjacent cells meet, every cell in the graph closure of a shell
whose filled cells lie in the ambient ball also meets that ball. -/
theorem shell_closure_subset_ambient
    {m : ℤ → ℤ → ℕ} {ε ρ R : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ}
    (hε : 0 ≤ ε) (hΘ : fillCells ε η Θ ⊆ ball 0 R) (hR : R ≤ ρ)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty) :
    vClosure m Θ ⊆ cellVertices ε η (ball 0 ρ) := by
  intro b hb
  rcases hb with hb | ⟨_, a, ha, hab⟩
  · refine ⟨vertexPoint ε η b, vertexPoint_mem_own_cell hε η b, ?_⟩
    exact ball_subset_ball hR (hΘ (mem_iUnion₂.mpr ⟨b, hb, vertexPoint_mem_own_cell hε η b⟩))
  · obtain ⟨z, hza, hzb⟩ := hadj a b hab
    exact ⟨z, hzb, ball_subset_ball hR (hΘ (mem_iUnion₂.mpr ⟨a, ha, hza⟩))⟩

/-- The same ambient cell-size estimate bounds cells in every graph closure
whose underlying filled shell lies in the ambient ball. -/
theorem iterated_shell_closure_diameters_of_ambient
    {m : ℤ → ℤ → ℕ} {ε ρ D : ℝ} {η : ℝ → ℂ}
    (Θ : ℕ → Set ℤ) (n : ℕ) (hε : 0 ≤ ε)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hfill : ∀ k ≤ n, fillCells ε η (Θ k) ⊆ ball 0 ρ)
    (hsize : ∀ a ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η a) ≤ D) :
    ∀ k ≤ n, ∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D := by
  intro k hk a ha
  exact hsize a (shell_closure_subset_ambient hε (hfill k hk) le_rfl hadj ha)

/-- A strict cumulative budget lets the ambient cell-size estimate propagate
through every shell and its graph closure. -/
theorem iterated_shell_geometry_of_ambient
    {m : ℤ → ℤ → ℕ} {ε ρ D R₀ : ℝ} {η : ℝ → ℂ}
    (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ)
    (hε : 0 ≤ ε) (hη : Continuous η) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀)
    (hr : ∀ k < n, 0 ≤ r k)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (h0 : Θ 0 ⊆ cellVertices ε η (closedBall 0 R₀))
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hbudget : ∀ k ≤ n,
      ((∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D)) + R₀ < ρ)
    (hsize : ∀ a ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η a) ≤ D) :
    (∀ k ≤ n, fillCells ε η (Θ k) ⊆ ball 0 ρ) ∧
      (∀ k ≤ n, ∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D) := by
  have hgeom : ∀ k ≤ n, (fillCells ε η (Θ k) ⊆ ball 0 ρ) ∧
      (∀ j ≤ k, ∀ a ∈ vClosure m (Θ j), diam (cell ε η a) ≤ D) := by
    intro k hk
    induction k with
    | zero =>
      have hzero : D + R₀ < ρ := by
        have h := hbudget 0 (by omega)
        simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero] at h
        linarith
      have hdiam0 : ∀ a ∈ Θ 0, diam (cell ε η a) ≤ D := by
        intro a ha
        apply hsize a
        exact cellVertices_mono (closedBall_subset_ball (by linarith)) (h0 ha)
      have hfill0 : fillCells ε η (Θ 0) ⊆ ball 0 ρ := by
        have h := fillCells_subset_cthickening_of_meeting hη h0 hdiam0
        rw [cthickening_closedBall hD hR₀] at h
        exact h.trans (closedBall_subset_ball hzero)
      refine ⟨hfill0, ?_⟩
      intro j hj a ha
      have hj0 : j = 0 := by omega
      subst j
      exact hsize a (shell_closure_subset_ambient hε hfill0 le_rfl hadj ha)
    | succ k ih =>
      obtain ⟨_, hdiam⟩ := ih (by omega)
      have hmargin : ((∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D)) + R₀ <
          ρ - r k - D := by
        have h := hbudget (k + 1) hk
        rw [Finset.sum_range_succ, Nat.cast_succ] at h
        linarith
      have hprev := fill_iterated_shells_closure_subset_ball Θ r k hη hD hR₀
        (fun j hj => hr j (by omega)) hadj h0 (fun j hj => hstep j (by omega)) hdiam hmargin
      have hprev' : fillCells ε η (Θ k) ⊆ ball 0 (ρ - r k - D) := by
        intro z hz
        apply hprev
        obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
        exact mem_iUnion₂.mpr ⟨a, Or.inl ha, hza⟩
      have hnextambient : Θ (k + 1) ⊆ cellVertices ε η (ball 0 ρ) := by
        rw [hstep k (by omega)]
        apply cellVertices_mono
        exact (thickening_subset_of_subset (r k) hprev').trans
          ((Metric.thickening_ball 0 (r k) (ρ - r k - D)).trans
            (ball_subset_ball (by linarith)))
      have hnextdiam : ∀ a ∈ Θ (k + 1), diam (cell ε η a) ≤ D :=
        fun a ha => hsize a (hnextambient ha)
      have hnextfill : fillCells ε η (Θ (k + 1)) ⊆ ball 0 ρ := by
        have h := fillCells_subset_ball_of_thickened_shell (s := 0) hη hprev'
          (by rw [hstep k (by omega)]) hnextdiam (by linarith : ρ - r k - D + r k + D + 0 ≤ ρ)
        simpa using h
      refine ⟨hnextfill, ?_⟩
      intro j hj a ha
      by_cases hjk : j ≤ k
      · exact hdiam j hjk a ha
      · have hjeq : j = k + 1 := by omega
        subst j
        exact hsize a (shell_closure_subset_ambient hε hnextfill le_rfl hadj ha)
  refine ⟨fun k hk => (hgeom k hk).1, ?_⟩
  exact (hgeom n le_rfl).2

/-- Since radii and cell-diameter errors are nonnegative, the final budget
controls the geometry of every preceding shell. -/
theorem iterated_shell_geometry_of_total_budget
    {m : ℤ → ℤ → ℕ} {ε ρ D R₀ : ℝ} {η : ℝ → ℂ}
    (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ)
    (hε : 0 ≤ ε) (hη : Continuous η) (hD : 0 ≤ D) (hR₀ : 0 ≤ R₀)
    (hr : ∀ k < n, 0 ≤ r k)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (h0 : Θ 0 ⊆ cellVertices ε η (closedBall 0 R₀))
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hbudget : ((∑ j ∈ Finset.range n, r j) + ((n : ℝ) + 1) * (2 * D)) + R₀ < ρ)
    (hsize : ∀ a ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η a) ≤ D) :
    (∀ k ≤ n, fillCells ε η (Θ k) ⊆ ball 0 ρ) ∧
      (∀ k ≤ n, ∀ a ∈ vClosure m (Θ k), diam (cell ε η a) ≤ D) := by
  apply iterated_shell_geometry_of_ambient Θ r n hε hη hD hR₀ hr hadj h0 hstep _ hsize
  intro k hk
  have hsum : (∑ j ∈ Finset.range k, r j) ≤ ∑ j ∈ Finset.range n, r j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
    intro j hj _
    exact hr j (Finset.mem_range.mp hj)
  have hcast : (k : ℝ) ≤ n := by exact_mod_cast hk
  nlinarith

/-- One ambient cell-size bound supplies the diameter and finiteness inputs
for the current shell, its intermediate expansion, and the stopped cluster. -/
theorem shell_geometric_inputs_of_ambient
    {m : ℤ → ℤ → ℕ} {ε ρ t r R D : ℝ} {η : ℝ → ℂ} {Θ : Set ℤ}
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (hΘ : fillCells ε η Θ ⊆ ball 0 R)
    (hmargin : r + R ≤ ρ)
    (hfin : (cellVertices ε η (closedBall 0 ρ)).Finite)
    (hsize : ∀ a ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η a) ≤ D) :
    Θ ⊆ cellVertices ε η (ball 0 ρ) ∧ Θ.Finite ∧
    (cellVertices ε η (thickening r (fillCells ε η Θ))).Finite ∧
    (∀ a ∈ cellVertices ε η (thickening (r / 4) (fillCells ε η Θ)),
      diam (cell ε η a) ≤ D) ∧
    (matedDiscreteCluster m ε η ρ t).Finite ∧
    (∀ a ∈ matedDiscreteCluster m ε η ρ t, diam (cell ε η a) ≤ D) := by
  have hR : R ≤ ρ := by linarith
  have hΘsub : Θ ⊆ cellVertices ε η (ball 0 ρ) := by
    intro a ha
    refine ⟨vertexPoint ε η a, vertexPoint_mem_own_cell hε η a, ?_⟩
    exact ball_subset_ball hR (hΘ (mem_iUnion₂.mpr ⟨a, ha, vertexPoint_mem_own_cell hε η a⟩))
  have hclust : matedDiscreteCluster m ε η ρ t ⊆ cellVertices ε η (ball 0 ρ) := by
    intro a ha
    exact ha.1
  have hambientfin : (cellVertices ε η (ball 0 ρ)).Finite :=
    hfin.subset (cellVertices_mono ball_subset_closedBall)
  refine ⟨hΘsub, hambientfin.subset hΘsub,
    finite_cellVertices_thickening_fill_of_ball hΘ hmargin hfin, ?_,
    hambientfin.subset hclust, fun a ha => hsize a (hclust ha)⟩
  intro a ha
  apply hsize a
  apply cellVertices_mono _ ha
  exact (thickening_subset_of_subset (r / 4) hΘ).trans
    ((Metric.thickening_ball 0 (r / 4) R).trans (ball_subset_ball (by linarith)))

end MatedCRT.Sec7
