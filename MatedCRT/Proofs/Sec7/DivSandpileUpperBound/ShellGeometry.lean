import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.CrudeCells
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Stopping
import Mathlib.Tactic

/-! Euclidean growth of the filled graph closures in the shell iteration. -/

namespace MatedCRT.Sec7

open Set Metric

/-- Cells meeting a set and having diameter at most `D` fill at most its closed
`D`-neighborhood. -/
theorem fillCells_subset_cthickening_of_meeting
    {ε D : ℝ} {η : ℝ → ℂ} {A : Set ℤ} {X : Set ℂ}
    (hη : Continuous η) (hA : A ⊆ cellVertices ε η X)
    (hdiam : ∀ a ∈ A, diam (cell ε η a) ≤ D) :
    fillCells ε η A ⊆ cthickening D X := by
  intro z hz
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
  obtain ⟨y, hya, hyX⟩ := hA ha
  have hbdd : Bornology.IsBounded (cell ε η a) := (isCompact_Icc.image hη).isBounded
  exact mem_cthickening_of_dist_le z y D X hyX
    ((dist_le_diam_of_mem hbdd hza hya).trans (hdiam a ha))

/-- One shell adds its Euclidean radius and at most two cell diameters to the
filled graph closure. -/
theorem fill_shell_closure_subset_cthickening
    {m : ℤ → ℤ → ℕ} {ε r D : ℝ} {η : ℝ → ℂ} {A Θ : Set ℤ}
    (hη : Continuous η) (hr : 0 ≤ r) (hD : 0 ≤ D)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hA : A ⊆ cellVertices ε η (thickening r (fillCells ε η (vClosure m Θ))))
    (hdiam : ∀ a ∈ vClosure m A, diam (cell ε η a) ≤ D) :
    fillCells ε η (vClosure m A) ⊆ cthickening (r + 2 * D) (fillCells ε η (vClosure m Θ)) := by
  have hfill := fillCells_subset_cthickening_of_meeting hη hA (fun a ha => hdiam a (Or.inl ha))
  have hA' : fillCells ε η A ⊆ cthickening (D + r) (fillCells ε η (vClosure m Θ)) :=
    hfill.trans ((cthickening_subset_of_subset D (thickening_subset_cthickening r _)).trans
      (cthickening_cthickening_subset hD hr _))
  have hcl := fill_closure_subset_cthickening m A ε D η hη hadj hdiam
  have hsum := hcl.trans ((cthickening_subset_of_subset D hA').trans
    (cthickening_cthickening_subset hD (by linarith : 0 ≤ D + r) _))
  have heq : D + (D + r) = r + 2 * D := by ring
  rw [heq] at hsum
  exact hsum

/-- Filling the initial graph closure of cells which meet `X` adds at most two
cell diameters to `X`. -/
theorem fill_initial_closure_subset_cthickening
    {m : ℤ → ℤ → ℕ} {ε D : ℝ} {η : ℝ → ℂ} {A : Set ℤ} {X : Set ℂ}
    (hη : Continuous η) (hD : 0 ≤ D)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hA : A ⊆ cellVertices ε η X)
    (hdiam : ∀ a ∈ vClosure m A, diam (cell ε η a) ≤ D) :
    fillCells ε η (vClosure m A) ⊆ cthickening (2 * D) X := by
  have hfill := fillCells_subset_cthickening_of_meeting hη hA (fun a ha => hdiam a (Or.inl ha))
  have hcl := fill_closure_subset_cthickening m A ε D η hη hadj hdiam
  have hsum := hcl.trans ((cthickening_subset_of_subset D hfill).trans
    (cthickening_cthickening_subset hD hD X))
  have heq : D + D = 2 * D := by ring
  rw [heq] at hsum
  exact hsum

/-- Every vertex in the current set belongs to the next set of cells meeting a
positive-radius neighborhood of its filled closure. -/
theorem subset_cellVertices_thickening_fill_closure
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {A : Set ℤ}
    (hε : 0 ≤ ε) (hr : 0 < r) :
    A ⊆ cellVertices ε η (thickening r (fillCells ε η (vClosure m A))) := by
  intro a ha
  have hz : vertexPoint ε η a ∈ cell ε η a := vertexPoint_mem_own_cell hε η a
  have hfill : vertexPoint ε η a ∈ fillCells ε η (vClosure m A) :=
    mem_iUnion₂.mpr ⟨a, Or.inl ha, hz⟩
  exact ⟨vertexPoint ε η a, hz, self_subset_thickening hr _ hfill⟩

/-- The shell expansion preserves the origin, as required by the final crude bound. -/
theorem zero_mem_iterated_shells
    {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} (Θ : ℕ → Set ℤ) (r : ℕ → ℝ)
    (hε : 0 ≤ ε) (hr : ∀ k, 0 < r k) (hzero : (0 : ℤ) ∈ Θ 0)
    (hstep : ∀ k, cellVertices ε η (thickening (r k) (fillCells ε η (vClosure m (Θ k)))) ⊆ Θ (k + 1))
    (n : ℕ) : (0 : ℤ) ∈ Θ n := by
  induction n with
  | zero => exact hzero
  | succ n ih => exact hstep n (subset_cellVertices_thickening_fill_closure hε (hr n) ih)

/-- Closed-neighborhood bounds accumulate by adding their nonnegative radii. -/
theorem iterated_cthickening_subset {E : ℕ → Set ℂ} {X : Set ℂ}
    {d : ℝ} {s : ℕ → ℝ} (hd : 0 ≤ d) (hs : ∀ k, 0 ≤ s k)
    (h0 : E 0 ⊆ cthickening d X)
    (hstep : ∀ k, E (k + 1) ⊆ cthickening (s k) (E k)) (n : ℕ) :
    E n ⊆ cthickening (d + ∑ k ∈ Finset.range n, s k) X := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hsum : 0 ≤ d + ∑ k ∈ Finset.range n, s k := by
      exact add_nonneg hd (Finset.sum_nonneg fun k _ => hs k)
    have hnext := (hstep n).trans ((cthickening_subset_of_subset (s n) ih).trans
      (cthickening_cthickening_subset (hs n) hsum X))
    have heq : s n + (d + ∑ k ∈ Finset.range n, s k) =
        d + ∑ k ∈ Finset.range (n + 1), s k := by
      rw [Finset.sum_range_succ]
      ring
    rwa [heq] at hnext

/-- The filled closure of each shell lies within the sum of the chosen radii,
plus two cell diameters per shell and two for the initial closure. -/
theorem fill_iterated_shells_subset_cthickening
    {m : ℤ → ℤ → ℕ} {ε D : ℝ} {η : ℝ → ℂ} {X : Set ℂ}
    (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (n : ℕ) (hη : Continuous η) (hD : 0 ≤ D)
    (hr : ∀ k < n, 0 ≤ r k)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (h0 : Θ 0 ⊆ cellVertices ε η X)
    (hstep : ∀ k < n, Θ (k + 1) ⊆ cellVertices ε η
      (thickening (r k) (fillCells ε η (vClosure m (Θ k)))))
    (hdiam : ∀ k ≤ n, ∀ a, a ∈ vClosure m (Θ k) → diam (cell ε η a) ≤ D) :
    fillCells ε η (vClosure m (Θ n)) ⊆
      cthickening ((∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D)) X := by
  have hlocal : ∀ k ≤ n, fillCells ε η (vClosure m (Θ k)) ⊆
      cthickening ((∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D)) X := by
    intro k hk
    induction k with
    | zero =>
      simpa using fill_initial_closure_subset_cthickening hη hD hadj h0 (hdiam 0 (by omega))
    | succ k ih =>
      have hprev := ih (by omega)
      have hsum : 0 ≤ (∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D) := by
        apply add_nonneg
        · exact Finset.sum_nonneg fun j hj => hr j (by have := Finset.mem_range.mp hj; omega)
        · positivity
      have hnext := fill_shell_closure_subset_cthickening hη (hr k (by omega)) hD hadj
        (hstep k (by omega)) (hdiam (k + 1) hk)
      have hnext' := hnext.trans ((cthickening_subset_of_subset _ hprev).trans
        (cthickening_cthickening_subset (by have := hr k (by omega); positivity) hsum X))
      have heq : (r k + 2 * D) + ((∑ j ∈ Finset.range k, r j) + ((k : ℝ) + 1) * (2 * D)) =
          (∑ j ∈ Finset.range (k + 1), r j) + (((k + 1 : ℕ) : ℝ) + 1) * (2 * D) := by
        rw [Finset.sum_range_succ, Nat.cast_succ]
        ring
      rwa [heq] at hnext'
  exact hlocal n le_rfl

/-- A shell with a small boundary odometer and a sufficiently small cumulative
radius is an intermediate set suitable for the final crude-path estimate. -/
theorem exists_localized_intermediate_shell
    {m : ℤ → ℤ → ℕ} {ε D δ M : ℝ} {η : ℝ → ℂ} {X : Set ℂ}
    (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (u : ℤ → ℝ) (n : ℕ)
    (hε : 0 ≤ ε) (hη : Continuous η) (hD : 0 ≤ D) (hr : ∀ k < n, 0 < r k)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hzero : (0 : ℤ) ∈ Θ 0) (h0 : Θ 0 ⊆ cellVertices ε η X)
    (hstep : ∀ k < n, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hdiam : ∀ k ≤ n, ∀ a, a ∈ vClosure m (Θ k) → diam (cell ε η a) ≤ D)
    (hbound : ∀ a ∈ vBoundary m (Θ n), u a ≤ M)
    (hbudget : (∑ k ∈ Finset.range n, r k) + ((n : ℝ) + 1) * (2 * D) ≤ δ) :
    ∃ T : Set ℤ, (0 : ℤ) ∈ T ∧ (∀ a ∈ vBoundary m T, u a ≤ M) ∧
      fillCells ε η (vClosure m T) ⊆ outerNbhd δ X := by
  have hzero' : (0 : ℤ) ∈ Θ n := by
    have hzero'' : ∀ k ≤ n, (0 : ℤ) ∈ Θ k := by
      intro k hk
      induction k with
      | zero => exact hzero
      | succ k ih =>
        rw [hstep k (by omega)]
        have hmem := ih (by omega)
        have hz := vertexPoint_mem_own_cell hε η 0
        exact ⟨vertexPoint ε η 0, hz,
          self_subset_thickening (hr k (by omega)) _ (mem_iUnion₂.mpr ⟨0, hmem, hz⟩)⟩
    exact hzero'' n le_rfl
  have hstep' : ∀ k < n, Θ (k + 1) ⊆ cellVertices ε η
      (thickening (r k) (fillCells ε η (vClosure m (Θ k)))) := by
    intro k hk a ha
    rw [hstep k hk] at ha
    obtain ⟨z, hzc, hz⟩ := ha
    refine ⟨z, hzc, thickening_subset_of_subset (r k) ?_ hz⟩
    intro w hw
    obtain ⟨b, hb, hwb⟩ := mem_iUnion₂.mp hw
    exact mem_iUnion₂.mpr ⟨b, Or.inl hb, hwb⟩
  have hfill := fill_iterated_shells_subset_cthickening Θ r n hη hD (fun k hk => (hr k hk).le)
    hadj h0 hstep' hdiam
  refine ⟨Θ n, hzero', hbound, ?_⟩
  exact hfill.trans (cthickening_mono hbudget X)

/-- A fixed-factor contraction and its radius budget produce a localized shell
whose boundary odometer is below the stopping threshold. -/
theorem localized_shell_of_geometric_iteration
    {m : ℤ → ℤ → ℕ} {η : ℝ → ℂ} {X : Set ℂ}
    (Θ : ℕ → Set ℤ) (r O : ℕ → ℝ) (u : ℤ → ℝ)
    (ε q p C ω A R D δ : ℝ)
    (hε : 0 < ε) (hη : Continuous η) (hq : 0 < q) (hq1 : q < 1)
    (hp : 0 ≤ p) (hp1 : p < 1) (hC : 0 < C) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hzero : (0 : ℤ) ∈ Θ 0) (h0 : Θ 0 ⊆ cellVertices ε η X)
    (hrpos : ∀ k, 0 < r k)
    (hshell : ∀ k, Θ (k + 1) = cellVertices ε η
      (thickening (r k) (fillCells ε η (Θ k))))
    (hdiam : ∀ k a, a ∈ vClosure m (Θ k) → diam (cell ε η a) ≤ D)
    (hmaximum : ∀ k a, a ∈ vBoundary m (Θ k) → u a ≤ O k)
    (hinitial : ε ^ (-ω) < O 0) (hupper : O 0 ≤ C / ε)
    (hcontract : ∀ k, ε ^ (-ω) < O k → O (k + 1) ≤ q * O k)
    (hradius : ∀ k, (∀ j < k, ε ^ (-ω) < O j) → r k ≤ max (A * p ^ k) R)
    (hbudget : let L := (Real.log C + (1 - ω) * Real.log ε⁻¹) / (-Real.log q) + 1
      A / (1 - p) + L * R + (L + 1) * (2 * D) ≤ δ) :
    ∃ T : Set ℤ, (0 : ℤ) ∈ T ∧
      (∀ a ∈ vBoundary m T, u a ≤ ε ^ (-ω)) ∧
      fillCells ε η (vClosure m T) ⊆ outerNbhd δ X := by
  obtain ⟨n, hn, hsum⟩ := exists_shell_threshold_with_iteration_budget O r q p C ε ω A R D δ
    hq hq1 hp hp1 hC hε hA hR hD hinitial hupper hcontract hradius hbudget
  apply exists_localized_intermediate_shell Θ r u n hε.le hη hD
    (fun k _ => hrpos k) hadj hzero h0 (fun k _ => hshell k)
    (fun k _ => hdiam k) ?_ hsum
  intro a ha
  exact (hmaximum n a ha).trans hn

end MatedCRT.Sec7
