import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellContraction
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.InitialOdometer

/-! The initial graph boundary lies near the continuum frontier.
-/

namespace MatedCRT.Sec7

open Set Metric

/-- If adjacent cells meet, every cell on the graph boundary of the cells
meeting an open set lies within two cell diameters of its frontier. -/
theorem boundary_cells_subset_cthickening_frontier
    {m : ℤ → ℤ → ℕ} {ε D : ℝ} {η : ℝ → ℂ} {O : Set ℂ}
    (hη : Continuous η) (hO : IsOpen O)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ a ∈ vClosure m (cellVertices ε η O), diam (cell ε η a) ≤ D)
    {b : ℤ} (hb : b ∈ vBoundary m (cellVertices ε η O)) :
    cell ε η b ⊆ cthickening (2 * D) (frontier O) := by
  obtain ⟨hbout, a, ha, hab⟩ := hb
  obtain ⟨y, hya, hyb⟩ := hadj a b hab
  have haF : a ∈ cellVertices ε η (frontier O) := by
    by_contra haF
    have hyO := cell_subset_open_of_meets_avoids_frontier hη hO ha haF hya
    exact hbout ⟨y, hyb, hyO⟩
  obtain ⟨w, hwa, hwF⟩ := haF
  intro x hxb
  have hbdA : Bornology.IsBounded (cell ε η a) := (isCompact_Icc.image hη).isBounded
  have hbdB : Bornology.IsBounded (cell ε η b) := (isCompact_Icc.image hη).isBounded
  have hD1 := (dist_le_diam_of_mem hbdA hya hwa).trans (hdiam a (Or.inl ha))
  have hD2 := (dist_le_diam_of_mem hbdB hxb hyb).trans
    (hdiam b (Or.inr ⟨hbout, a, ha, hab⟩))
  apply mem_cthickening_of_dist_le x w (2 * D) (frontier O) hwF
  linarith [dist_triangle x y w]

/-- A continuous function vanishing on a compact frontier is uniformly small
on a sufficiently thin neighborhood contained in its domain. -/
theorem exists_frontier_neighborhood_of_continuous_zero
    {O U : Set ℂ} {f : ℂ → ℝ} {q : ℝ}
    (hcompact : IsCompact (frontier O)) (hU : IsOpen U)
    (hfront : frontier O ⊆ U) (hf : ContinuousOn f U)
    (hzero : ∀ x ∈ frontier O, f x = 0) (hq : 0 < q) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ cthickening d (frontier O), x ∈ U ∧ f x < q := by
  have hopen : IsOpen (U ∩ f ⁻¹' Iio q) := hf.isOpen_inter_preimage hU isOpen_Iio
  have hsub : frontier O ⊆ U ∩ f ⁻¹' Iio q := by
    intro x hx
    exact ⟨hfront hx, by simpa [hzero x hx] using hq⟩
  obtain ⟨d, hd, hdn⟩ := hcompact.exists_cthickening_subset_open hopen hsub
  exact ⟨d, hd, fun x hx => hdn hx⟩

/-- A cellwise mesh-normalized estimate controls the initial boundary
maximum once the continuum gap is small near the frontier. -/
theorem initial_boundary_iSup_le_of_frontier_gap
    {m : ℤ → ℤ → ℕ} {ε D B q : ℝ} {η : ℝ → ℂ} {O K : Set ℂ}
    {f : ℂ → ℝ} {u : ℤ → ℝ}
    (hε : 0 < ε) (hB : 0 ≤ B) (hη : Continuous η) (hO : IsOpen O)
    (hadj : ∀ a b, m a b ≠ 0 → (cell ε η a ∩ cell ε η b).Nonempty)
    (hdiam : ∀ a ∈ vClosure m (cellVertices ε η O), diam (cell ε η a) ≤ D)
    (hK : cthickening (2 * D) (frontier O) ⊆ K)
    (hgap : ∀ x ∈ cthickening (2 * D) (frontier O), f x ≤ q)
    (hbound : ∀ a : ℤ, cell ε η a ⊆ K →
      (∀ x ∈ cell ε η a, f x ≤ q) → ε * u a ≤ B) :
    ε * (⨆ a : vBoundary m (cellVertices ε η O), u a) ≤ B := by
  apply mesh_boundary_iSup_le hε hB
  intro a ha
  have hcell := boundary_cells_subset_cthickening_frontier hη hO hadj hdiam ha
  exact hbound a (hcell.trans hK) (fun x hx => hgap x (hcell hx))

end MatedCRT.Sec7
