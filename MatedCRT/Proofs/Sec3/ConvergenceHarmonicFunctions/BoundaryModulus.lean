import MatedCRT.Proofs.Sec3.DiscretePotentialTightness.EquicontinuityLemmas

/-! # Quantitative boundary-cell extension -/

namespace MatedCRT

open Filter Topology Set Metric Tightness

/-- Every cell meeting the closure has an open-domain representative; if the
original cell misses the domain then the two cells meet at a boundary point. -/
theorem closure_cell_open_representative {ε : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) {D : Set ℂ} (hD : IsOpen D)
    {a : ℤ} (ha : a ∈ cellVertices ε η (closure D)) :
    ∃ b ∈ cellVertices ε η D, ∃ p ∈ closure D,
      p ∈ cell ε η a ∧ p ∈ cell ε η b ∧
      (a ∉ cellVertices ε η D → p ∈ frontier D) := by
  obtain ⟨p, hpa, hpD⟩ := ha
  obtain ⟨b, hb, hpb⟩ := exists_mem_cellVertices_of_mem_closure hη hp hsurj hε hpD
  refine ⟨b, hb, p, hpD, hpa, hpb, ?_⟩
  intro haD
  rw [hD.frontier_eq]
  exact ⟨hpD, fun hp' => haD ⟨p, hpa, hp'⟩⟩

/-- Boundary Hölder data and a uniform cell-radius bound control the error
incurred when a closure cell is replaced by a cell meeting the open domain. -/
theorem closure_cell_representative_of_boundary_holder {ε d H χ : ℝ}
    {η : ℝ → ℂ} {D : Set ℂ} {u : ℤ → ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) (hH : 0 ≤ H) (hχ : 0 ≤ χ)
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hD : IsOpen D)
    (hcell : ∀ a ∈ cellVertices ε η (closure D), ∀ p ∈ cell ε η a,
      dist (vertexPoint ε η a) p ≤ d)
    (hdata : ∀ a ∈ cellVertices ε η (frontier D),
      ∀ b ∈ cellVertices ε η (frontier D),
      |u a - u b| ≤ H * max ε (dist (vertexPoint ε η a) (vertexPoint ε η b)) ^ χ)
    {a : ℤ} (ha : a ∈ cellVertices ε η (closure D)) :
    ∃ a' ∈ cellVertices ε η D,
      dist (vertexPoint ε η a) (vertexPoint ε η a') ≤ 2 * d ∧
      |u a - u a'| ≤ H * max ε (2 * d) ^ χ := by
  by_cases haD : a ∈ cellVertices ε η D
  · refine ⟨a, haD, ?_, ?_⟩
    · simpa using (show 0 ≤ 2 * d by linarith)
    · simp only [sub_self, abs_zero]
      exact mul_nonneg hH (Real.rpow_nonneg (le_trans hε.le (le_max_left _ _)) _)
  · obtain ⟨a', ha'D, p, hpD, hpa, hpa', hpf⟩ :=
      closure_cell_open_representative hε hη hp hsurj hD ha
    have ha'cl : a' ∈ cellVertices ε η (closure D) := ⟨p, hpa', hpD⟩
    have hdist : dist (vertexPoint ε η a) (vertexPoint ε η a') ≤ 2 * d := by
      have ht := dist_triangle (vertexPoint ε η a) p (vertexPoint ε η a')
      have hc := hcell a' ha'cl p hpa'
      rw [dist_comm] at hc
      linarith [hcell a ha p hpa]
    refine ⟨a', ha'D, hdist, ?_⟩
    have hboundary := hdata a ⟨p, hpa, hpf haD⟩ a' ⟨p, hpa', hpf haD⟩
    exact hboundary.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (le_trans hε.le (le_max_left _ _))
        (max_le_max_left ε hdist) hχ) hH)

/-- A bound on representatives and a modulus on open-domain cells give a
quantitative modulus on all closure cells. The boundary estimate supplies the
representative error. -/
theorem closure_cell_modulus_of_representatives {ε d H K χ ξ : ℝ}
    {η : ℝ → ℂ} {D : Set ℂ} {u : ℤ → ℝ}
    (hε : 0 ≤ ε) (hK : 0 ≤ K) (hξ : 0 ≤ ξ)
    (hrep : ∀ a ∈ cellVertices ε η (closure D),
      ∃ a' ∈ cellVertices ε η D,
        dist (vertexPoint ε η a) (vertexPoint ε η a') ≤ 2 * d ∧
        |u a - u a'| ≤ H * max ε (2 * d) ^ χ)
    (hmod : ∀ a ∈ cellVertices ε η D, ∀ b ∈ cellVertices ε η D,
      |u a - u b| ≤ K * max ε (dist (vertexPoint ε η a) (vertexPoint ε η b)) ^ ξ)
    {a b : ℤ} (ha : a ∈ cellVertices ε η (closure D))
    (hb : b ∈ cellVertices ε η (closure D)) :
    |u a - u b| ≤ 2 * (H * max ε (2 * d) ^ χ) +
      K * max ε (dist (vertexPoint ε η a) (vertexPoint ε η b) + 4 * d) ^ ξ := by
  obtain ⟨a', ha', hda, hua⟩ := hrep a ha
  obtain ⟨b', hb', hdb, hub⟩ := hrep b hb
  have hdist : dist (vertexPoint ε η a') (vertexPoint ε η b') ≤
      dist (vertexPoint ε η a) (vertexPoint ε η b) + 4 * d := by
    have h1 := dist_triangle (vertexPoint ε η a') (vertexPoint ε η a) (vertexPoint ε η b')
    have h2 := dist_triangle (vertexPoint ε η a) (vertexPoint ε η b) (vertexPoint ε η b')
    have hda' : dist (vertexPoint ε η a') (vertexPoint ε η a) ≤ 2 * d := by
      simpa only [dist_comm] using hda
    linarith
  have hpow := Real.rpow_le_rpow (le_trans hε (le_max_left _ _))
    (max_le_max_left ε hdist) hξ
  have hmid := (hmod a' ha' b' hb').trans (mul_le_mul_of_nonneg_left hpow hK)
  have h1 := abs_sub_le (u a) (u a') (u b)
  have h2 := abs_sub_le (u a') (u b') (u b)
  rw [abs_sub_comm (u b') (u b)] at h2
  linarith

/-- Boundary and interior Hölder estimates extend quantitatively to the
closure, with an error controlled by the largest cell radius. -/
theorem closure_cell_modulus_of_boundary_holder {ε d H K χ ξ : ℝ}
    {η : ℝ → ℂ} {D : Set ℂ} {u : ℤ → ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hχ : 0 ≤ χ) (hξ : 0 ≤ ξ)
    (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) (hD : IsOpen D)
    (hcell : ∀ a ∈ cellVertices ε η (closure D), ∀ p ∈ cell ε η a,
      dist (vertexPoint ε η a) p ≤ d)
    (hdata : ∀ a ∈ cellVertices ε η (frontier D),
      ∀ b ∈ cellVertices ε η (frontier D),
      |u a - u b| ≤ H * max ε (dist (vertexPoint ε η a) (vertexPoint ε η b)) ^ χ)
    (hmod : ∀ a ∈ cellVertices ε η D, ∀ b ∈ cellVertices ε η D,
      |u a - u b| ≤ K * max ε (dist (vertexPoint ε η a) (vertexPoint ε η b)) ^ ξ)
    {a b : ℤ} (ha : a ∈ cellVertices ε η (closure D))
    (hb : b ∈ cellVertices ε η (closure D)) :
    |u a - u b| ≤ 2 * (H * max ε (2 * d) ^ χ) +
      K * max ε (dist (vertexPoint ε η a) (vertexPoint ε η b) + 4 * d) ^ ξ := by
  apply closure_cell_modulus_of_representatives hε.le hK hξ _ hmod ha hb
  intro c hc
  exact closure_cell_representative_of_boundary_holder hε hd hH hχ hη hp hsurj hD hcell hdata hc

end MatedCRT
