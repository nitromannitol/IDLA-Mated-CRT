import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExitTimeSolutionBound
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ClosedDomainGeometry

/-! Expected-exit-time comparison for the Dirichlet boundary barrier. -/

namespace MatedCRT

open Set Metric Filter Topology

/-- On disk cells, the difference between a Poisson solution and a harmonic
function with the same boundary values is bounded by the source bound times
the ordinary expected exit time. This is the discrete barrier used in Step 3
of the proof of Lemma 3.5 (corrected paper lines 1575–1605). -/
theorem abs_sub_harmonic_le_expectedExitTime
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 < ε) (hr : 0 < r) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsucc : ∀ k, m k (k + 1) ≠ 0)
    (u h : ℤ → ℝ) {C : ℝ}
    (hlap : ∀ a ∈ interiorCellVertices ε η (ball z r), |matedLaplacian m u a| ≤ C)
    (hharm : ∀ a ∈ interiorCellVertices ε η (ball z r), matedLaplacian m h a = 0)
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r), u b = h b)
    (hQfin : ∀ a ∈ interiorCellVertices ε η (ball z r),
      expectedExitTime m (interiorCellVertices ε η (ball z r)) a ≠ ⊤) :
    ∀ a ∈ cellVertices ε η (ball z r),
      |u a - h a| ≤ C * (expectedExitTime m (interiorCellVertices ε η (ball z r)) a).toReal := by
  have hlf := Tightness.isLocallyFiniteMult_of_cells hη hp hε hadj
  have h := abs_solution_le_boundary_add_expectedExitTime hε hr hη hp hadj hsucc
    (fun a => u a - h a) (C := C) (M := 0) ?_ ?_ hQfin
  · intro a ha
    simpa using h a ha
  · intro a ha
    change |mLaplacian m (fun a => u a - h a) a| ≤ C
    rw [mLaplacian_sub_of_locallyFinite hlf, show mLaplacian m h a = 0 from hharm a ha, sub_zero]
    exact hlap a ha
  · intro b hb
    simp [hbd b hb]

/-- The same barrier holds on cells meeting the closed disk. -/
theorem abs_sub_harmonic_le_expectedExitTime_closedBall
    {m : ℤ → ℤ → ℕ} {ε r : ℝ} {η : ℝ → ℂ} {z : ℂ}
    (hε : 0 < ε) (hr : 0 < r) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsucc : ∀ k, m k (k + 1) ≠ 0)
    (u h : ℤ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hlap : ∀ a ∈ interiorCellVertices ε η (ball z r), |matedLaplacian m u a| ≤ C)
    (hharm : ∀ a ∈ interiorCellVertices ε η (ball z r), matedLaplacian m h a = 0)
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r), u b = h b)
    (hQfin : ∀ a ∈ interiorCellVertices ε η (ball z r),
      expectedExitTime m (interiorCellVertices ε η (ball z r)) a ≠ ⊤) :
    ∀ a ∈ cellVertices ε η (closedBall z r),
      |u a - h a| ≤ C * (expectedExitTime m (interiorCellVertices ε η (ball z r)) a).toReal := by
  intro a ha
  rcases cellVertices_closedBall_subset_interior_union_sphere hr ha with ha | ha
  · exact abs_sub_harmonic_le_expectedExitTime hε hr hη hp hadj hsucc u h hlap hharm hbd hQfin a ha.1
  · rw [hbd a ha, sub_self, abs_zero]
    exact mul_nonneg hC ENNReal.toReal_nonneg

/-- Rescaling preserves the exit-time barrier at any point whose selected cell
meets the closed disk. -/
theorem abs_rescale_sub_harmonic_le_expectedExitTime
    {m : ℤ → ℤ → ℕ} {ε r M : ℝ} {η : ℝ → ℂ} {z x : ℂ}
    (hε : 0 < ε) (hr : 0 < r) (hM : 0 ≤ M⁻¹) (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hadj : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hsucc : ∀ k, m k (k + 1) ≠ 0)
    (u h : ℤ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hlap : ∀ a ∈ interiorCellVertices ε η (ball z r), |matedLaplacian m u a| ≤ C)
    (hharm : ∀ a ∈ interiorCellVertices ε η (ball z r), matedLaplacian m h a = 0)
    (hbd : ∀ b ∈ cellVertices ε η (sphere z r), u b = h b)
    (hQfin : ∀ a ∈ interiorCellVertices ε η (ball z r),
      expectedExitTime m (interiorCellVertices ε η (ball z r)) a ≠ ⊤)
    (hx : x ∈ closedBall z r) (hcell : x ∈ cell ε η (vertexOf ε η x)) :
    |rescale M ε η u x - rescale M ε η h x| ≤
      C * (M⁻¹ * (expectedExitTime m (interiorCellVertices ε η (ball z r))
        (vertexOf ε η x)).toReal) := by
  have hbound := abs_sub_harmonic_le_expectedExitTime_closedBall hε hr hη hp hadj hsucc u h hC
    hlap hharm hbd hQfin (vertexOf ε η x) ⟨x, hcell, hx⟩
  calc
    |rescale M ε η u x - rescale M ε η h x| =
        M⁻¹ * |u (vertexOf ε η x) - h (vertexOf ε η x)| := by
          simp [rescale, ← mul_sub, abs_mul, abs_of_nonneg hM]
    _ ≤ M⁻¹ * (C * (expectedExitTime m (interiorCellVertices ε η (ball z r))
        (vertexOf ε η x)).toReal) := mul_le_mul_of_nonneg_left hbound hM
    _ = _ := by ring

end MatedCRT

#print axioms MatedCRT.abs_rescale_sub_harmonic_le_expectedExitTime
