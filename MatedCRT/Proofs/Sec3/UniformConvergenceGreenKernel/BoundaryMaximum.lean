import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.HarmonicAwayFromPole
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import MatedCRT.Proofs.Sec7.OdometerBoundMass.Laplacian

/-!
# Discrete Green-kernel boundary barrier

On any finite annular vertex set excluding the pole, the maximum principle bounds the
Green kernel by its values on the vertex boundary of the annulus. This is
the finite-graph part of the boundary argument in Lemma 3.3.
-/

namespace MatedCRT

open Set

/-- A bound on the vertex boundary of a pole-free subdomain propagates to that
subdomain for every scalar multiple of the Green kernel. -/
theorem scaled_greenKernel_le_of_boundary_le {m : ℤ → ℤ → ℕ} {A B : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite) (hBA : B ⊆ A)
    {o : ℤ} (ho : o ∈ A) (hoB : o ∉ B) (c M : ℝ)
    (hbound : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∉ B → c * greenKernel m A o b ≤ M) :
    ∀ b ∈ B, c * greenKernel m A o b ≤ M := by
  have hB : B.Finite := hA.subset hBA
  have hsub : ∀ b ∈ B, 0 ≤ lapSum hlf (fun x => c * greenKernel m A o x - M) b := by
    intro b hb
    have hne : b ≠ o := fun h => hoB (h ▸ hb)
    have hlap := greenKernelLaplacianStep m A hsymm hlf hcons hA o ho b (hBA hb)
    have hc : mLaplacian m (fun _ : ℤ => -M) b = 0 := by simp [mLaplacian]
    rw [← mLaplacian_mul_mdeg hlf]
    have heq : (fun x => c * greenKernel m A o x - M) =
        (fun x => c * greenKernel m A o x + -M) := by funext x; ring
    rw [heq, mLaplacian_add_of_locallyFinite hlf, mLaplacian_const_mul, hlap, hc]
    simp [hne]
  have h := nonpos_of_lapSum_nonneg hlf hB (escape_of_adjacent_succ hcons hB) hsub
    (fun a ha b hab hb => sub_nonpos.mpr (hbound a ha b hab hb))
  intro b hb
  exact sub_nonpos.mp (h b hb)

/-- A bound on a set containing the pole extends to the whole domain. This is
useful when the set is an inner region and the complement is a boundary layer. -/
theorem scaled_greenKernel_le_of_inner_le {m : ℤ → ℤ → ℕ} {A T : Set ℤ}
    (hsymm : ∀ a b, m a b = m b a) (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ a, m a (a + 1) ≠ 0) (hA : A.Finite)
    {o : ℤ} (ho : o ∈ A) (hoT : o ∈ T) (c M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ b ∈ A ∩ T, c * greenKernel m A o b ≤ M) :
    ∀ b ∈ A, c * greenKernel m A o b ≤ M := by
  have houter := scaled_greenKernel_le_of_boundary_le hsymm hlf hcons hA
    (show A \ T ⊆ A from sdiff_subset) ho (show o ∉ A \ T from fun h => h.2 hoT) c M
    (by
      intro a ha b hab hb
      by_cases hbA : b ∈ A
      · exact hbound b ⟨hbA, by simpa [hbA] using hb⟩
      · simpa [greenKernel_eq_zero_of_not_mem_right m o hbA] using hM)
  intro b hb
  by_cases hbT : b ∈ T
  · exact hbound b ⟨hb, hbT⟩
  · exact houter b ⟨hb, hbT⟩

end MatedCRT
