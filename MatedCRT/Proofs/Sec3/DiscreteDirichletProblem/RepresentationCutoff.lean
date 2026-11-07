import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.EnvSigmaRepresentation

/-! # Cutoff invariance of the discrete Green representation -/

namespace MatedCRT

open Set MeasureTheory

/-- A finite-domain Green representation is unchanged when its source is
replaced on the interior and its exit data are replaced on an almost-sure
exit set. No measurability of the original data is required. -/
theorem green_representation_congr_on
    {m : ℤ → ℤ → ℕ} {A B : Set ℤ} (hA : A.Finite) {a : ℤ}
    (F q q' g g' : ℤ → ℝ)
    (hq : ∀ b ∈ A, q b = q' b)
    (hg : ∀ b ∈ B, g b = g' b)
    (hexit : ∀ᵐ x ∂srwLaw m a, vExitPosition A x ∈ B)
    (hrep : F a = (∫ x, g (vExitPosition A x) ∂srwLaw m a) -
      ∑ b ∈ hA.toFinset, q b * greenFn m A a b) :
    F a = (∫ x, g' (vExitPosition A x) ∂srwLaw m a) -
      ∑ b ∈ hA.toFinset, q' b * greenFn m A a b := by
  have hint : (∫ x, g (vExitPosition A x) ∂srwLaw m a) =
      ∫ x, g' (vExitPosition A x) ∂srwLaw m a := by
    apply integral_congr_ae
    filter_upwards [hexit] with x hx
    exact hg _ hx
  have hsum : (∑ b ∈ hA.toFinset, q b * greenFn m A a b) =
      ∑ b ∈ hA.toFinset, q' b * greenFn m A a b := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [hq b (hA.mem_toFinset.mp hb)]
  rw [hint, hsum] at hrep
  exact hrep

/-- The boundary indicator in the finite-domain Dirichlet representation can
be replaced by prescribed boundary values, and the source by any function
agreeing with it on the interior. -/
theorem green_representation_of_boundary_and_source_cutoffs
    {m : ℤ → ℤ → ℕ} {A B : Set ℤ} (hA : A.Finite) {a : ℤ}
    (F q q' g : ℤ → ℝ)
    (hq : ∀ b ∈ A, q b = q' b)
    (hg : ∀ b ∈ B, F b = g b)
    (hexit : ∀ᵐ x ∂srwLaw m a, vExitPosition A x ∈ B)
    (hrep : F a = (∫ x, B.indicator F (vExitPosition A x) ∂srwLaw m a) -
      ∑ b ∈ hA.toFinset, q b * greenFn m A a b) :
    F a = (∫ x, g (vExitPosition A x) ∂srwLaw m a) -
      ∑ b ∈ hA.toFinset, q' b * greenFn m A a b := by
  apply green_representation_congr_on hA F q q' (B.indicator F) g hq ?_ hexit hrep
  intro b hb
  rw [indicator_of_mem hb, hg b hb]

end MatedCRT
