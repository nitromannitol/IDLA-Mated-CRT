import MatedCRT.Proofs.Sec4.GreenLaplacian
import MatedCRT.Proofs.Sec4.SubsequentialProperties.DiscreteComparison

/-! # Discrete Dirichlet problem on a finite set

On a finite set `A` of vertices of a locally finite multigraph, the maximum principle (as an injectivity statement)
makes the restricted Laplacian injective, hence surjective (finite dimension). This gives a discrete solution with
prescribed interior Laplacian and prescribed values off `A`. Pattern: `Proofs/Sandpile/Dirichlet.lean`, with the
connectivity hypothesis replaced by the maximum principle on arbitrary finite sets. -/

namespace MatedCRT.FirstPass35Bridge

open Set

/-- The Laplacian of the zero function vanishes. -/
theorem mLaplacian_zero_fun' (m : ℤ → ℤ → ℕ) (a : ℤ) : mLaplacian m (fun _ => (0 : ℝ)) a = 0 := by
  simp [mLaplacian]

/-- **Discrete Dirichlet problem on a finite set.** If the maximum principle holds on `A` (every subharmonic
function on `A` attains its maximum over `A` at the boundary `∂A`), then for every interior datum `ψ` and every
boundary datum `w` there is a function `G` equal to `w` off `A` with `Δ G = ψ` on `A`. -/
theorem exists_discrete_dirichlet_extension {m : ℤ → ℤ → ℕ} (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    {A : Set ℤ} (hA : A.Finite)
    (hmax : ∀ u : ℤ → ℝ, IsSubharmonicOn m u A → ∀ a ∈ A, ∃ b ∈ vBoundary m A, u a ≤ u b)
    (ψ w : ℤ → ℝ) :
    ∃ G : ℤ → ℝ, (∀ b, b ∉ A → G b = w b) ∧ ∀ a ∈ A, mLaplacian m G a = ψ a := by
  classical
  have := hA.to_subtype
  have hinj : Function.Injective (restrictedLaplacian m hlf A) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hlap : ∀ a ∈ A, mLaplacian m (extendByZero A x) a = 0 := fun a ha => congrFun hx ⟨a, ha⟩
    have hbd : ∀ b ∈ vBoundary m A, extendByZero A x b = 0 := fun b hb => extendByZero_of_not_mem hb.1
    have hsub : IsSubharmonicOn m (extendByZero A x) A := fun a ha => (hlap a ha).ge
    have hsup : IsSubharmonicOn m (fun z => (0 : ℝ) - extendByZero A x z) A := by
      intro a ha
      have h := mLaplacian_sub_of_locallyFinite hlf (fun _ => (0 : ℝ)) (extendByZero A x) a
      rw [mLaplacian_zero_fun', hlap a ha] at h
      show 0 ≤ mLaplacian m (fun z => (0 : ℝ) - extendByZero A x z) a
      rw [h]
      norm_num
    have h1 := hmax _ hsub
    have h2 := hmax _ hsup
    have hfin : ∀ a ∈ A, extendByZero A x a = 0 := by
      intro a ha
      obtain ⟨b, hb, hvb⟩ := h1 a ha
      obtain ⟨b', hb', hvb'⟩ := h2 a ha
      rw [hbd b hb] at hvb
      have hv' : (0 : ℝ) - extendByZero A x b' = 0 := by rw [hbd b' hb']; ring
      have hvb'' : (0 : ℝ) - extendByZero A x a ≤ 0 := by
        have := hvb'
        rw [hv'] at this
        exact this
      linarith
    funext a
    have := hfin a a.2
    rw [extendByZero_coe] at this
    exact this
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.1 hinj) (fun a : A => ψ a - mLaplacian m w a)
  refine ⟨fun z => extendByZero A x z + w z, ?_, ?_⟩
  · intro b hb
    simp [extendByZero_of_not_mem hb]
  · intro a ha
    have hTx : mLaplacian m (extendByZero A x) a = ψ a - mLaplacian m w a := congrFun hx ⟨a, ha⟩
    rw [mLaplacian_add_of_locallyFinite hlf]
    linarith

end MatedCRT.FirstPass35Bridge
