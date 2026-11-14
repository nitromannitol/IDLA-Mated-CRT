import MatedCRT.Proofs.WalkPotential.Markov

/-! # Finite-index cylinders for multigraph random walk -/

namespace MatedCRT

open MeasureTheory
open scoped ENNReal

/-- The finite-dimensional distributions of the multigraph walk, indexed by `Fin`. -/
theorem srwLaw_fin_cylinder (m : ℤ → ℤ → ℕ) (a : ℤ) (n : ℕ)
    (x : Fin (n + 1) → ℤ) :
    srwLaw m a {ω | ∀ i : Fin (n + 1), ω i = x i} =
      (if x 0 = a then 1 else 0) *
        ∏ i : Fin n, srwStep m (x i.castSucc) {x i.succ} := by
  classical
  let s : ℕ → ℤ := fun i => if h : i < n + 1 then x ⟨i, h⟩ else x 0
  have hs : ∀ i : Fin (n + 1), s i = x i := by
    intro i
    simp only [s, dite_eq_left i.isLt]
  have he : {ω : ℕ → ℤ | ∀ i : Fin (n + 1), ω i = x i} =
      {ω | ∀ i ≤ n, ω i = s i} := by
    ext ω
    constructor
    · intro h i hi
      rw [hs ⟨i, Nat.lt_succ_of_le hi⟩]
      exact h ⟨i, Nat.lt_succ_of_le hi⟩
    · intro h i
      rw [← hs i]
      exact h i (Nat.le_of_lt_succ i.isLt)
  have hs0 : s 0 = x 0 := hs 0
  rw [he, srwLaw_cylinder, hs0, ← Fin.prod_univ_eq_prod_range]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have h1 : s (i : ℕ) = x i.castSucc := hs i.castSucc
  have h2 : s ((i : ℕ) + 1) = x i.succ := hs i.succ
  rw [h1, h2]

end MatedCRT
