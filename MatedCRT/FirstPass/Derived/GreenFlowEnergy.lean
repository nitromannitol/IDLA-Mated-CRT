import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# The killed Green function as a Poisson solution in finite-sum form

For a finite set `A`, the Green function `u = G_A(·, x)` of simple random walk killed on exiting `A`
satisfies `Δ u = -δ_x` on `A` (eq:discrete-green-laplacian), where `Δ` is the degree normalized
Laplacian. Multiplying by the degree gives the unnormalized (conductance) form

  `∑_b m(a,b) (u(a) - u(b)) = deg(x) 1{a = x}`   for `a ∈ A`,

with the sum over any finite set `S` containing every neighbour of `A`, and `u = 0` off `A`.
This is the form consumed by the Thomson bound for the effective resistance of a network with
conductances `c(a,b) = m(a,b)`.
-/

namespace MatedCRT

open Finset

variable {m : ℤ → ℤ → ℕ}

/-- **Poisson equation for the killed Green function, finite-sum form.** For a finite set `A`
and a finite set `S` containing every neighbour of every vertex of `A`,
`∑_{b ∈ S} m(a,b) (G_A(a,x) - G_A(b,x)) = deg(x) 1{a = x}` for every `a ∈ A`. -/
theorem sum_mul_greenFn_sub_eq_ite (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} (hA : A.Finite) (x : ℤ) {S : Finset ℤ}
    (hS : ∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∈ S) :
    ∀ a ∈ A, ∑ b ∈ S, (m a b : ℝ) * (greenFn m A a x - greenFn m A b x) =
      if a = x then (mdeg m x : ℝ) else 0 := by
  intro a ha
  set u : ℤ → ℝ := fun y => greenFn m A y x with hu
  have hΔ := WalkPotential.mLaplacian_greenFn hlf hcons hA x a ha
  have hmul := mLaplacian_mul_mdeg hlf u a
  have hsub : nbrs hlf a ⊆ S := fun b hb => hS a ha b ((mem_nbrs hlf).1 hb)
  have hS' : ∑ b ∈ S, (m a b : ℝ) * (u a - u b) = ∑ b ∈ nbrs hlf a, (m a b : ℝ) * (u a - u b) :=
    (Finset.sum_subset hsub fun b _ hb => by
      rw [show m a b = 0 from not_not.1 fun h => hb ((mem_nbrs hlf).2 h)]; simp).symm
  have hneg : ∑ b ∈ nbrs hlf a, (m a b : ℝ) * (u a - u b) = -lapSum hlf u a := by
    rw [show lapSum hlf u a = ∑ b ∈ nbrs hlf a, (m a b : ℝ) * (u b - u a) from rfl,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  change ∑ b ∈ S, (m a b : ℝ) * (u a - u b) = _
  rw [hS', hneg, ← hmul, hΔ]
  by_cases h : a = x
  · subst h; simp
  · simp [h]

/-- The killed Green function vanishes off `A` (first variable). -/
theorem greenFn_eq_zero_of_not_mem' {A : Set ℤ} (x : ℤ) :
    ∀ a, a ∉ A → greenFn m A a x = 0 :=
  fun _ ha => greenFn_eq_zero_of_not_mem m ha x

end MatedCRT
