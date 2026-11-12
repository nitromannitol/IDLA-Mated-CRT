import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.FirstPass.S5c.GreenDiagDomination
import LatticeProb.Network.ConductanceThomsonBound

/-!
# The killed Green function as a Poisson solution in finite-sum form

For a finite set `A`, the Green function `u = G_A(·, x)` of simple random walk killed on exiting `A`
satisfies `Δ u = -δ_x` on `A` (eq:discrete-green-laplacian), where `Δ` is the degree normalized
Laplacian. Multiplying by the degree gives the unnormalized (conductance) form

  `∑_b m(a,b) (u(a) - u(b)) = deg(x) 1{a = x}`   for `a ∈ A`,

with the sum over any finite set `S` containing every neighbour of `A`, and `u = 0` off `A`.
This is the form consumed by the Thomson bound for the effective resistance of a network with
conductances `c(a,b) = m(a,b)`.

Combined with the Thomson bound (`LatticeProb.le_mul_flowEnergy_of_poisson`), every entry of the
killed Green function is bounded by the degree of the pole times the energy of any unit flow from
the pole out of `A`:

  `G_A(a, x) ≤ G_A(x, x) ≤ deg(x) · ½ ∑_{a,b} θ(a,b)² / m(a,b)`

(the first inequality is the maximum principle `greenFn_le_greenFn_diag`). This is the effective
resistance bound of [BG20, lem-eff-res-upper] in the form used for the crude Green function bound.
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

/-- **Thomson bound for the diagonal of the killed Green function.** For a finite set `A`, a
finite set `S ⊇ A` containing every neighbour of `A`, symmetric conductances `m`, and any unit flow
`θ` from `x ∈ A` out of `A` carried by the edges, `G_A(x,x) ≤ deg(x) · ½ ∑_{a,b ∈ S} θ(a,b)²/m(a,b)`. -/
theorem greenFn_diag_le_mdeg_mul_flowEnergy (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hsymm : ∀ a b, m a b = m b a)
    {A S : Finset ℤ} (hAS : A ⊆ S) (hS : ∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∈ S) {x : ℤ} (hx : x ∈ A)
    {θ : ℤ → ℤ → ℝ} (hθ : ∀ a b, θ a b = -θ b a) (hθc : ∀ a b, m a b = 0 → θ a b = 0)
    (hdiv : ∀ a ∈ A, ∑ b ∈ S, θ a b = if a = x then 1 else 0) :
    greenFn m (A : Set ℤ) x x ≤
      (mdeg m x : ℝ) * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / (m a b : ℝ)) :=
  LatticeProb.le_mul_flowEnergy_of_poisson (c := fun a b => (m a b : ℝ))
    (u := fun y => greenFn m (A : Set ℤ) y x) hAS
    (fun a b => by show (m a b : ℝ) = m b a; rw [hsymm a b]) (fun _ _ => Nat.cast_nonneg _)
    (fun a ha => greenFn_eq_zero_of_not_mem m (by simpa using ha) x) hx (Nat.cast_nonneg _)
    (fun a ha => sum_mul_greenFn_sub_eq_ite hlf hcons A.finite_toSet x
      (fun a' ha' b hb => hS a' (by simpa using ha') b hb) a (by simpa using ha))
    hθ (fun a b h => hθc a b (by exact_mod_cast h)) hdiv

/-- **Thomson bound for the killed Green function, every entry.** Under the hypotheses of
`greenFn_diag_le_mdeg_mul_flowEnergy`, `G_A(a,x) ≤ deg(x) · ½ ∑_{a,b ∈ S} θ(a,b)²/m(a,b)` for every
`a` (maximum principle `greenFn_le_greenFn_diag`). -/
theorem greenFn_le_mdeg_mul_flowEnergy (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hsymm : ∀ a b, m a b = m b a)
    {A S : Finset ℤ} (hAS : A ⊆ S) (hS : ∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∈ S) {x : ℤ} (hx : x ∈ A)
    {θ : ℤ → ℤ → ℝ} (hθ : ∀ a b, θ a b = -θ b a) (hθc : ∀ a b, m a b = 0 → θ a b = 0)
    (hdiv : ∀ a ∈ A, ∑ b ∈ S, θ a b = if a = x then 1 else 0) (a : ℤ) :
    greenFn m (A : Set ℤ) a x ≤
      (mdeg m x : ℝ) * ((1 / 2) * ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / (m a b : ℝ)) :=
  (greenFn_le_greenFn_diag hlf hcons A.finite_toSet a x).trans
    (greenFn_diag_le_mdeg_mul_flowEnergy hlf hcons hsymm hAS hS hx hθ hθc hdiv)

end MatedCRT
