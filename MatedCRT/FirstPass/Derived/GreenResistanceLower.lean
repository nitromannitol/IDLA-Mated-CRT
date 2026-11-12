import MatedCRT.FirstPass.Derived.GreenInnerBoundaryMin
import LatticeProb.Network.ClampedPoissonFlowBound

/-!
# Lower bound for the energy of a unit flow in terms of the Green kernel

Let `B ⊆ ℤ` be finite, `x ∈ A ⊆ B`, and `g_B(y, x) = G_B(y, x) / deg(x)` the Green kernel with
pole `x`. If `g_B(·, x) ≥ a₀ ≥ 0` on `A`, then every unit flow `θ` from `A` out of `B` (divergence
free on `B ∖ A`, total flux `1` out of `A`) has energy `½ ∑ θ(a,b)² / m(a,b) ≥ a₀`.
Consequently the minimum of `g_B(·, x)` over the inner boundary of `A` is bounded above by the
energy of any unit flow from `A` to the complement of `B`. This is the lower half of
[BG20, Lem. 3.4] in the strengthened form without error term, used for [BG20, Lem. 5.5].

The proof wires the abstract statement `LatticeProb.le_flowEnergy_of_clamped_poisson` (the clamped
potential `min(u, a₀)` is a test function of Dirichlet energy at most `a₀`) to the Poisson
equation `∑_b m(a,b) (G_B(a,x) - G_B(b,x)) = deg(x) 1{a = x}`.
-/

namespace MatedCRT

open Finset

variable {m : ℤ → ℤ → ℕ}

/-- **Energy of a unit flow from `A` out of `B` is at least `a₀`** when the Green kernel
`g_B(·, x)` is at least `a₀ ≥ 0` on `A`. -/
theorem le_flowEnergy_of_le_greenKernel (hlf : ∀ a, {b | m a b ≠ 0}.Finite)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hsymm : ∀ a b, m a b = m b a)
    {B A S : Finset ℤ} (hBS : B ⊆ S) (hAB : A ⊆ B)
    (hS : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∈ S) {x : ℤ} (hx : x ∈ A)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (hA : ∀ y ∈ A, a₀ ≤ greenKernel m (B : Set ℤ) y x)
    {θ : ℤ → ℤ → ℝ} (hθ : ∀ a b, θ a b = -θ b a) (hθc : ∀ a b, m a b = 0 → θ a b = 0)
    (hdiv : ∀ v ∈ B, v ∉ A → ∑ b ∈ S, θ v b = 0) (hflux : ∑ v ∈ A, ∑ b ∈ S, θ v b = 1) :
    a₀ ≤ (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / (m a b : ℝ) := by
  classical
  have hdpos : (0 : ℝ) < (mdeg m x : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero (mdeg_ne_zero_of_ne_zero hlf (hcons x)))
  refine LatticeProb.le_flowEnergy_of_clamped_poisson (c := fun a b => (m a b : ℝ))
    (u := fun v => greenKernel m (B : Set ℤ) v x) hBS hAB
    (fun a b => by rw [hsymm a b]) (fun _ _ => Nat.cast_nonneg _) ?_ hx ?_ ha₀ hA hθ
    (fun a b hab => hθc a b (by exact_mod_cast hab)) hdiv hflux
  · intro a ha
    unfold greenKernel
    rw [greenFn_eq_zero_of_not_mem' x a (by simpa using ha), zero_div]
  · intro a ha
    have hp := sum_mul_greenFn_sub_eq_ite hlf hcons B.finite_toSet x
      (fun a ha b hb => hS a (by simpa using ha) b hb) a (by simpa using ha)
    have : ∑ b ∈ S, (m a b : ℝ) * (greenKernel m (B : Set ℤ) a x - greenKernel m (B : Set ℤ) b x) =
        (∑ b ∈ S, (m a b : ℝ) * (greenFn m (B : Set ℤ) a x - greenFn m (B : Set ℤ) b x)) /
          (mdeg m x : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold greenKernel
      ring
    simp only [this, hp]
    by_cases hax : a = x
    · subst hax
      simp [hdpos.ne']
    · simp [hax]

/-- **Minimum of the Green kernel over the inner boundary is at most the energy of a unit flow.**
For finite `x ∈ A ⊆ B ⊆ S` and a unit flow `θ` from `A` out of `B`, there is a point `y ∈ A` with
a neighbour outside `A` at which `v ↦ G_B(v, x)` is minimal over `A`, and
`g_B(y, x) ≤ ½ ∑ θ(a,b)² / m(a,b)`. -/
theorem exists_mem_innerBoundary_greenKernel_le_flowEnergy
    (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hsymm : ∀ a b, m a b = m b a) {B A S : Finset ℤ} (hBS : B ⊆ S) (hAB : A ⊆ B)
    (hS : ∀ a ∈ B, ∀ b, m a b ≠ 0 → b ∈ S) {x : ℤ} (hx : x ∈ A)
    {θ : ℤ → ℤ → ℝ} (hθ : ∀ a b, θ a b = -θ b a) (hθc : ∀ a b, m a b = 0 → θ a b = 0)
    (hdiv : ∀ v ∈ B, v ∉ A → ∑ b ∈ S, θ v b = 0) (hflux : ∑ v ∈ A, ∑ b ∈ S, θ v b = 1) :
    ∃ y ∈ A, (∃ z, z ∉ A ∧ m y z ≠ 0) ∧
      (∀ v ∈ A, greenFn m (B : Set ℤ) y x ≤ greenFn m (B : Set ℤ) v x) ∧
      greenKernel m (B : Set ℤ) y x ≤ (1 / 2) * ∑ a ∈ S, ∑ b ∈ S, θ a b ^ 2 / (m a b : ℝ) := by
  obtain ⟨y, hyA, hyout, hymin⟩ := exists_mem_innerBoundary_greenFn_le hlf hcons
    B.finite_toSet (Finset.coe_subset.2 hAB) (Finset.mem_coe.2 hx)
  refine ⟨y, Finset.mem_coe.1 hyA, hyout, fun v hv => hymin v (Finset.mem_coe.2 hv), ?_⟩
  refine le_flowEnergy_of_le_greenKernel hlf hcons hsymm hBS hAB hS hx
    (div_nonneg (greenFn_nonnegative _ _ _ _) (Nat.cast_nonneg _)) (fun v hv => ?_) hθ hθc hdiv hflux
  unfold greenKernel
  exact div_le_div_of_nonneg_right (hymin v (Finset.mem_coe.2 hv)) (Nat.cast_nonneg _)

end MatedCRT
