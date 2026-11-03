import MatedCRT.Draft.SectionA
import MatedCRT.Proofs.Infra.DiscretePotential

/-!
# Lemma A.1: the discrete divergence theorem

Proof of `DiscreteDivergenceTheoremStmt` (lemma:discrete-divergence-theorem, line 3347): for a symmetric locally finite
edge multiplicity and finitely supported `f, g`,
`∑_a f(a) Δg(a) deg(a) = ∑_a g(a) Δf(a) deg(a)` (summation by parts; Telcs 2006, eq. (2.17)). Both sides equal
`∑_{a,b} m(a,b) f(a) g(b) - ∑_a f(a) g(a) deg(a)` (`finsum_mul_lap_mul_deg_eq`), which is symmetric in `f, g` by the
symmetry of `m`.
-/

namespace MatedCRT

open Set Finset Classical

variable {α : Type*} {m : α → α → ℕ}

/-- For `u, v` supported in the finite set `s`:
`∑_a u(a) Δv(a) deg(a) = ∑_{a, b ∈ s} m(a,b) u(a) v(b) - ∑_{a ∈ s} u(a) v(a) deg(a)`. -/
theorem finsum_mul_lap_mul_deg_eq (hlf : IsLocallyFiniteMult m) (s : Finset α) (u v : α → ℝ)
    (hu : Function.support u ⊆ ↑s) (hv : Function.support v ⊆ ↑s) :
    ∑ᶠ a, u a * mLaplacian m v a * (mdeg m a : ℝ) =
      ∑ a ∈ s, ∑ b ∈ s, (m a b : ℝ) * u a * v b - ∑ a ∈ s, u a * v a * (mdeg m a : ℝ) := by
  have h1 : (fun a => u a * mLaplacian m v a * (mdeg m a : ℝ)) = fun a => u a * lapSum hlf v a := by
    funext a
    rw [mul_assoc, mLaplacian_mul_mdeg hlf]
  rw [h1, finsum_eq_sum_of_support_subset _ (s := s) ?_]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : lapSum hlf v a = ∑ b ∈ s, (m a b : ℝ) * v b - v a * (mdeg m a : ℝ) := by
      have h3 : ∑ b ∈ nbrs hlf a, (m a b : ℝ) * v b = ∑ b ∈ s, (m a b : ℝ) * v b := by
        rw [← finsum_mul_eq_sum_nbrs hlf a v]
        refine finsum_eq_sum_of_support_subset _ fun b hb => hv ?_
        intro hvb
        apply hb
        simp [hvb]
      rw [mdeg_cast_eq hlf a, ← h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [h2, mul_sub, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun b _ => ?_
      ring
    · ring
  · intro a ha
    apply hu
    intro hua
    apply ha
    simp [hua]

/-- **Lemma A.1** (lemma:discrete-divergence-theorem, line 3347). -/
theorem discreteDivergenceTheorem : DiscreteDivergenceTheoremStmt := by
  intro α m hsymm hlf f g hf hg
  set s : Finset α := hf.toFinset ∪ hg.toFinset with hs
  have hfs : Function.support f ⊆ ↑s := fun a ha => by
    rw [hs, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl ha
  have hgs : Function.support g ⊆ ↑s := fun a ha => by
    rw [hs, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inr (by rwa [Set.Finite.coe_toFinset])
  rw [finsum_mul_lap_mul_deg_eq hlf s f g hfs hgs, finsum_mul_lap_mul_deg_eq hlf s g f hgs hfs]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsymm b a]
    ring
  · refine Finset.sum_congr rfl fun a _ => ?_
    ring

end MatedCRT
