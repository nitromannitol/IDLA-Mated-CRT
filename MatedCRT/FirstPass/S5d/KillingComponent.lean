import MatedCRT.Proofs.WalkPotential.GreenFirstStep
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Vanishing of the killed Green function across components

Referee notes/fp-gaps/CHATGPT-5-1-gaps-referee.md §5.4: for a finite killing set `I ⊆ ℤ` and `a ∈ I` not joined to `0`
by a path inside `I`, the Green function vanishes: `G_I(a,0) = 0`. Proof: the maximum principle on the set `U` of
vertices of `I` reached from `a` inside `I` (`nonpos_of_lapSum_nonneg`, applied to `±G_I(·,0)`), with
`Δ G_I(·,0) = -δ_0 = 0` on `U` (`WalkPotential.mLaplacian_greenFn`) and `G_I(·,0) = 0` off `I`
(`greenFn_eq_zero_of_not_mem`). Deterministic; `U` need not be connected.
-/

namespace MatedCRT

open Set

/-- The vertices of `I` reached from `a` by a path inside `I`: the component of `a` in the killing set `I`. -/
def reachIn (m : ℤ → ℤ → ℕ) (I : Set ℤ) (a : ℤ) : Set ℤ :=
  {b | b ∈ I ∧ Relation.ReflTransGen (fun u v => u ∈ I ∧ v ∈ I ∧ m u v ≠ 0) a b}

theorem mem_reachIn {m : ℤ → ℤ → ℕ} {I : Set ℤ} {a x : ℤ} :
    x ∈ reachIn m I a ↔ x ∈ I ∧ Relation.ReflTransGen (fun u v => u ∈ I ∧ v ∈ I ∧ m u v ≠ 0) a x :=
  Iff.rfl

theorem lapSum_neg_fn {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (u : ℤ → ℝ) (a : ℤ) :
    lapSum hlf (fun x => -u x) a = -lapSum hlf u a := by
  simp only [lapSum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Maximum principle on a finite escaping set.** If `lapSum w = 0` on the finite set `U` and `w = 0` on the
neighbours of `U` outside `U`, then `w = 0` on `U`. Applies `nonpos_of_lapSum_nonneg` to `w` and to `-w`. -/
theorem eq_zero_of_lapSum_zero {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {U : Set ℤ} (hU : U.Finite) {w : ℤ → ℝ} (hW : ∀ a ∈ U, lapSum hlf w a = 0)
    (hbd : ∀ a ∈ U, ∀ b, m a b ≠ 0 → b ∉ U → w b = 0) : ∀ a ∈ U, w a = 0 := by
  have hesc := escape_of_adjacent_succ hcons hU
  have h1 : ∀ a ∈ U, w a ≤ 0 :=
    nonpos_of_lapSum_nonneg hlf hU hesc (w := w) (fun a ha => (hW a ha).ge)
      (fun a ha b hb hbU => (hbd a ha b hb hbU).le)
  have h2 : ∀ a ∈ U, -w a ≤ 0 :=
    nonpos_of_lapSum_nonneg hlf hU hesc (w := fun x => -w x)
      (fun a ha => by simp [lapSum_neg_fn, hW a ha])
      (fun a ha b hb hbU => by simp [hbd a ha b hb hbU])
  intro a ha
  linarith [h1 a ha, h2 a ha]

/-- **Vanishing of the Green function across components** (referee §5.4): if `a ∈ I` and `0` is not reached from `a`
by a path inside `I`, then `G_I(a,0) = 0`. -/
theorem greenFn_eq_zero_of_not_reach {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {I : Set ℤ} (hI : I.Finite) {a : ℤ} (ha : a ∈ I)
    (h0 : (0 : ℤ) ∉ reachIn m I a) :
    greenFn m I a 0 = 0 := by
  have hUI : ∀ x ∈ reachIn m I a, x ∈ I := fun x hx => (mem_reachIn.1 hx).1
  have hU : (reachIn m I a).Finite := hI.subset hUI
  have haU : a ∈ reachIn m I a := mem_reachIn.2 ⟨ha, Relation.ReflTransGen.refl⟩
  have hGn : ∀ x ∈ reachIn m I a, x ≠ 0 := fun x hx hx0 => h0 (by rw [← hx0]; exact hx)
  have hW : ∀ x ∈ reachIn m I a, lapSum hlf (fun y => greenFn m I y 0) x = 0 := by
    intro x hx
    have h := mLaplacian_mul_mdeg hlf (fun y => greenFn m I y 0) x
    have hx0 : (if x = 0 then (1 : ℝ) else 0) = 0 := by simp [hGn x hx]
    rw [WalkPotential.mLaplacian_greenFn hlf hcons hI 0 x (hUI x hx), hx0] at h
    linarith
  have hbd : ∀ x ∈ reachIn m I a, ∀ b, m x b ≠ 0 → b ∉ reachIn m I a →
      (fun y => greenFn m I y 0) b = 0 := by
    intro x hx b hb hbU
    have hbI : b ∉ I := fun hbI =>
      hbU (mem_reachIn.2 ⟨hbI, (mem_reachIn.1 hx).2.tail ⟨(mem_reachIn.1 hx).1, hbI, hb⟩⟩)
    exact greenFn_eq_zero_of_not_mem m hbI 0
  exact eq_zero_of_lapSum_zero hlf hcons hU (w := fun y => greenFn m I y 0) hW hbd a haU

end MatedCRT
