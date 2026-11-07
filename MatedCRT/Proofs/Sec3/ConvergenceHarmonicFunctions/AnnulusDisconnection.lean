import MatedCRT.Defs.WalkDisconnection
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! # Walk traces and annulus disconnection -/

namespace MatedCRT

open Set

/-- A disconnecting vertex set intersects every graph walk from the separated
vertex to the target set. -/
theorem graphDisconnects_intersects_walk {V : Type*} {G : SimpleGraph V}
    {K A : Set V} {y a : V} (h : graphDisconnects G K y A) (ha : a ∈ A)
    (w : G.Walk y a) : ∃ v ∈ w.support, v ∈ K := by
  classical
  by_contra hn
  have hw : ∀ v ∈ w.support, v ∈ Kᶜ := by
    intro v hv
    simp only [mem_compl_iff]
    intro hvK
    exact hn ⟨v, hv, hvK⟩
  exact h (hw y w.start_mem_support) a ha (hw a w.end_mem_support)
    ⟨w.induce Kᶜ hw⟩

/-- If a walk disconnects a vertex from a target before hitting the target,
then every graph walk joining them contains a vertex visited before the hit. -/
theorem walkDisconnectsBeforeHit_intersects_walk
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {y a : ℤ} {x : ℕ → ℤ}
    (h : walkDisconnectsBeforeHit m A y x) (ha : a ∈ A)
    (w : (adjGraph m).Walk y a) :
    ∃ n : ℕ, (n : ℕ∞) < vHitTime A x ∧ x n ∈ w.support := by
  obtain ⟨v, hv, ⟨n, hn, hnv⟩⟩ := graphDisconnects_intersects_walk h ha w
  exact ⟨n, hn, hnv ▸ hv⟩

/-- A graph walk supported outside an open region rules out disconnection by
a trace contained in that region. This is the graph-theoretic part of the
planar separation step in the annulus argument. -/
theorem not_walkDisconnectsBeforeHit_of_avoiding_region
    {m : ℤ → ℤ → ℕ} {A U : Set ℤ} {y a : ℤ} {x : ℕ → ℤ}
    (ha : a ∈ A) (w : (adjGraph m).Walk y a)
    (hw : ∀ v ∈ w.support, v ∉ U)
    (hx : ∀ n : ℕ, (n : ℕ∞) < vHitTime A x → x n ∈ U) :
    ¬ walkDisconnectsBeforeHit m A y x := by
  intro h
  obtain ⟨n, hn, hnw⟩ := walkDisconnectsBeforeHit_intersects_walk h ha w
  exact hw (x n) hnw (hx n hn)

end MatedCRT
