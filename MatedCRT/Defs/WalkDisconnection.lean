import MatedCRT.Defs.RandomWalk

/-! # Walk traces and graph disconnection -/

namespace MatedCRT

open Set

/-- Vertices visited strictly before a prescribed extended time. -/
def walkTraceBefore {V : Type*} (x : ℕ → V) (t : ℕ∞) : Set V :=
  {v | ∃ n : ℕ, (n : ℕ∞) < t ∧ x n = v}

/-- `K` disconnects `y` from `A` if no path in the complement of `K`
connects `y` to a vertex of `A`. This includes the case `y ∈ K`. -/
def graphDisconnects {V : Type*} (G : SimpleGraph V) (K : Set V)
    (y : V) (A : Set V) : Prop :=
  ∀ (hy : y ∉ K) (a : V) (_ha : a ∈ A) (hak : a ∉ K),
    ¬ (G.induce Kᶜ).Reachable ⟨y, hy⟩ ⟨a, hak⟩

/-- The walk disconnects `y` from `A` strictly before its first hit of `A`. -/
def walkDisconnectsBeforeHit (m : ℤ → ℤ → ℕ) (A : Set ℤ)
    (y : ℤ) (x : ℕ → ℤ) : Prop :=
  graphDisconnects (adjGraph m) (walkTraceBefore x (vHitTime A x)) y A

end MatedCRT
