import Mathlib

/-!
# FIRST PASS, Lemma 5.3: compact cover step (G-5-3 note, Section 1, eq. (5))

Deterministic: an increasing sequence of continuous functions with pointwise eventual positivity on a compact set
is eventually positive on that set, uniformly (the open sets `{A n > 0}` increase and cover the compact set; a finite
subcover is a single member). Pure topology; no paper input.
-/

namespace MatedCRT.S5c

open Set Topology

/-- A compact set covered by an increasing sequence of open sets lies in one member of the sequence. -/
lemma compact_subset_of_monotone_cover {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (O : ℕ → Set X) (hO : ∀ n, IsOpen (O n)) (hmono : Monotone O) (hcov : K ⊆ ⋃ n, O n) :
    ∃ n, K ⊆ O n :=
  hK.elim_directed_cover O hO hcov hmono.directed_le

/-- **Eq. (5), uniform form** (G-5-3 Section 1): if `A n` are continuous, nondecreasing in `n` at each point, and
each point of a compact `K` is eventually strictly positive, then for some `n` the function `A n` is strictly positive
on all of `K`. -/
lemma exists_forall_pos_of_monotone_eventually_pos {K : Set ℂ} (hK : IsCompact K) (A : ℕ → ℂ → ℝ)
    (hA : ∀ n, Continuous (A n)) (hmono : ∀ x, Monotone fun n => A n x)
    (hpos : ∀ x ∈ K, ∃ n, 0 < A n x) : ∃ n, ∀ x ∈ K, 0 < A n x := by
  obtain ⟨n, hn⟩ := compact_subset_of_monotone_cover hK (fun n => {x | 0 < A n x})
    (fun n => isOpen_lt continuous_const (hA n))
    (fun n m hnm x hx => lt_of_lt_of_le hx (hmono x hnm))
    (fun x hx => by
      obtain ⟨n, hn⟩ := hpos x hx
      exact mem_iUnion.2 ⟨n, hn⟩)
  exact ⟨n, fun x hx => hn hx⟩

/-- **Eq. (5), minimum form**: on a nonempty compact `K`, the minimum of `A n` is strictly positive for some `n`. -/
lemma exists_min_pos_of_monotone_eventually_pos {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty)
    (A : ℕ → ℂ → ℝ) (hA : ∀ n, Continuous (A n)) (hmono : ∀ x, Monotone fun n => A n x)
    (hpos : ∀ x ∈ K, ∃ n, 0 < A n x) : ∃ n, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K, b ≤ A n x := by
  obtain ⟨n, hn⟩ := exists_forall_pos_of_monotone_eventually_pos hK A hA hmono hpos
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne (hA n).continuousOn
  exact ⟨n, A n x₀, hn x₀ hx₀, fun x hx => hmin hx⟩

end MatedCRT.S5c
