import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Order.Compact

/-!
# FIRST PASS, Lemma 5.3 (three-inputs section 3, A9): compact minima of a positive continuous function

Deterministic (extreme value theorem, Mathlib `IsCompact.exists_isMinOn`). If `f` is continuous on a compact set `K`
and `f > 0` on `K`, then `f` has a positive uniform lower bound on `K`. Used for the margin `A_1` of the full G1
(three-inputs A9, "take compact minima"): on each compact `K ⊆ Λ_t` the margin attains a positive minimum, so no
measurable selection and no frozen input is needed.
-/

namespace MatedCRT.S5c

open Set

/-- Extreme value theorem for a positive continuous function on a compact set: a uniform positive lower bound
(three-inputs A9). For `K = ∅` the constant `1` works. -/
theorem exists_pos_lower_bound_on_compact {X : Type*} [TopologicalSpace X] {K : Set X} {f : X → ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ β : ℝ, 0 < β ∧ ∀ x ∈ K, β ≤ f x := by
  rcases K.eq_empty_or_nonempty with hKe | hne
  · exact ⟨1, one_pos, fun x hx => by simp [hKe] at hx⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x₀, hpos x₀ hx₀, fun x hx => isMinOn_iff.1 hmin x hx⟩

/-- Uniform positive lower bound on a compact subset `K` of an open set `U` on which `f` is continuous and positive
(three-inputs A9 with `U = Λ_t`, `K ⊆ Λ_t` compact). -/
theorem exists_pos_lower_bound_of_subset {X : Type*} [TopologicalSpace X] {U K : Set X} {f : X → ℝ}
    (hKU : K ⊆ U) (hK : IsCompact K) (hf : ContinuousOn f U) (hpos : ∀ x ∈ U, 0 < f x) :
    ∃ β : ℝ, 0 < β ∧ ∀ x ∈ K, β ≤ f x :=
  exists_pos_lower_bound_on_compact hK (hf.mono hKU) (fun x hx => hpos x (hKU hx))

end MatedCRT.S5c
