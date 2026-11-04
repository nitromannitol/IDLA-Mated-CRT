import MatedCRT.Draft.Section4

/-!
# Uniform convergence from subsequential convergence

The deterministic subsequence argument used in the proof of Theorem 4.1.
-/

open Filter Set
open scoped Topology

namespace MatedCRT

/-- If every subsequence has a further subsequence converging uniformly to the same function,
then the original sequence converges uniformly. -/
theorem tendstoUniformlyOn_of_subsequence {α β : Type*} [UniformSpace β]
    {F : ℕ → α → β} {f : α → β} {s : Set α}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoUniformlyOn (fun n => F (φ (ψ n))) f atTop s) :
    TendstoUniformlyOn F f atTop s := by
  intro U hU
  by_contra hfail
  have hfreq : ∃ᶠ n in atTop, ¬ ∀ x ∈ s, (f x, F n x) ∈ U :=
    not_eventually.mp hfail
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, _, hconv⟩ := h φ hφ
  obtain ⟨n, hn⟩ := (hconv U hU).exists
  exact hbad (ψ n) hn

end MatedCRT
