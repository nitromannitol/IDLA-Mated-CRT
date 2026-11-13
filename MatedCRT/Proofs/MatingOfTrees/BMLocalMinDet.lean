/- Adds `fine_Icc` to the Brownian local-extrema determinism lemmas of the shared library. -/
import MatedCRT.Steps.Infra.MatingOfTrees
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Probability.BMLocalMin.Det

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology

namespace MatedCRTHarmonic.MoTPort
namespace BMLocalMin

/-- The family `ℚ ∪ {T}` is fine in `[0, T]`. -/
lemma fine_Icc {D : Set ℝ} (hQ : ∀ u : ℚ, (u : ℝ) ∈ D) {T : ℝ} (hT : 0 < T) (hTD : T ∈ D) :
    Fine D (Icc 0 T) := by
  intro t ht ε hε
  obtain ⟨p, hp, hp0, hpt, hp', hpt'⟩ := fine_left hQ ht.1 hε
  have hR : ∃ q ∈ D, t ≤ q ∧ q < t + ε ∧ q ≤ T ∧ (t < q ∨ t = T) := by
    rcases ht.2.eq_or_lt with h | h
    · exact ⟨T, hTD, h.le, by linarith, le_rfl, Or.inr h⟩
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < min T (t + ε) from lt_min h (by linarith))
      rw [lt_min_iff] at hq2
      exact ⟨q, hQ q, hq1.le, hq2.2, hq2.1.le, Or.inl hq1⟩
  obtain ⟨q, hq, htq, hq', hqT, htq'⟩ := hR
  have hpq : p < q := by
    rcases hpt' with h | h
    · linarith
    · rcases htq' with h' | h'
      · linarith
      · linarith
  exact ⟨p, hp, q, hq, hpq, hpt, htq, hp', hq', Icc_subset_Icc hp0 hqT⟩

end BMLocalMin
end MatedCRTHarmonic.MoTPort
