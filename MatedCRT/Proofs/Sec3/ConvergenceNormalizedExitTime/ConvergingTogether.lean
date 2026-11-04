import MatedCRT.Defs.Notation

/-! The approximation step for convergence in probability. -/

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace MatedCRT

/-- Convergence in probability follows from approximations whose errors can
be made arbitrarily small uniformly at sufficiently fine scales. No
measurability assumption on the failure events is needed. -/
theorem tendstoInProbability_of_approximations
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : ℝ → Ω → ℝ) (U : Ω → ℝ)
    (happrox : ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e →
      ∃ (G : ℝ → Ω → ℝ) (V : Ω → ℝ), TendstoInProbability P G V ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | t < |F ε ω - G ε ω|} < e) ∧
        P {ω | t < |V ω - U ω|} < e) :
    TendstoInProbability P F U := by
  intro t ht
  apply ENNReal.tendsto_nhds_zero.2
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have he4 : 0 < (e / 2) / 2 := ENNReal.half_pos he2.ne'
  have ht3 : 0 < t / 3 := by linarith
  obtain ⟨G, V, hconv, hFG, hVU⟩ := happrox (t / 3) ht3 ((e / 2) / 2) he4
  have hGV := ENNReal.tendsto_nhds_zero.1 (hconv (t / 3) ht3) (e / 2) he2
  filter_upwards [hFG, hGV] with ε hFGε hGVε
  calc
    P {ω | t < |F ε ω - U ω|} ≤
        P ({ω | t / 3 < |F ε ω - G ε ω|} ∪
          ({ω | t / 3 < |V ω - U ω|} ∪ {ω | t / 3 < |G ε ω - V ω|})) := by
      apply measure_mono
      intro ω hω
      by_contra hn
      have h1 : |F ε ω - G ε ω| ≤ t / 3 := le_of_not_gt fun h => hn (Or.inl h)
      have h2 : |V ω - U ω| ≤ t / 3 := le_of_not_gt fun h => hn (Or.inr (Or.inl h))
      have h3 : |G ε ω - V ω| ≤ t / 3 := le_of_not_gt fun h => hn (Or.inr (Or.inr h))
      have hab := abs_add_le (F ε ω - G ε ω) (G ε ω - V ω)
      have hbc := abs_add_le ((F ε ω - G ε ω) + (G ε ω - V ω)) (V ω - U ω)
      have heq : F ε ω - U ω = (F ε ω - G ε ω) + (G ε ω - V ω) + (V ω - U ω) := by ring
      change t < |F ε ω - U ω| at hω
      rw [heq] at hω
      linarith
    _ ≤ P {ω | t / 3 < |F ε ω - G ε ω|} +
        (P {ω | t / 3 < |V ω - U ω|} + P {ω | t / 3 < |G ε ω - V ω|}) :=
      (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
    _ ≤ (e / 2) / 2 + ((e / 2) / 2 + e / 2) :=
      add_le_add (le_of_lt hFGε) (add_le_add (le_of_lt hVU) hGVε)
    _ = e := by rw [← add_assoc, ENNReal.add_halves, ENNReal.add_halves]

end MatedCRT
