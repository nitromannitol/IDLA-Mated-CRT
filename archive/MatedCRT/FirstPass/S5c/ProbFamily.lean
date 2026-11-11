import Mathlib

/-!
# FIRST PASS, Lemma 5.3: localization with bad events depending on the truncation index (G-5-3 Section 1 assembly)

The bad events of the surplus lower bound involve finitely many masses `s_0, …, s_J` (the convergence errors of
`ConvergenceDivisibleStmt` at each `s_n`, `n ≤ J`), so they depend on the truncation index `J`. Pathwise, on `F`, the
surplus bound `E ε` fails only on `Bad J ε ∪ Loc J`; if for each `J` the bad events vanish as `ε → 0` and the localization
events are uniformly small for large `J`, then `P (F ∩ (E ε)ᶜ) → 0`. Outer-measure bookkeeping only.
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- **Localization with truncation-dependent bad events** (G-5-3 Section 1 assembly). -/
theorem tendsto_failure_of_bad_family {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω}
    {E : ℝ → Set Ω} {Bad : ℕ → ℝ → Set Ω} {Loc : ℕ → Set Ω}
    (hsplit : ∀ (ε : ℝ) (J : ℕ), F ∩ (E ε)ᶜ ⊆ Bad J ε ∪ Loc J)
    (hBad : ∀ J : ℕ, Tendsto (fun ε => P (Bad J ε)) (𝓝[>] 0) (𝓝 0))
    (hLoc : ∀ η : ℝ≥0∞, 0 < η → ∃ J : ℕ, P (Loc J) ≤ η) :
    Tendsto (fun ε => P (F ∩ (E ε)ᶜ)) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  have hη : (0 : ℝ≥0∞) < κ / 2 := ENNReal.div_pos hκ.ne' (by norm_num)
  obtain ⟨J, hJ⟩ := hLoc (κ / 2) hη
  have hB := ENNReal.tendsto_nhds_zero.1 (hBad J) (κ / 2) hη
  filter_upwards [hB] with ε hε
  calc P (F ∩ (E ε)ᶜ) ≤ P (Bad J ε ∪ Loc J) := measure_mono (hsplit ε J)
    _ ≤ P (Bad J ε) + P (Loc J) := measure_union_le _ _
    _ ≤ κ / 2 + κ / 2 := add_le_add hε hJ
    _ = κ := ENNReal.add_halves κ

end MatedCRT.S5c
