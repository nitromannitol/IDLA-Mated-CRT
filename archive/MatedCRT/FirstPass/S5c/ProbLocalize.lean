import Mathlib

/-!
# FIRST PASS, Lemma 5.3: probabilistic localization of a pathwise surplus bound (G-5-3 Section 1 assembly)

Pathwise, on the event `F = {t < T}`, the surplus lower bound `E ε` fails only on a bad event `Bad ε` (finitely many
uniform convergences, cell diameters, mass threshold: probability tending to zero) or on a localization event `Loc J`
(the random floor index exceeds `J` or the random floor is small), with `P (Loc J)` uniformly small for large `J`.
Then `P (F ∩ (E ε)ᶜ) → 0`. Outer-measure bookkeeping only: no measurability of `E ε` is needed (`TendsToOneOn`,
Defs/Notation.lean:40). Measurability of the localization events is the open step B1.
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- **Localization of the surplus bound** (G-5-3 Section 1 assembly): a pathwise splitting into vanishing bad events
and uniformly small localization events yields vanishing failure probability. -/
theorem tendsto_failure_of_bad_and_loc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω}
    {E Bad : ℝ → Set Ω} {Loc : ℕ → Set Ω}
    (hsplit : ∀ (ε : ℝ) (J : ℕ), F ∩ (E ε)ᶜ ⊆ Bad ε ∪ Loc J)
    (hBad : Tendsto (fun ε => P (Bad ε)) (𝓝[>] 0) (𝓝 0))
    (hLoc : ∀ η : ℝ≥0∞, 0 < η → ∃ J : ℕ, P (Loc J) ≤ η) :
    Tendsto (fun ε => P (F ∩ (E ε)ᶜ)) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  have hη : (0 : ℝ≥0∞) < κ / 2 := ENNReal.div_pos hκ.ne' (by norm_num)
  obtain ⟨J, hJ⟩ := hLoc (κ / 2) hη
  have hB := ENNReal.tendsto_nhds_zero.1 hBad (κ / 2) hη
  filter_upwards [hB] with ε hε
  calc P (F ∩ (E ε)ᶜ) ≤ P (Bad ε ∪ Loc J) := measure_mono (hsplit ε J)
    _ ≤ P (Bad ε) + P (Loc J) := measure_union_le _ _
    _ ≤ κ / 2 + κ / 2 := add_le_add hε hJ
    _ = κ := ENNReal.add_halves κ

end MatedCRT.S5c
