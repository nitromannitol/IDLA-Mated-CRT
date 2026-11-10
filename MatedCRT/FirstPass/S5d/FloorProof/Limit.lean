import Mathlib

/-!
# The epsilon-n limit behind the outer-probability conclusion of the floor (task fp-S5d-5-1, floor note Part I, Step 9)

Pure measure-theoretic bookkeeping for `notes/fp-gaps/CHATGPT-z5-floor.md`, Section 9, equations (25)-(26): a family of
probabilities `f ε` is bounded, for every fixed index `n`, by `h n + q n ε` where `q n ε → 0` as `ε → 0⁺` (the finitely
many good events of Section 7 at the fixed index `n`) and `h n → 0` as `n → ∞` (the localization `P(L_n^c) → 0`,
equation (17)). Then `f ε → 0`. No measure theory beyond the union bound is used here.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MatedCRT

namespace FloorProof

/-- The epsilon-n limit (floor note, Section 9, (25)-(26)): if `f ≤ h n + q n` eventually for each `n`, where
`q n → 0` along the filter `l` for each `n` and `h n → 0` as `n → ∞`, then `f → 0` along `l`. -/
theorem tendsto_zero_of_le_add {α : Type*} {l : Filter α} [l.NeBot] {f : α → ℝ≥0∞}
    {h : ℕ → ℝ≥0∞} {q : ℕ → α → ℝ≥0∞}
    (hh : Tendsto h atTop (𝓝 0)) (hq : ∀ n, Tendsto (q n) l (𝓝 0))
    (hf : ∀ n, ∀ᶠ x in l, f x ≤ h n + q n x) : Tendsto f l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨n, hn⟩ := (hh.eventually (gt_mem_nhds he2)).exists
  filter_upwards [hf n, ENNReal.tendsto_nhds_zero.1 (hq n) (e / 2) he2] with x hx1 hx2
  calc f x ≤ h n + q n x := hx1
    _ ≤ e / 2 + e / 2 := add_le_add hn.le hx2
    _ = e := ENNReal.add_halves e

/-- The union bound used in (25): an event contained in a union of three events has measure at most the sum of their
measures (outer measure of the ambient measure). -/
theorem measure_le_three {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A B C D : Set Ω)
    (h : A ⊆ B ∪ C ∪ D) : P A ≤ P B + P C + P D := by
  calc P A ≤ P (B ∪ C ∪ D) := measure_mono h
    _ ≤ P (B ∪ C) + P D := measure_union_le _ _
    _ ≤ P B + P C + P D := add_le_add_left (measure_union_le _ _) _

end FloorProof

end MatedCRT
