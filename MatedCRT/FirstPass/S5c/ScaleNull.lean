import Mathlib

/-!
# FIRST PASS, stopped clause of 5.1: the scale-invariance null argument (G-stopped Gap 1 repair)

Pure real analysis for the fixed-deterministic-time assertion of the Gap 1 repair (CHATGPT-stopped-repair-check.md,
item 1-4): if the probability `P (E t)` of the new-mass event is invariant under dilation of the time (the printed
scaling of the cone family, IDLA lines 597-602, combined with law invariance: an external input) and only countably
many times `t` have `P (E t) > 0` (the atoms of the entrance-time laws), then `P (E t) = 0` for every `t > 0`.
No measurability of `E t` is used: the statement is about the values `P (E t) ∈ ℝ≥0∞` of the outer measure.
-/

namespace MatedCRT.S5c

open MeasureTheory Set

/-- The half-line `(0, ∞)` is uncountable: otherwise `ℝ = log (0, ∞)` would be countable. -/
theorem not_countable_Ioi_zero : ¬ (Set.Ioi (0 : ℝ)).Countable := fun h =>
  Cardinal.not_countable_real (Set.Countable.mono
    (show (Set.univ : Set ℝ) ⊆ Real.log '' Set.Ioi 0 from
      fun x _ => ⟨Real.exp x, Real.exp_pos x, Real.log_exp x⟩)
    (h.image Real.log))

/-- **Scale-invariance null argument** (G-stopped Gap 1 repair): a dilation-invariant family of measures of events with
countably many positive values is null at every positive time. -/
theorem null_of_scale_invariant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → Set Ω)
    (hscale : ∀ b t : ℝ, 0 < b → 0 < t → P (E (b * t)) = P (E t))
    (hcount : {t : ℝ | 0 < P (E t)}.Countable) (t : ℝ) (ht : 0 < t) : P (E t) = 0 := by
  by_contra hne
  have hpos : 0 < P (E t) := pos_iff_ne_zero.2 hne
  have hall : Set.Ioi (0 : ℝ) ⊆ {s : ℝ | 0 < P (E s)} := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have e : P (E s) = P (E t) := by
      have h := hscale (s / t) t (div_pos hs' ht) ht
      rwa [div_mul_cancel₀ s ht.ne'] at h
    show 0 < P (E s)
    rw [e]
    exact hpos
  exact not_countable_Ioi_zero (Set.Countable.mono hall hcount)

end MatedCRT.S5c
