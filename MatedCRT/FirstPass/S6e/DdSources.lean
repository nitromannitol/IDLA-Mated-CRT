import Mathlib
import MatedCRT.FirstPass.S6e.Cutoff
import MatedCRT.FirstPass.S4S6c.DyadicCutoff68
import MatedCRT.FirstPass.S4S6c.GoodRadiusCover

/-!
# FIRST PASS: the Lean sources of the boxed radius `dd` of LEMMA68 (D4) (task fp-S6e-lemma68-C17, z9)

Write-up: `δ* = 2^(-J_A)` (A-section, `notes/fp-gaps/CHATGPT-lemma68-open-parts.md` line 362) is field measurable,
with a positive deterministic default on `{J_A = ∞}`; `t* = min {2^(-(J_V+3)), (ρ₁-ρ)/8, 1/16}` (line 110) with a
positive default on `{J_V = ∞}`. Their Lean sources: `DyadicCutoff68.exists_dyadic_cutoff` (positive and
`F`-measurable everywhere, for `δ*`) and `GoodRadiusCover.exists_dyadic_threshold` (positive only almost surely,
for `t*`). The null-set modification `exists_pos_measurable_of_ae_pos` makes the latter everywhere positive.
-/

open MeasureTheory Set

namespace MatedCRT

namespace Lemma68DdSources

/-- A field-measurable function that is almost surely positive is modified on a null set to be everywhere
positive: `t' = t` on `{0 < t}` and `t' = 1` elsewhere. Measurability and the almost sure values are kept. -/
theorem exists_pos_measurable_of_ae_pos {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    (t : Ω → ℝ) (ht : Measurable[m] t) (hpos : ∀ᵐ ω ∂P, 0 < t ω) :
    ∃ t' : Ω → ℝ, Measurable[m] t' ∧ (∀ ω, 0 < t' ω) ∧ ∀ᵐ ω ∂P, t' ω = t ω := by
  classical
  refine ⟨fun ω => if 0 < t ω then t ω else 1, ?_, fun ω => ?_, ?_⟩
  · exact Measurable.ite (measurableSet_lt measurable_const ht) ht measurable_const
  · show 0 < (if 0 < t ω then t ω else 1)
    split_ifs with h
    · exact h
    · exact one_pos
  · filter_upwards [hpos] with ω hω
    simp [hω]

/-- The boxed radius of (D4) with its two field-measurable sources, for a probability `Q` on the field
σ-algebra `F` (the convention of `DyadicCutoff68.exists_dyadic_cutoff` and `GoodRadiusCover.exists_dyadic_threshold`).
Output: `dStar`, `tStar` are `F`-measurable and everywhere positive; `ddBoxed r0' p dStar tStar` is `F`-measurable,
everywhere positive and at most `r0'`; `Q`-almost surely both sources keep their witness properties. -/
theorem exists_ddBoxed_source {Ω : Type*} {F : MeasurableSpace Ω} (Q : Measure Ω) [IsProbabilityMeasure Q]
    (E1 : ℝ → Set Ω) (hE1 : ∀ δ, MeasurableSet[F] (E1 δ))
    (hpoly1 : HarmonicBalls.PolyHighProb Q E1) (E2 : ℝ → Set Ω)
    (hE2 : ∀ n : ℕ, MeasurableSet[F] (E2 ((1 / 2 : ℝ) ^ n))) (hpoly2 : HarmonicBalls.PolyHighProb Q E2)
    (r0' p : ℝ) (hr0 : 0 < r0') :
    ∃ dStar tStar : Ω → ℝ, Measurable[F] dStar ∧ (∀ ω, 0 < dStar ω) ∧ Measurable[F] tStar ∧
      (∀ ω, 0 < tStar ω) ∧ Measurable[F] (Lemma68Cutoff.ddBoxed r0' p dStar tStar) ∧
      (∀ ω, 0 < Lemma68Cutoff.ddBoxed r0' p dStar tStar ω) ∧
      (∀ ω, Lemma68Cutoff.ddBoxed r0' p dStar tStar ω ≤ r0') ∧
      ∀ᵐ ω ∂Q, (∀ δ : ℝ, 0 < δ → δ ≤ dStar ω → ∃ δ' : ℝ, δ / 2 ≤ δ' ∧ δ' ≤ δ ∧ ω ∈ E1 δ') ∧
        (∀ n : ℕ, (1 / 2 : ℝ) ^ n < tStar ω → ω ∈ E2 ((1 / 2 : ℝ) ^ n)) := by
  obtain ⟨dStar, hdm, hdpos, hdae⟩ := DyadicCutoff68.exists_dyadic_cutoff Q E1 hE1 hpoly1
  obtain ⟨t0, ht0m, ht0ae⟩ := GoodRadiusCover.exists_dyadic_threshold E2 hE2 hpoly2
  obtain ⟨tStar, htm, htpos, htae⟩ := exists_pos_measurable_of_ae_pos Q t0 ht0m (ht0ae.mono fun ω h => h.1)
  refine ⟨dStar, tStar, hdm, hdpos, htm, htpos, Lemma68Cutoff.measurable_ddBoxed hdm htm,
    fun ω => Lemma68Cutoff.ddBoxed_pos hr0 hdpos htpos ω, fun ω => Lemma68Cutoff.ddBoxed_le_r0 ω, ?_⟩
  filter_upwards [hdae, htae, ht0ae] with ω h1 h2 h3
  exact ⟨h1, fun n hn => h3.2 n (by rw [← h2]; exact hn)⟩

end Lemma68DdSources

end MatedCRT
