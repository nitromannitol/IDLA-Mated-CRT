import Mathlib

/-!
# Radius selector

For a scale `0 < δ < 1` the seven-adic candidates are the radii `7^{-n}` with `n` in
`[n₋, n₊]`, where `L = log (1/δ)`, `n₋ = ⌈L / (2 log 7)⌉`, `n₊ = ⌊L / log 7⌋`
(the block after the definition of `K`). The selector
`R_δ(z)` takes the least candidate exponent `n` whose good predicate holds at `z`, and the default
`δ` when there is none (line 685: "give it the default `R_z = δ` if the point is inadmissible
or no good radius exists"). The probabilistic content (which candidates are good) enters only
through the predicate `good`; the range `δ ≤ R_δ(z) ≤ √δ` is deterministic
`R_j ≥ δ` is a lemma about the selector.

Terminology: Armitage-Gardiner (potential theory) for the radii; Gwynne-Miller annulus iteration for
the seven-adic scales.
-/

open scoped Classical

namespace MatedCRT
namespace Uniform68Selector

/-- The lower candidate exponent `n₋ = ⌈log(1/δ) / (2 log 7)⌉`. -/
noncomputable def nLo (δ : ℝ) : ℤ := ⌈Real.log (1 / δ) / (2 * Real.log 7)⌉

/-- The upper candidate exponent `n₊ = ⌊log(1/δ) / log 7⌋`. -/
noncomputable def nHi (δ : ℝ) : ℤ := ⌊Real.log (1 / δ) / Real.log 7⌋

/-- The candidate exponents `n ∈ [n₋, n₊]`; the candidate radii are `7^{-n}`. -/
noncomputable def candidates (δ : ℝ) : Finset ℤ := Finset.Icc (nLo δ) (nHi δ)

/-- The radius selector `R_δ(z)` for a grid point `z`, given the predicate `good n` ("the candidate
radius `7^{-n}` is a good radius at `z`"): the radius `7^{-n}` for the least good candidate exponent
`n`, and the default `δ` if no candidate is good. -/
noncomputable def selectRadius (δ : ℝ) (good : ℤ → Prop) : ℝ :=
  if h : ((candidates δ).filter good).Nonempty then
    (1 / 7 : ℝ) ^ ((candidates δ).filter good).min' h
  else δ

/-- A candidate exponent `n ∈ [n₋, n₊]` gives a seven-adic radius in `[δ, √δ]`. -/
theorem seven_zpow_mem_Icc {δ : ℝ} (hδ0 : 0 < δ) {n : ℤ} (hlo : nLo δ ≤ n) (hhi : n ≤ nHi δ) :
    δ ≤ (1 / 7 : ℝ) ^ n ∧ (1 / 7 : ℝ) ^ n ≤ Real.sqrt δ := by
  set L : ℝ := Real.log (1 / δ) with hL
  have h7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  -- `n log 7 ≤ L` from `n ≤ ⌊L / log 7⌋`
  have hup : (n : ℝ) * Real.log 7 ≤ L := by
    have h1 : (n : ℝ) ≤ (nHi δ : ℝ) := by exact_mod_cast hhi
    have h2 : (nHi δ : ℝ) ≤ L / Real.log 7 := Int.floor_le _
    have h3 : (n : ℝ) ≤ L / Real.log 7 := h1.trans h2
    rwa [le_div_iff₀ h7] at h3
  -- `L ≤ 2 n log 7` from `n ≥ ⌈L / (2 log 7)⌉`
  have hdown : L ≤ 2 * (n : ℝ) * Real.log 7 := by
    have h1 : (nLo δ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
    have h2 : L / (2 * Real.log 7) ≤ (nLo δ : ℝ) := Int.le_ceil _
    have h3 : L / (2 * Real.log 7) ≤ (n : ℝ) := h2.trans h1
    rw [div_le_iff₀ (by positivity)] at h3
    linarith
  -- express the powers of `1/7` and `δ`, `√δ` as exponentials of `-n log 7`, `-L`, `-L/2`
  have hpow : (1 / 7 : ℝ) ^ n = Real.exp (-((n : ℝ) * Real.log 7)) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 7)]
    congr 1
    rw [one_div, Real.log_inv]
    ring
  have hδe : δ = Real.exp (-L) := by
    rw [hL, one_div, Real.log_inv, neg_neg, Real.exp_log hδ0]
  have hsq : Real.sqrt δ = Real.exp (-L / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq hδ0.le (Real.exp_pos _).le, ← Real.exp_add, hδe]
    congr 1
    ring
  rw [hpow, hsq, hδe]
  constructor
  · apply Real.exp_le_exp.2
    linarith
  · apply Real.exp_le_exp.2
    linarith

/-- **The selector range** (`R_j ≥ δ`): for every good predicate,
`δ ≤ R_δ(z) ≤ √δ`, including the default branch. -/
theorem selectRadius_mem {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (good : ℤ → Prop) :
    δ ≤ selectRadius δ good ∧ selectRadius δ good ≤ Real.sqrt δ := by
  unfold selectRadius
  split_ifs with h
  · have hmem := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hmem
    have hc := hmem.1
    simp only [candidates, Finset.mem_Icc] at hc
    exact seven_zpow_mem_Icc hδ0 hc.1 hc.2
  · refine ⟨le_rfl, ?_⟩
    exact (Real.le_sqrt hδ0.le hδ0.le).2 (by nlinarith)

/-- The selector is at least `δ` (`R_j ≥ δ`). -/
theorem selectRadius_ge {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (good : ℤ → Prop) :
    δ ≤ selectRadius δ good :=
  (selectRadius_mem hδ0 hδ1 good).1

/-- The selector is at most `√δ`. -/
theorem selectRadius_le_sqrt {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (good : ℤ → Prop) :
    selectRadius δ good ≤ Real.sqrt δ :=
  (selectRadius_mem hδ0 hδ1 good).2

end Uniform68Selector
end MatedCRT

#print axioms MatedCRT.Uniform68Selector.seven_zpow_mem_Icc
#print axioms MatedCRT.Uniform68Selector.selectRadius_mem
