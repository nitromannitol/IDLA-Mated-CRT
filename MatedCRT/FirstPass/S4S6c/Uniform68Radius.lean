import MatedCRT.FirstPass.S4S6c.Uniform68Local

/-!
# The selected good radius of a band centre (q2, task fp-S4S6c-envscaling-6-7-6-8, config-level assembly)

The config-level test `Uniform68.config_exit_lower_bound` takes a radius `rad y` for each band centre `ctr y`, with
`rad y` a good seven-adic radius (`IsGoodAnnulusEvent`, Defs/Setting.lean:333). The good-annulus cover event
(`GoodRadiusCover.lean:47`) gives, for each centre, a good radius `r ∈ [δ, √δ]` of the form `7^{-n}` (natural `n`).

* `candidates_of_mem`: such an `n` lies in the selector's candidate range `candidates δ` (`Uniform68Selector`);
* `radiusAt`: the selector `selectRadius` applied to the good predicate of the centre `z`;
* `radiusAt_good`: `radiusAt μ c0 C δ z` lies in `[δ, √δ]` and is a good radius for `z`, whenever the cover holds at `z`.

Terminology: Gwynne-Miller annulus iteration (seven-adic radii); good annulus (Duplantier-Sheffield, Berestycki-Powell).
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace MatedCRT.Uniform68Radius

open Uniform68Selector

/-- A seven-adic radius `δ ≤ (1/7)^n ≤ √δ` has its exponent in the candidate range. -/
theorem candidates_of_mem {δ : ℝ} {n : ℤ} (hδ0 : 0 < δ) (h1 : δ ≤ (1 / 7 : ℝ) ^ n)
    (h2 : (1 / 7 : ℝ) ^ n ≤ Real.sqrt δ) : n ∈ candidates δ := by
  have h7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have hlog1 : Real.log ((1 / 7 : ℝ) ^ n) = -(n * Real.log 7) := by
    rw [Real.log_zpow, one_div, Real.log_inv]
    ring
  have hlo : Real.log δ ≤ Real.log ((1 / 7 : ℝ) ^ n) := Real.log_le_log hδ0 h1
  have hhi : Real.log ((1 / 7 : ℝ) ^ n) ≤ Real.log (Real.sqrt δ) :=
    Real.log_le_log (by positivity) h2
  rw [Real.log_sqrt hδ0.le] at hhi
  rw [hlog1] at hlo hhi
  unfold candidates nLo nHi
  rw [Finset.mem_Icc]
  constructor
  · -- ⌈L / (2 log 7)⌉ ≤ n, from n log 7 ≥ L / 2 with L = log(1/δ) = -log δ
    apply Int.ceil_le.2
    have hL : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
    rw [hL, div_le_iff₀ (by positivity)]
    have : (n : ℝ) * Real.log 7 ≥ -Real.log δ / 2 := by linarith
    linarith
  · -- n ≤ ⌊L / log 7⌋, from n log 7 ≤ L
    apply Int.le_floor.2
    have hL : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
    rw [hL, le_div_iff₀ h7]
    linarith

/-- The selector's radius at a centre `z`: `selectRadius δ` for the good predicate `n ↦ IsGoodAnnulusEvent` at `7^{-n}`. -/
noncomputable def radiusAt (μ : Measure ℂ) (c0 C δ : ℝ) (z : ℂ) : ℝ :=
  selectRadius δ (fun n : ℤ => IsGoodAnnulusEvent μ c0 C ((1 / 7 : ℝ) ^ n) z)

/-- **The selected radius is a good radius of the centre.** If the good-annulus cover holds at `z` (some good radius
`r ∈ [δ, √δ]` of the form `7^{-n}`, `n` natural), then `radiusAt μ c0 C δ z ∈ [δ, √δ]` and it is a good radius for `z`. -/
theorem radiusAt_good {μ : Measure ℂ} {c0 C δ : ℝ} {z : ℂ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hcov : ∃ r : ℝ, δ ≤ r ∧ r ≤ Real.sqrt δ ∧ (∃ n : ℕ, r = ((7 : ℝ)⁻¹) ^ n) ∧
      IsGoodAnnulusEvent μ c0 C r z) :
    δ ≤ radiusAt μ c0 C δ z ∧ radiusAt μ c0 C δ z ≤ Real.sqrt δ ∧
      IsGoodAnnulusEvent μ c0 C (radiusAt μ c0 C δ z) z := by
  obtain ⟨r, hr1, hr2, ⟨n, rfl⟩, hg⟩ := hcov
  have e : ((7 : ℝ)⁻¹) ^ n = (1 / 7 : ℝ) ^ (n : ℤ) := by
    rw [one_div, zpow_natCast]
  have hr1' : δ ≤ (1 / 7 : ℝ) ^ (n : ℤ) := by rw [← e]; exact hr1
  have hr2' : (1 / 7 : ℝ) ^ (n : ℤ) ≤ Real.sqrt δ := by rw [← e]; exact hr2
  have hg' : IsGoodAnnulusEvent μ c0 C ((1 / 7 : ℝ) ^ (n : ℤ)) z := by rw [← e]; exact hg
  have hmem : (n : ℤ) ∈ candidates δ := candidates_of_mem hδ0 hr1' hr2'
  obtain ⟨k, -, hk, heq⟩ := Uniform68Local.selectRadius_good (δ := δ)
    (fun n : ℤ => IsGoodAnnulusEvent μ c0 C ((1 / 7 : ℝ) ^ n) z) ⟨(n : ℤ), hmem, hg'⟩
  have hb := selectRadius_mem hδ0 hδ1 (fun n : ℤ => IsGoodAnnulusEvent μ c0 C ((1 / 7 : ℝ) ^ n) z)
  unfold radiusAt
  refine ⟨hb.1, hb.2, ?_⟩
  rw [heq]
  exact hk

end MatedCRT.Uniform68Radius

/-! ## Audit -/

#print axioms MatedCRT.Uniform68Radius.radiusAt_good
