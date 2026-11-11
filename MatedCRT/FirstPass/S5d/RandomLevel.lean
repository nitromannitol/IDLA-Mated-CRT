import MatedCRT.Defs.Notation

/-!
# A random level from fixed levels

The ceiling of the stopped clause of Proposition 5.1 (`S5d/StoppedExitInput.lean`) is the bound `u^ε ≤ c/(2ε)` off the
killing set with a positive random constant `c`. The written source ([C21], corrected tex 2364) gives it at every fixed level
`κ/(2ε)` (`ε M_ε → 0` in probability), and this file turns the fixed levels into the random one. Pure measure theory; no
stochastic input.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- **Random level from fixed levels.** Let `Lv ε x ω` be an event monotone in the level `x`. If, for every `κ > 0`,
`Lv ε (κ/(2ε))` holds with probability tending to one on `F` (as `ε → 0⁺`), then `Lv ε (c ω/(2ε))` holds with probability tending
to one on `F`, for a positive random `c` whose sublevel sets `{c < κ}` are null-measurable. -/
theorem tendsToOneOn_randomLevel {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Set Ω} {c : Ω → ℝ} (hcpos : ∀ ω, 0 < c ω) (hcm : ∀ κ : ℝ, 0 < κ → NullMeasurableSet {ω | c ω < κ} P)
    {Lv : ℝ → ℝ → Ω → Prop} (hmono : ∀ (ε : ℝ) (ω : Ω) (x y : ℝ), x ≤ y → Lv ε x ω → Lv ε y ω)
    (hκ : ∀ κ : ℝ, 0 < κ → TendsToOneOn P F fun ε => {ω | Lv ε (κ / (2 * ε)) ω}) :
    TendsToOneOn P F fun ε => {ω | Lv ε (c ω / (2 * ε)) ω} := by
  -- the sublevel sets `{c < 1/(n+1)}` decrease to the empty set, so their probabilities tend to zero
  have hanti : Antitone (fun n : ℕ => {ω | c ω < 1 / ((n : ℝ) + 1)}) := by
    intro m n hmn ω hω
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    exact lt_of_lt_of_le hω (one_div_le_one_div_of_le hpos hmn')
  have hlim : Tendsto (fun n : ℕ => P {ω | c ω < 1 / ((n : ℝ) + 1)}) atTop
      (𝓝 (P (⋂ n : ℕ, {ω | c ω < 1 / ((n : ℝ) + 1)}))) :=
    tendsto_measure_iInter_atTop (fun n => hcm _ (by positivity)) hanti ⟨0, measure_ne_top P _⟩
  have hempty : (⋂ n : ℕ, {ω | c ω < 1 / ((n : ℝ) + 1)}) = ∅ := by
    ext ω
    simp only [mem_iInter, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hcpos ω)
    exact ⟨n, hn.le⟩
  rw [hempty, measure_empty] at hlim
  -- the ε-estimate
  unfold TendsToOneOn at hκ ⊢
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.half_pos hη.ne'))).exists
  have hκpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hh := ENNReal.tendsto_nhds_zero.1 (hκ _ hκpos) (η / 2) (ENNReal.half_pos hη.ne')
  filter_upwards [hh, self_mem_nhdsWithin] with ε hε hεpos
  have hεpos' : 0 < ε := hεpos
  have hsub : F ∩ {ω | Lv ε (c ω / (2 * ε)) ω}ᶜ ⊆
      (F ∩ {ω | Lv ε (1 / ((n : ℝ) + 1) / (2 * ε)) ω}ᶜ) ∪ {ω | c ω < 1 / ((n : ℝ) + 1)} := by
    rintro ω ⟨hF, hnL⟩
    by_cases hc : c ω < 1 / ((n : ℝ) + 1)
    · exact Or.inr hc
    · left
      refine ⟨hF, fun hL => hnL (hmono ε ω _ _ ?_ hL)⟩
      exact div_le_div_of_nonneg_right (not_lt.1 hc) (by linarith)
  calc P (F ∩ {ω | Lv ε (c ω / (2 * ε)) ω}ᶜ)
      ≤ P (F ∩ {ω | Lv ε (1 / ((n : ℝ) + 1) / (2 * ε)) ω}ᶜ) + P {ω | c ω < 1 / ((n : ℝ) + 1)} :=
        le_trans (measure_mono hsub) (measure_union_le _ _)
    _ ≤ η / 2 + η / 2 := add_le_add hε hn.le
    _ = η := ENNReal.add_halves η

end MatedCRT
