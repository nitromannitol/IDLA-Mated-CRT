import MatedCRT.FirstPass.Derived.ProbabilityMeasurePolish

/-!
# A Polish space of data for locally finite measures on the plane

The LQG measure `μ_h` is a locally finite Borel measure on `ℂ`. This file builds a Polish space
`LQGData` whose points encode locally finite measures on `ℂ` through a partition of unity
subordinate to the closed annuli `ann R = {z | R - 1 ≤ ‖z‖ ≤ R + 1}`, `R : ℕ`.

* `tent t = max 0 (1 - |t|)` and `annRho R z = tent (‖z‖ - R)`: continuous, with values in
  `[0, 1]`, vanishing off `ann R`, and `∑_R annRho R z = 1` for every `z` (`hasSum_annRho`).
  A point of `ann R` has norm at least `R - 1` (`le_norm_add_one_of_mem_ann`), so a ball meets
  only finitely many annuli.
* `LQGData = ∀ R : ℕ, ℝ≥0 × ProbabilityMeasure (ann R)` (a mass and a probability measure on each
  annulus), with the product topology and the product `σ`-algebra. Each `ann R` is a compact
  subset of `ℂ`, so `ProbabilityMeasure (ann R)` is Polish with its Borel `σ`-algebra
  (`MatedCRT.polishSpace_probabilityMeasure_of_polish`,
  `MatedCRT.borelSpace_probabilityMeasure_of_polish`); hence `LQGData` is a Polish space whose
  `σ`-algebra is its Borel `σ`-algebra.
* `LQGData.toMeasure d = ∑_R (d R).1 • ι_R* (d R).2`, where `ι_R : ann R → ℂ` is the inclusion,
  is a locally finite measure on `ℂ` for every `d`: the unit ball around `z` meets only the
  annuli with `R < ⌊‖z‖⌋₊ + 3`.
-/

open MeasureTheory Topology
open scoped NNReal ENNReal

noncomputable section

namespace MatedCRT.FirstPass.Derived

/-! ### The annular partition of unity -/

/-- The tent function `t ↦ max 0 (1 - |t|)`, supported in `[-1, 1]`. -/
def tent (t : ℝ) : ℝ := max 0 (1 - |t|)

theorem continuous_tent : Continuous tent :=
  show Continuous fun t : ℝ => max 0 (1 - |t|) from
    continuous_const.max (continuous_const.sub continuous_abs)

theorem tent_nonneg (t : ℝ) : 0 ≤ tent t := by
  unfold tent
  exact le_max_left _ _

theorem tent_le_one (t : ℝ) : tent t ≤ 1 := by
  unfold tent
  exact max_le zero_le_one (by linarith [abs_nonneg t])

theorem tent_eq_zero_of_one_le_abs {t : ℝ} (h : 1 ≤ |t|) : tent t = 0 := by
  unfold tent
  exact max_eq_left (by linarith)

theorem tent_of_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : tent t = 1 - t := by
  unfold tent
  rw [abs_of_nonneg h0]
  exact max_eq_right (by linarith)

theorem tent_of_nonpos {t : ℝ} (h0 : t ≤ 0) (h1 : -1 ≤ t) : tent t = 1 + t := by
  unfold tent
  rw [abs_of_nonpos h0]
  have h : (0 : ℝ) ≤ 1 - -t := by linarith
  rw [max_eq_right h]
  ring

/-- The closed annulus `{z | R - 1 ≤ ‖z‖ ≤ R + 1}` (a closed disc of radius `1` for `R = 0`). -/
def ann (R : ℕ) : Set ℂ := {z | (R : ℝ) - 1 ≤ ‖z‖ ∧ ‖z‖ ≤ R + 1}

theorem mem_ann {R : ℕ} {z : ℂ} : z ∈ ann R ↔ (R : ℝ) - 1 ≤ ‖z‖ ∧ ‖z‖ ≤ R + 1 :=
  Iff.rfl

/-- A point of the annulus `ann R` has norm at least `R - 1`. -/
theorem le_norm_add_one_of_mem_ann {R : ℕ} {z : ℂ} (h : z ∈ ann R) : (R : ℝ) ≤ ‖z‖ + 1 := by
  linarith [(mem_ann.mp h).1]

theorem isClosed_ann (R : ℕ) : IsClosed (ann R) := by
  have h : ann R = {z : ℂ | (R : ℝ) - 1 ≤ ‖z‖} ∩ {z : ℂ | ‖z‖ ≤ R + 1} :=
    Set.ext fun _ => Iff.rfl
  rw [h]
  exact (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)

theorem isCompact_ann (R : ℕ) : IsCompact (ann R) :=
  (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 1)).of_isClosed_subset (isClosed_ann R)
    fun _ hz => mem_closedBall_zero_iff.mpr (mem_ann.mp hz).2

instance compactSpace_ann (R : ℕ) : CompactSpace (ann R) :=
  isCompact_iff_compactSpace.mp (isCompact_ann R)

/-- The partition-of-unity function of the annulus `ann R`: `z ↦ tent (‖z‖ - R)`. -/
def annRho (R : ℕ) (z : ℂ) : ℝ := tent (‖z‖ - R)

theorem continuous_annRho (R : ℕ) : Continuous (annRho R) :=
  continuous_tent.comp (continuous_norm.sub continuous_const)

theorem annRho_nonneg (R : ℕ) (z : ℂ) : 0 ≤ annRho R z :=
  tent_nonneg _

theorem annRho_le_one (R : ℕ) (z : ℂ) : annRho R z ≤ 1 :=
  tent_le_one _

theorem annRho_eq_zero_of_one_le_abs {R : ℕ} {z : ℂ} (h : 1 ≤ |‖z‖ - (R : ℝ)|) :
    annRho R z = 0 :=
  tent_eq_zero_of_one_le_abs h

theorem annRho_eq_zero_of_notMem {R : ℕ} {z : ℂ} (hz : z ∉ ann R) : annRho R z = 0 := by
  simp only [mem_ann, not_and_or, not_le] at hz
  apply annRho_eq_zero_of_one_le_abs
  rcases hz with hz | hz
  · have := neg_le_abs (‖z‖ - (R : ℝ))
    linarith
  · have := le_abs_self (‖z‖ - (R : ℝ))
    linarith

/-- The function `annRho R` vanishes off the annulus `ann R`. -/
theorem mem_ann_of_annRho_ne_zero {R : ℕ} {z : ℂ} (h : annRho R z ≠ 0) : z ∈ ann R := by
  by_contra hz
  exact h (annRho_eq_zero_of_notMem hz)

/-- **The functions `annRho R` form a partition of unity**: `∑_R annRho R z = 1`. With
`n = ⌊‖z‖⌋₊`, `annRho n z = 1 - (‖z‖ - n)`, `annRho (n + 1) z = ‖z‖ - n`, and every other term
vanishes. -/
theorem hasSum_annRho (z : ℂ) : HasSum (fun R => annRho R z) 1 := by
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, (n : ℝ) ≤ ‖z‖ ∧ ‖z‖ < n + 1 :=
    ⟨⌊‖z‖⌋₊, Nat.floor_le (norm_nonneg z), Nat.lt_floor_add_one _⟩
  have hzero : ∀ R ∉ ({n, n + 1} : Finset ℕ), annRho R z = 0 := by
    intro R hR
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hR
    obtain ⟨hR1, hR2⟩ := hR
    apply annRho_eq_zero_of_one_le_abs
    have hcases : R + 1 ≤ n ∨ n + 2 ≤ R := by omega
    rcases hcases with h | h
    · have h' : (R : ℝ) + 1 ≤ n := by exact_mod_cast h
      have := le_abs_self (‖z‖ - (R : ℝ))
      linarith
    · have h' : (n : ℝ) + 2 ≤ R := by exact_mod_cast h
      have := neg_le_abs (‖z‖ - (R : ℝ))
      linarith
  have e1 : annRho n z = 1 - (‖z‖ - n) := tent_of_nonneg (by linarith) (by linarith)
  have e2 : annRho (n + 1) z = 1 + (‖z‖ - ((n + 1 : ℕ) : ℝ)) :=
    tent_of_nonpos (by push_cast; linarith) (by push_cast; linarith)
  have hsum : ∑ R ∈ ({n, n + 1} : Finset ℕ), annRho R z = 1 := by
    rw [Finset.sum_pair (show n ≠ n + 1 by omega), e1, e2]
    push_cast
    ring
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero hzero

/-! ### The space `LQGData` -/

instance polishSpace_ann (R : ℕ) : PolishSpace (ann R) :=
  (isClosed_ann R).polishSpace

instance polishSpace_probabilityMeasure_ann (R : ℕ) : PolishSpace (ProbabilityMeasure (ann R)) :=
  polishSpace_probabilityMeasure_of_polish (ann R)

instance borelSpace_probabilityMeasure_ann (R : ℕ) : BorelSpace (ProbabilityMeasure (ann R)) :=
  borelSpace_probabilityMeasure_of_polish (ann R)

/-- **Data of a locally finite measure on `ℂ`**: for each annulus `ann R`, a mass in `ℝ≥0` and a
Borel probability measure on `ann R`. It carries the product topology (convergence in
distribution in each probability coordinate) and the product `σ`-algebra. -/
abbrev LQGData : Type := ∀ R : ℕ, ℝ≥0 × ProbabilityMeasure (ann R)

/-- `LQGData` is a Polish space: a countable product of the Polish spaces
`ℝ≥0 × ProbabilityMeasure (ann R)`. -/
instance polishSpace_lqgData : PolishSpace LQGData :=
  inferInstance

/-- The product `σ`-algebra of `LQGData` is its Borel `σ`-algebra. -/
instance borelSpace_lqgData : BorelSpace LQGData :=
  inferInstance

example : TopologicalSpace.PseudoMetrizableSpace LQGData := inferInstance

example : SecondCountableTopology LQGData := inferInstance

example : BorelSpace LQGData := inferInstance

/-- The measure on `ℂ` encoded by `d : LQGData`: `∑_R (d R).1 • ι_R* (d R).2`, where
`ι_R : ann R → ℂ` is the inclusion. -/
def LQGData.toMeasure (d : LQGData) : Measure ℂ :=
  Measure.sum fun R => ((d R).1 : ℝ≥0∞) • ((d R).2 : Measure (ann R)).map Subtype.val

/-- The unit ball around `z` has finite `d.toMeasure`-measure: it meets only the annuli
`ann R` with `R < ⌊‖z‖⌋₊ + 3`, and each of them carries the mass `(d R).1`. -/
theorem LQGData.toMeasure_ball_lt_top (d : LQGData) (z : ℂ) :
    d.toMeasure (Metric.ball z 1) < ∞ := by
  have hn : ‖z‖ < ⌊‖z‖⌋₊ + 1 := Nat.lt_floor_add_one _
  have hvan : ∀ R ∉ Finset.range (⌊‖z‖⌋₊ + 3),
      (((d R).1 : ℝ≥0∞) • ((d R).2 : Measure (ann R)).map Subtype.val) (Metric.ball z 1) = 0 := by
    intro R hR
    rw [Finset.mem_range, not_lt] at hR
    have hR' : (⌊‖z‖⌋₊ : ℝ) + 3 ≤ R := by exact_mod_cast hR
    have hempty : (Subtype.val ⁻¹' Metric.ball z 1 : Set (ann R)) = ∅ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false, mem_ball_iff_norm]
      intro hw
      have h1 := le_norm_add_one_of_mem_ann w.2
      have h2 := norm_sub_norm_le (w : ℂ) z
      linarith
    rw [Measure.smul_apply, Measure.map_apply measurable_subtype_coe
      Metric.isOpen_ball.measurableSet, hempty, measure_empty, smul_zero]
  rw [LQGData.toMeasure, Measure.sum_apply _ Metric.isOpen_ball.measurableSet, tsum_eq_sum hvan]
  refine lt_of_le_of_lt (Finset.sum_le_sum (g := fun R => ((d R).1 : ℝ≥0∞)) fun R _ => ?_) ?_
  · rw [Measure.smul_apply, Measure.map_apply measurable_subtype_coe
      Metric.isOpen_ball.measurableSet, smul_eq_mul]
    exact mul_le_of_le_one_right zero_le prob_le_one
  · rw [← ENNReal.ofNNReal_finsetSum]
    exact ENNReal.coe_lt_top

/-- **The encoded measure is locally finite** for every `d : LQGData`. -/
instance LQGData.isLocallyFiniteMeasure_toMeasure (d : LQGData) :
    IsLocallyFiniteMeasure d.toMeasure :=
  ⟨fun z => ⟨Metric.ball z 1, Metric.ball_mem_nhds z one_pos, d.toMeasure_ball_lt_top z⟩⟩

end MatedCRT.FirstPass.Derived

end
