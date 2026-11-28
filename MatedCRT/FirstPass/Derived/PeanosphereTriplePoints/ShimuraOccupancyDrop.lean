import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancySteps

/-!
# Basic facts on the drops across a cell

For a continuous function `f` and `a ≤ b`, the drop `⨆ s ∈ [a, b], (f b - f s)` is the supremum
of a continuous function on the compact interval, so it is bounded, non-negative, and attained.
Consequently `x < drop` holds if and only if some `s ∈ [a, b]` has `x < f b - f s`, and
`drop ≤ x` if and only if every `s ∈ [a, b]` has `f b - f s ≤ x`.

These facts are specialised to the drops `cellDropR n k` and `cellDropL n k` of the second and
first coordinate of a path across the cell `[(k - 1)/n, k/n]` (no condition on `n` is needed, since
for `n = 0` the cell is the single point `0`).  The drops are measurable functions of the path,
since `{drop ≤ x}` is an intersection of closed sets, and therefore the events `tameEvent` and
`pastEvent` are measurable.
-/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT (Path2)

namespace MatedCRT.PeanosphereTriplePoints

/-! ### The drop of a continuous function over an interval -/

/-- The drops of a continuous function over `[a, b]` are bounded above. -/
theorem bddAbove_range_sub {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    BddAbove (range fun s : Icc a b => f b - f s) :=
  (isCompact_range (by fun_prop : Continuous fun s : Icc a b => f b - f (s : ℝ))).bddAbove

/-- The supremum of the drops of a continuous function over `[a, b]` is non-negative. -/
theorem iSup_sub_nonneg {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ⨆ s : Icc a b, (f b - f s) := by
  have := le_ciSup (bddAbove_range_sub hf a b) (⟨b, hab, le_rfl⟩ : Icc a b)
  simpa using this

/-- The supremum of the drops of a continuous function over `[a, b]` is attained. -/
theorem exists_eq_iSup_sub {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    ∃ s ∈ Icc a b, (⨆ s : Icc a b, (f b - f s)) = f b - f s := by
  have : Nonempty (Icc a b) := ⟨⟨b, hab, le_rfl⟩⟩
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab)
    (by fun_prop : Continuous fun s : ℝ => f b - f s).continuousOn
  refine ⟨s, hs, le_antisymm (ciSup_le fun y => hmax y.2) ?_⟩
  exact le_ciSup (bddAbove_range_sub hf a b) (⟨s, hs⟩ : Icc a b)

/-- `x` is below the supremum of the drops if and only if it is below one of them. -/
theorem lt_iSup_sub_iff {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    x < (⨆ s : Icc a b, (f b - f s)) ↔ ∃ s ∈ Icc a b, x < f b - f s := by
  constructor
  · intro h
    obtain ⟨s, hs, he⟩ := exists_eq_iSup_sub hf hab
    exact ⟨s, hs, he ▸ h⟩
  · rintro ⟨s, hs, h⟩
    exact h.trans_le (le_ciSup (bddAbove_range_sub hf a b) (⟨s, hs⟩ : Icc a b))

/-- The supremum of the drops is at most `x` if and only if every drop is. -/
theorem iSup_sub_le_iff {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    (⨆ s : Icc a b, (f b - f s)) ≤ x ↔ ∀ s ∈ Icc a b, f b - f s ≤ x := by
  rw [← not_lt, lt_iSup_sub_iff hf hab]
  simp only [not_exists, not_and, not_lt]

/-! ### The drops across a cell -/

theorem cell_le (n k : ℕ) : ((k : ℝ) - 1) / n ≤ (k : ℝ) / n :=
  div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg n)

theorem continuous_snd_path (p : Path2) : Continuous fun t : ℝ => (p t).2 :=
  continuous_snd.comp p.continuous

theorem continuous_fst_path (p : Path2) : Continuous fun t : ℝ => (p t).1 :=
  continuous_fst.comp p.continuous

/-- The drops of the second coordinate across a cell are bounded above. -/
theorem bddAbove_cellDropR (n k : ℕ) (p : Path2) :
    BddAbove (range fun s : Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n) =>
      (p ((k : ℝ) / n)).2 - (p s).2) :=
  bddAbove_range_sub (continuous_snd_path p) _ _

/-- The drops of the first coordinate across a cell are bounded above. -/
theorem bddAbove_cellDropL (n k : ℕ) (p : Path2) :
    BddAbove (range fun s : Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n) =>
      (p ((k : ℝ) / n)).1 - (p s).1) :=
  bddAbove_range_sub (continuous_fst_path p) _ _

/-- The drop of the second coordinate across a cell is non-negative. -/
theorem cellDropR_nonneg (n k : ℕ) (p : Path2) : 0 ≤ cellDropR n k p :=
  iSup_sub_nonneg (continuous_snd_path p) (cell_le n k)

/-- The drop of the first coordinate across a cell is non-negative. -/
theorem cellDropL_nonneg (n k : ℕ) (p : Path2) : 0 ≤ cellDropL n k p :=
  iSup_sub_nonneg (continuous_fst_path p) (cell_le n k)

/-- The drop of the second coordinate across a cell is attained at a point of the cell. -/
theorem exists_eq_cellDropR (n k : ℕ) (p : Path2) :
    ∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
      cellDropR n k p = (p ((k : ℝ) / n)).2 - (p s).2 :=
  exists_eq_iSup_sub (continuous_snd_path p) (cell_le n k)

/-- The drop of the first coordinate across a cell is attained at a point of the cell. -/
theorem exists_eq_cellDropL (n k : ℕ) (p : Path2) :
    ∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
      cellDropL n k p = (p ((k : ℝ) / n)).1 - (p s).1 :=
  exists_eq_iSup_sub (continuous_fst_path p) (cell_le n k)

/-- The drop of the second coordinate exceeds `x` if and only if some point of the cell has a drop
exceeding `x`. -/
theorem lt_cellDropR_iff (n k : ℕ) (p : Path2) (x : ℝ) :
    x < cellDropR n k p ↔
      ∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n), x < (p ((k : ℝ) / n)).2 - (p s).2 :=
  lt_iSup_sub_iff (continuous_snd_path p) (cell_le n k) x

/-- The drop of the first coordinate exceeds `x` if and only if some point of the cell has a drop
exceeding `x`. -/
theorem lt_cellDropL_iff (n k : ℕ) (p : Path2) (x : ℝ) :
    x < cellDropL n k p ↔
      ∃ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n), x < (p ((k : ℝ) / n)).1 - (p s).1 :=
  lt_iSup_sub_iff (continuous_fst_path p) (cell_le n k) x

/-- The drop of the second coordinate is at most `x` if and only if every point of the cell has a
drop at most `x`. -/
theorem cellDropR_le_iff (n k : ℕ) (p : Path2) (x : ℝ) :
    cellDropR n k p ≤ x ↔
      ∀ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n), (p ((k : ℝ) / n)).2 - (p s).2 ≤ x :=
  iSup_sub_le_iff (continuous_snd_path p) (cell_le n k) x

/-- The drop of the first coordinate is at most `x` if and only if every point of the cell has a
drop at most `x`. -/
theorem cellDropL_le_iff (n k : ℕ) (p : Path2) (x : ℝ) :
    cellDropL n k p ≤ x ↔
      ∀ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n), (p ((k : ℝ) / n)).1 - (p s).1 ≤ x :=
  iSup_sub_le_iff (continuous_fst_path p) (cell_le n k) x

/-! ### Measurability -/

/-- The set of paths whose drop over a cell is at most `x` is closed. -/
theorem isClosed_drop_le (g : ℝ × ℝ → ℝ) (hg : Continuous g) (a b x : ℝ) :
    IsClosed {p : Path2 | ∀ s ∈ Icc a b, g (p b) - g (p s) ≤ x} := by
  have hev : Continuous fun q : Path2 × ℝ => q.1 q.2 := ContinuousEval.continuous_eval
  have : {p : Path2 | ∀ s ∈ Icc a b, g (p b) - g (p s) ≤ x} =
      ⋂ s ∈ Icc a b, {p : Path2 | g (p b) - g (p s) ≤ x} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
  rw [this]
  refine isClosed_biInter fun s _ => isClosed_le ?_ continuous_const
  have h1 : Continuous fun p : Path2 => p b := hev.comp (continuous_id.prodMk continuous_const)
  have h2 : Continuous fun p : Path2 => p s := hev.comp (continuous_id.prodMk continuous_const)
  exact (hg.comp h1).sub (hg.comp h2)

/-- The drop of the second coordinate across a cell is a measurable function of the path. -/
theorem measurable_cellDropR (n k : ℕ) : Measurable (cellDropR n k) := by
  refine measurable_of_Iic fun x => ?_
  have : cellDropR n k ⁻¹' Iic x =
      {p : Path2 | ∀ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
        (fun y : ℝ × ℝ => y.2) (p ((k : ℝ) / n)) - (fun y : ℝ × ℝ => y.2) (p s) ≤ x} := by
    ext p
    exact cellDropR_le_iff n k p x
  rw [this]
  exact (isClosed_drop_le (fun y : ℝ × ℝ => y.2) continuous_snd _ _ x).measurableSet

/-- The drop of the first coordinate across a cell is a measurable function of the path. -/
theorem measurable_cellDropL (n k : ℕ) : Measurable (cellDropL n k) := by
  refine measurable_of_Iic fun x => ?_
  have : cellDropL n k ⁻¹' Iic x =
      {p : Path2 | ∀ s ∈ Icc (((k : ℝ) - 1) / n) ((k : ℝ) / n),
        (fun y : ℝ × ℝ => y.1) (p ((k : ℝ) / n)) - (fun y : ℝ × ℝ => y.1) (p s) ≤ x} := by
    ext p
    exact cellDropL_le_iff n k p x
  rw [this]
  exact (isClosed_drop_le (fun y : ℝ × ℝ => y.1) continuous_fst _ _ x).measurableSet

/-- The event `F` that both drops across the cell are small is measurable. -/
theorem measurableSet_tameEvent (n k j : ℕ) : MeasurableSet (tameEvent n k j) :=
  (measurableSet_le (measurable_cellDropR n k) measurable_const).inter
    (measurableSet_le (measurable_cellDropL n k) measurable_const)

/-- The past event `C_k` is measurable. -/
theorem measurableSet_pastEvent (n k : ℕ) : MeasurableSet (pastEvent n k) :=
  measurableSet_priorCellsFail n k

end MatedCRT.PeanosphereTriplePoints
