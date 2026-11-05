import Mathlib

/-!
# Riemann sums of integrals of a path along a level function (eq:gff, `ConeMeanZeroRestrictionStep`)

Let `ν` be a measure on `α`, `g ∈ L¹(ν)` a weight and `s : α → ℝ` a measurable level function. For a path
`w : ℝ → ℝ` consider the *level integral* `∫ g(x) w(s(x)) dν(x)`. For the lateral part of a field `h` this is the
pairing of an observable (Lebesgue measure with a test function as weight, or a circle measure) with the radial
part `x ↦ h_{|x|}(0)`, where `s(x) = -log |x|` and `w(s) = h_{e^{-s}}(0)` is the radial process.

The level integral is an iterated limit of finite linear combinations of values of `w`, the Riemann sums
`R_{n,k}(w) = ∑_{|j| ≤ Nk} c_j w(j/N)`, `N = n + 1`, with weights `c_j = ∫_{|s| ≤ k, ⌊N s⌋ = j} g dν`:
* `n → ∞` (`tendsto_levelRiemann`): `R_{n,k}(w)` tends to the truncated integral `∫_{|s| ≤ k} g · w ∘ s dν` for
  `w` continuous, by dominated convergence (`w` is bounded on `[-k-1, k]`);
* `k → ∞` (`tendsto_levelTrunc`): the truncated integrals tend to the level integral when `g · w ∘ s` is integrable.
-/

namespace MatedCRT.Field.Level

open MeasureTheory Filter Topology Set

variable {α : Type*} [MeasurableSpace α]

/-- The level integral `∫ g · w ∘ s dν`. -/
noncomputable def levelIntegral (ν : Measure α) (g s : α → ℝ) (w : ℝ → ℝ) : ℝ := ∫ x, g x * w (s x) ∂ν

/-- The level integral truncated to `|s| ≤ k`. -/
noncomputable def levelTrunc (ν : Measure α) (g s : α → ℝ) (k : ℕ) (w : ℝ → ℝ) : ℝ :=
  ∫ x, {x | |s x| ≤ k}.indicator (fun x => g x * w (s x)) x ∂ν

/-- The cell `{x : |s(x)| ≤ k, ⌊N s(x)⌋ = j}`, `N = n + 1`, of the Riemann sum. -/
def levelCell (s : α → ℝ) (n k : ℕ) (j : ℤ) : Set α := {x | |s x| ≤ k ∧ ⌊s x * (n + 1 : ℕ)⌋ = j}

/-- The index range `|j| ≤ Nk` of the Riemann sum. -/
def levelIndex (n k : ℕ) : Finset ℤ := Finset.Icc (-(((n + 1) * k : ℕ) : ℤ)) (((n + 1) * k : ℕ) : ℤ)

/-- The weight `c_j = ∫_{cell j} g dν` of the Riemann sum. -/
noncomputable def levelWeight (ν : Measure α) (g s : α → ℝ) (n k : ℕ) (j : ℤ) : ℝ :=
  ∫ x in levelCell s n k j, g x ∂ν

/-- The grid point `j / N` of index `j`. -/
noncomputable def gridVal (n : ℕ) (j : ℤ) : ℝ := (j : ℝ) / (n + 1 : ℕ)

/-- The Riemann sum `R_{n,k}(w) = ∑_{|j| ≤ Nk} c_j w(j/N)`: a finite linear combination of values of `w`. -/
noncomputable def levelRiemann (ν : Measure α) (g s : α → ℝ) (n k : ℕ) (w : ℝ → ℝ) : ℝ :=
  ∑ j ∈ levelIndex n k, levelWeight ν g s n k j * w (gridVal n j)

/-- The grid point `⌊N s(x)⌋ / N` below `s(x)`. -/
noncomputable def gridPt (s : α → ℝ) (n : ℕ) (x : α) : ℝ := gridVal n ⌊s x * (n + 1 : ℕ)⌋

variable {s : α → ℝ}

lemma measurable_floor_level (hs : Measurable s) (n : ℕ) : Measurable fun x => ⌊s x * (n + 1 : ℕ)⌋ :=
  Int.measurable_floor.comp (hs.mul_const _)

lemma measurableSet_levelLe (hs : Measurable s) (k : ℕ) : MeasurableSet {x | |s x| ≤ k} :=
  measurableSet_le (continuous_abs.measurable.comp hs) measurable_const

lemma measurableSet_levelCell (hs : Measurable s) (n k : ℕ) (j : ℤ) : MeasurableSet (levelCell s n k j) :=
  (measurableSet_levelLe hs k).inter (measurableSet_eq_fun (measurable_floor_level hs n) measurable_const)

lemma measurable_comp_gridPt (hs : Measurable s) (n : ℕ) (w : ℝ → ℝ) : Measurable fun x => w (gridPt s n x) :=
  (measurable_of_countable (fun j : ℤ => w (gridVal n j))).comp (measurable_floor_level hs n)

lemma natSucc_pos (n : ℕ) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity

omit [MeasurableSpace α] in
lemma gridPt_le (n : ℕ) (x : α) : gridPt s n x ≤ s x := by
  rw [gridPt, gridVal, div_le_iff₀ (natSucc_pos n)]
  exact Int.floor_le _

omit [MeasurableSpace α] in
lemma lt_gridPt (n : ℕ) (x : α) : s x - 1 / ((n + 1 : ℕ) : ℝ) < gridPt s n x := by
  have hn' := natSucc_pos n
  rw [gridPt, gridVal, lt_div_iff₀ hn', sub_mul, one_div, inv_mul_cancel₀ hn'.ne']
  linarith [Int.lt_floor_add_one (s x * ((n + 1 : ℕ) : ℝ))]

omit [MeasurableSpace α] in
lemma tendsto_gridPt (x : α) : Tendsto (fun n => gridPt s n x) atTop (𝓝 (s x)) := by
  have h0 : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have h1 : Tendsto (fun n : ℕ => s x - 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (s x)) := by
    simpa using tendsto_const_nhds.sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds (fun n => (lt_gridPt n x).le)
    (fun n => gridPt_le n x)

omit [MeasurableSpace α] in
/-- On `|s| ≤ k` the grid point lies in `[-k-1, k]`. -/
lemma gridPt_mem_Icc {n k : ℕ} {x : α} (hx : |s x| ≤ k) : gridPt s n x ∈ Icc (-(k : ℝ) - 1) k := by
  have h1 : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (natSucc_pos n)]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  refine ⟨?_, (gridPt_le n x).trans (le_of_abs_le hx)⟩
  linarith [lt_gridPt (s := s) n x, neg_abs_le (s x)]

omit [MeasurableSpace α] in
/-- On `|s| ≤ k` the floor index lies in the index range. -/
lemma floor_mem_levelIndex {n k : ℕ} {x : α} (hx : |s x| ≤ k) : ⌊s x * (n + 1 : ℕ)⌋ ∈ levelIndex n k := by
  have hn := natSucc_pos n
  have hlo : -(((n + 1) * k : ℕ) : ℝ) ≤ s x * (n + 1 : ℕ) := by
    push_cast
    nlinarith [neg_abs_le (s x)]
  have hhi : s x * (n + 1 : ℕ) ≤ (((n + 1) * k : ℕ) : ℝ) := by
    push_cast
    nlinarith [le_abs_self (s x)]
  refine Finset.mem_Icc.2 ⟨?_, ?_⟩
  · exact Int.le_floor.2 (by push_cast at hlo ⊢; linarith)
  · exact Int.floor_le_iff.2 (by push_cast at hhi ⊢; linarith)

omit [MeasurableSpace α] in
/-- The integrand of the Riemann sum is a finite sum of indicators. -/
lemma indicator_gridPt_eq_sum (g : α → ℝ) (n k : ℕ) (w : ℝ → ℝ) (x : α) :
    {x | |s x| ≤ k}.indicator (fun x => g x * w (gridPt s n x)) x =
      ∑ j ∈ levelIndex n k, (levelCell s n k j).indicator g x * w (gridVal n j) := by
  by_cases hx : |s x| ≤ k
  · rw [indicator_of_mem (show x ∈ {x | |s x| ≤ k} from hx)]
    rw [Finset.sum_eq_single_of_mem _ (floor_mem_levelIndex hx)]
    · rw [indicator_of_mem (show x ∈ levelCell s n k _ from ⟨hx, rfl⟩)]
      rfl
    · intro j _ hj
      rw [indicator_of_notMem (fun h => hj h.2.symm), zero_mul]
  · rw [indicator_of_notMem (show x ∉ {x | |s x| ≤ k} from hx)]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [indicator_of_notMem (fun h => hx h.1), zero_mul]

variable {ν : Measure α} {g : α → ℝ}

/-- The Riemann sum is the integral of `g` against the path evaluated at the grid points. -/
lemma levelRiemann_eq_integral (hs : Measurable s) (hg : Integrable g ν) (n k : ℕ) (w : ℝ → ℝ) :
    levelRiemann ν g s n k w = ∫ x, {x | |s x| ≤ k}.indicator (fun x => g x * w (gridPt s n x)) x ∂ν := by
  simp_rw [indicator_gridPt_eq_sum]
  rw [integral_finsetSum _ fun j _ => (hg.indicator (measurableSet_levelCell hs n k j)).mul_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_indicator (measurableSet_levelCell hs n k j)]
  rfl

/-- **`n → ∞`.** For a continuous path, the Riemann sums tend to the truncated level integral. -/
theorem tendsto_levelRiemann (hs : Measurable s) (hg : Integrable g ν) (k : ℕ) {w : ℝ → ℝ}
    (hw : Continuous w) : Tendsto (fun n => levelRiemann ν g s n k w) atTop (𝓝 (levelTrunc ν g s k w)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(k : ℝ) - 1) (b := k)).exists_bound_of_continuousOn hw.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC k ⟨by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)], le_rfl⟩)
  simp_rw [levelRiemann_eq_integral hs hg]
  refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖ * C) (fun n => ?_)
    (hg.norm.mul_const C) (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · exact (hg.1.mul (measurable_comp_gridPt hs n w).aestronglyMeasurable).indicator (measurableSet_levelLe hs k)
  · by_cases hx : |s x| ≤ k
    · rw [indicator_of_mem (show x ∈ {x | |s x| ≤ k} from hx), norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _ (gridPt_mem_Icc hx)) (norm_nonneg _)
    · rw [indicator_of_notMem (show x ∉ {x | |s x| ≤ k} from hx), norm_zero]
      positivity
  · by_cases hx : |s x| ≤ k
    · simp only [indicator_of_mem (show x ∈ {x | |s x| ≤ k} from hx)]
      exact ((hw.tendsto _).comp (tendsto_gridPt x)).const_mul (g x)
    · simp only [indicator_of_notMem (show x ∉ {x | |s x| ≤ k} from hx)]
      exact tendsto_const_nhds

/-- **`k → ∞`.** When `g · w ∘ s` is integrable, the truncated integrals tend to the level integral. -/
theorem tendsto_levelTrunc (hs : Measurable s) {w : ℝ → ℝ} (hint : Integrable (fun x => g x * w (s x)) ν) :
    Tendsto (fun k : ℕ => levelTrunc ν g s k w) atTop (𝓝 (levelIntegral ν g s w)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖g x * w (s x)‖)
    (fun k => (hint.indicator (measurableSet_levelLe hs k)).1) hint.norm
    (fun k => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _)
    (Eventually.of_forall fun x => ?_)
  obtain ⟨N, hN⟩ := exists_nat_ge |s x|
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun k hk => ?_)
  dsimp only
  rw [indicator_of_mem (show x ∈ {x | |s x| ≤ k} from hN.trans (by exact_mod_cast hk))]

/-! ### Linearity and measurability of the Riemann sums -/

lemma levelRiemann_add (ν : Measure α) (g s : α → ℝ) (n k : ℕ) (w w' : ℝ → ℝ) :
    levelRiemann ν g s n k (fun t => w t + w' t) = levelRiemann ν g s n k w + levelRiemann ν g s n k w' := by
  simp only [levelRiemann, mul_add, Finset.sum_add_distrib]

lemma levelRiemann_const_mul (ν : Measure α) (g s : α → ℝ) (n k : ℕ) (c : ℝ) (w : ℝ → ℝ) :
    levelRiemann ν g s n k (fun t => c * w t) = c * levelRiemann ν g s n k w := by
  simp only [levelRiemann, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma measurable_levelRiemann (ν : Measure α) (g s : α → ℝ) (n k : ℕ) :
    Measurable fun w : ℝ → ℝ => levelRiemann ν g s n k w :=
  Finset.measurable_sum _ fun _ _ => measurable_const.mul (measurable_pi_apply _)

end MatedCRT.Field.Level
