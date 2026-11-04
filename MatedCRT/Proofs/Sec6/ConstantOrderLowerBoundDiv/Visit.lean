import MatedCRT.Steps.Sec6.ConstantOrderLowerBoundDiv

/-!
# Lemma 6.8, Step 2: the second moment method for the visits before the exit time (lines 2543-2546, 2616)

`srwVisitSecondMomentStep`: for simple random walk on any multigraph, the number `V` of visits to `E` before the exit
time `τ_W` satisfies `E[V]² ≤ E[τ_W²] P[V ≥ 1]` (Cauchy-Schwarz for `V = V 1_{V ≥ 1}`, and `V ≤ τ_W`), where `E[V]` is
the sum over `b' ∈ E` of the expected visit counts `G_W(b, b')`.
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

namespace ConstantOrderDiv

open Classical in
/-- `n < τ_W(y)` iff `y` stays in `W` up to time `n` (as in worker c5's `ConstantOrder.lt_vExitTime_iff`). -/
theorem lt_vExitTime_iff' {W : Set ℤ} {y : ℕ → ℤ} {i : ℕ} :
    (i : ℕ∞) < vExitTime W y ↔ ∀ j ≤ i, y j ∈ W := by
  unfold vExitTime
  split_ifs with h
  · rw [Nat.cast_lt]
    constructor
    · intro hi j hj
      exact not_not.1 (Nat.find_min h (lt_of_le_of_lt hj hi))
    · intro hall
      by_contra hle
      exact Nat.find_spec h (hall _ (not_lt.1 hle))
  · exact ⟨fun _ j _ => not_not.1 fun hj => h ⟨j, hj⟩, fun _ => ENat.natCast_lt_top i⟩

theorem measurableSet_lt_vExitTime (W : Set ℤ) (n : ℕ) :
    MeasurableSet {x : ℕ → ℤ | (n : ℕ∞) < vExitTime W x} := by
  have : {x : ℕ → ℤ | (n : ℕ∞) < vExitTime W x} = ⋂ j ∈ Finset.range (n + 1), (fun x : ℕ → ℤ => x j) ⁻¹' W := by
    ext x
    simp [lt_vExitTime_iff']
  rw [this]
  exact Finset.measurableSet_biInter _ fun j _ => (measurable_pi_apply j) (Set.to_countable W).measurableSet

theorem measurableSet_visit (W E : Set ℤ) (n : ℕ) :
    MeasurableSet {x : ℕ → ℤ | (n : ℕ∞) < vExitTime W x ∧ x n ∈ E} :=
  (measurableSet_lt_vExitTime W n).inter ((measurable_pi_apply n) (Set.to_countable E).measurableSet)

open Classical in
/-- The number of visits to `E` before the exit time from `W`. -/
noncomputable def visitCount (W E : Set ℤ) (x : ℕ → ℤ) : ℝ≥0∞ :=
  ∑' n : ℕ, (if (n : ℕ∞) < vExitTime W x ∧ x n ∈ E then 1 else 0)

theorem measurable_visitCount (W E : Set ℤ) : Measurable (visitCount W E) :=
  Measurable.tsum fun n => Measurable.ite (measurableSet_visit W E n) measurable_const measurable_const

theorem measurable_visitsBeforeExit (W : Set ℤ) (b : ℤ) : Measurable (visitsBeforeExit W b) :=
  Measurable.tsum fun n => Measurable.ite (measurableSet_visit W {b} n) measurable_const measurable_const

/-- `∑_{b' ∈ E} (visits to b') = (visits to E)`. -/
theorem tsum_visitsBeforeExit (W E : Set ℤ) (x : ℕ → ℤ) :
    ∑' b' : E, visitsBeforeExit W b' x = visitCount W E x := by
  classical
  unfold visitsBeforeExit visitCount
  rw [ENNReal.tsum_comm]
  congr 1
  funext n
  by_cases h : (n : ℕ∞) < vExitTime W x ∧ x n ∈ E
  · rw [ite_eq_left h, tsum_eq_single ⟨x n, h.2⟩]
    · simp [h.1]
    · intro b' hb'
      rw [ite_eq_right]
      rintro ⟨-, hx⟩
      exact hb' (Subtype.ext hx.symm)
  · rw [ite_eq_right h]
    exact ENNReal.tsum_eq_zero.2 fun b' =>
      ite_eq_right fun h' : (n : ℕ∞) < vExitTime W x ∧ x n = (b' : ℤ) => h ⟨h'.1, h'.2 ▸ b'.2⟩

/-- `V ≤ τ_W`. -/
theorem visitCount_le (W E : Set ℤ) (x : ℕ → ℤ) : visitCount W E x ≤ (vExitTime W x : ℝ≥0∞) := by
  classical
  unfold visitCount
  cases hτ : vExitTime W x with
  | top => simp
  | coe k =>
    calc ∑' n : ℕ, (if (n : ℕ∞) < (k : ℕ∞) ∧ x n ∈ E then (1 : ℝ≥0∞) else 0)
        ≤ ∑' n : ℕ, (if n < k then (1 : ℝ≥0∞) else 0) := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          split_ifs with h1 h2 <;> first | exact le_rfl | exact zero_le | exact absurd (Nat.cast_lt.1 h1.1) h2
      _ = ∑ n ∈ Finset.range k, (if n < k then (1 : ℝ≥0∞) else 0) :=
          tsum_eq_sum fun n hn => ite_eq_right fun h => hn (Finset.mem_range.2 h)
      _ = (k : ℝ≥0∞) := by
          rw [Finset.sum_congr rfl fun n hn => ite_eq_left (Finset.mem_range.1 hn)]
          simp
      _ = ((k : ℕ∞) : ℝ≥0∞) := by simp

/-- `V = V 1_{V ≥ 1}`. -/
theorem visitCount_eq_mul_indicator (W E : Set ℤ) (x : ℕ → ℤ) :
    visitCount W E x =
      visitCount W E x * {y : ℕ → ℤ | ∃ n : ℕ, (n : ℕ∞) < vExitTime W y ∧ y n ∈ E}.indicator 1 x := by
  set G : Set (ℕ → ℤ) := {y | ∃ n : ℕ, (n : ℕ∞) < vExitTime W y ∧ y n ∈ E}
  by_cases hx : x ∈ G
  · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
  · rw [indicator_of_notMem hx, mul_zero]
    exact ENNReal.tsum_eq_zero.2 fun n => ite_eq_right fun h => hx ⟨n, h⟩

theorem sq_rpow_half (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **The second moment method for the visits before the exit time** (lines 2543-2546, 2616). -/
theorem srwVisitSecondMomentStep : SrwVisitSecondMomentStep := by
  intro m W E b
  classical
  set μ := srwLaw m b
  set G : Set (ℕ → ℤ) := {y | ∃ n : ℕ, (n : ℕ∞) < vExitTime W y ∧ y n ∈ E} with hGdef
  have hG : MeasurableSet G := by
    have : G = ⋃ n : ℕ, {y : ℕ → ℤ | (n : ℕ∞) < vExitTime W y ∧ y n ∈ E} := by
      ext y
      simp [hGdef]
    rw [this]
    exact MeasurableSet.iUnion fun n => measurableSet_visit W E n
  set g : (ℕ → ℤ) → ℝ≥0∞ := G.indicator 1 with hg
  have hV := measurable_visitCount W E
  have hsum : ∑' b' : E, ∫⁻ x, visitsBeforeExit W b' x ∂μ = ∫⁻ x, visitCount W E x ∂μ := by
    rw [← lintegral_tsum fun b' : E => (measurable_visitsBeforeExit W b').aemeasurable]
    exact lintegral_congr fun x => tsum_visitsBeforeExit W E x
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hV.aemeasurable
    ((measurable_one.indicator hG).aemeasurable)
  have hVG : ∫⁻ x, visitCount W E x ∂μ = ∫⁻ x, (visitCount W E * g) x ∂μ :=
    lintegral_congr fun x => visitCount_eq_mul_indicator W E x
  have hV2 : ∫⁻ x, visitCount W E x ^ (2 : ℝ) ∂μ ≤ exitTimeMoment m W b 2 := by
    unfold exitTimeMoment
    refine lintegral_mono fun x => ?_
    rw [ENNReal.rpow_two]
    exact pow_le_pow_left₀ zero_le (visitCount_le W E x) 2
  have hG2 : ∫⁻ x, g x ^ (2 : ℝ) ∂μ = μ G := by
    rw [← lintegral_indicator_one hG]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ G <;> simp [hg, hx]
  rw [hsum, hVG]
  calc (∫⁻ x, (visitCount W E * g) x ∂μ) ^ 2
      ≤ ((∫⁻ x, visitCount W E x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le hHolder 2
    _ = (∫⁻ x, visitCount W E x ^ (2 : ℝ) ∂μ) * ∫⁻ x, g x ^ (2 : ℝ) ∂μ := by
        rw [mul_pow, sq_rpow_half, sq_rpow_half]
    _ ≤ exitTimeMoment m W b 2 * μ G := by
        rw [hG2]
        gcongr

end ConstantOrderDiv

end MatedCRT
