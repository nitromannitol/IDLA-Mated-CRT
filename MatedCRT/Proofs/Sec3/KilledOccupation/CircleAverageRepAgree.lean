import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockFun

/-!
# Agreement of the circle-average representative with a continuous family (step B1 of the transfer of thm:occ-main)

For a family `ψ` of circle averages indexed by `UnitDiskCircleIndex` which is continuous, the circle-average
representative `ψ̃(ε, x) = circleAverageRep ψ ε x` of `regClockFun` equals `ψ(ε, x)` at every index point `(ε, x)`.
The proof: the index set is open in `ℝ × ℂ`, the dyadic approximants of `(ε, x)` converge to `(ε, x)`
(`tendsto_dyadicGridPoint`), so eventually they are evaluated by `ψ` at points tending to `(ε, x)`, and the limit
superior of a convergent sequence is its limit.

Only the continuity of `ψ` on the index set is used; no measure-theoretic input.
-/

open MeasureTheory Set Filter Topology Metric
open scoped NNReal

namespace MatedCRT.KilledOccupation

/-- The index set of the circle averages is open in `ℝ × ℂ`: the condition `closedBall z r ⊆ B_1` with `r > 0` is the
strict inequality `|z| + r < 1`. -/
lemma unitDiskCircleIndex_eq_inter :
    UnitDiskCircleIndex = {q : ℝ × ℂ | 0 < q.1} ∩ {q : ℝ × ℂ | ‖q.2‖ + q.1 < 1} := by
  ext q
  constructor
  · rintro ⟨hr, hball⟩
    refine ⟨hr, ?_⟩
    show ‖q.2‖ + q.1 < 1
    rcases eq_or_ne q.2 0 with hz | hz
    · have hmem : ((q.1 : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
        apply hball
        rw [Metric.mem_closedBall, dist_eq_norm, hz, sub_zero, Complex.norm_real,
          Real.norm_of_nonneg hr.le]
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hr.le] at hmem
      rw [hz, norm_zero]
      linarith
    · have hpos : 0 < ‖q.2‖ := norm_pos_iff.2 hz
      have ht0 : 0 ≤ q.1 / ‖q.2‖ := div_nonneg hr.le hpos.le
      have hmem : (1 + q.1 / ‖q.2‖) • q.2 ∈ closedBall q.2 q.1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hsub : (1 + q.1 / ‖q.2‖) • q.2 - q.2 = (q.1 / ‖q.2‖) • q.2 := by
          rw [add_smul, one_smul, add_sub_cancel_left]
        rw [hsub, norm_smul, Real.norm_of_nonneg ht0, div_mul_cancel₀ _ hpos.ne']
      have h1 := hball hmem
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by linarith)] at h1
      have h2 : (1 + q.1 / ‖q.2‖) * ‖q.2‖ = ‖q.2‖ + q.1 := by
        rw [add_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
      linarith
  · rintro ⟨hr, hn⟩
    simp only [Set.mem_ofPred_eq] at hr hn
    refine ⟨hr, ?_⟩
    refine Metric.closedBall_subset_ball' ?_
    rw [dist_zero_right]
    linarith

/-- The index set `UnitDiskCircleIndex` of the circle averages is open in `ℝ × ℂ` (B1 of MQ-li-8 (b)). -/
lemma isOpen_unitDiskCircleIndex : IsOpen UnitDiskCircleIndex := by
  rw [unitDiskCircleIndex_eq_inter]
  exact (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt (continuous_snd.norm.add continuous_fst) continuous_const)

/-- The floor approximation of a real number at dyadic mesh `2^{-n}`: `⌊2^n t⌋ / 2^n → t`. -/
lemma tendsto_dyadic_floor_div (t : ℝ) :
    Tendsto (fun n : ℕ => ((⌊(2 : ℝ) ^ n * t⌋ : ℤ) : ℝ) / 2 ^ n) atTop (𝓝 t) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => pow_pos two_pos n
  have hlow : ∀ n : ℕ, t - (1 / 2 : ℝ) ^ n ≤ ((⌊(2 : ℝ) ^ n * t⌋ : ℤ) : ℝ) / 2 ^ n := by
    intro n
    rw [one_div_pow, le_div_iff₀ (hpos n)]
    have h2 : (t - 1 / 2 ^ n) * 2 ^ n = 2 ^ n * t - 1 := by
      rw [sub_mul, one_div, inv_mul_cancel₀ (hpos n).ne']
      ring
    rw [h2]
    linarith [Int.lt_floor_add_one ((2 : ℝ) ^ n * t)]
  have hup : ∀ n : ℕ, ((⌊(2 : ℝ) ^ n * t⌋ : ℤ) : ℝ) / 2 ^ n ≤ t := by
    intro n
    rw [div_le_iff₀ (hpos n)]
    linarith [Int.floor_le ((2 : ℝ) ^ n * t)]
  have hlim : Tendsto (fun n : ℕ => t - (1 / 2 : ℝ) ^ n) atTop (𝓝 t) := by
    have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using (tendsto_const_nhds (x := t)).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun n => hlow n) (fun n => hup n)

/-- The dyadic approximants `dyadicGridPoint n (dyadicRound n q)` of a point `q ∈ ℝ × ℂ` converge to `q`. -/
lemma tendsto_dyadicGridPoint (q : ℝ × ℂ) :
    Tendsto (fun n : ℕ => dyadicGridPoint n (dyadicRound n q)) atTop (𝓝 q) := by
  have hcont : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) := by
    have : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) = Complex.equivRealProdCLM.symm := by
      funext p
      apply Complex.ext <;> simp
    rw [this]
    exact Complex.equivRealProdCLM.symm.continuous
  have h2 : Tendsto (fun n : ℕ => (⟨((⌊(2 : ℝ) ^ n * q.2.re⌋ : ℤ) : ℝ) / 2 ^ n,
      ((⌊(2 : ℝ) ^ n * q.2.im⌋ : ℤ) : ℝ) / 2 ^ n⟩ : ℂ)) atTop (𝓝 q.2) := by
    have := (hcont.tendsto (q.2.re, q.2.im)).comp
      ((tendsto_dyadic_floor_div q.2.re).prodMk_nhds (tendsto_dyadic_floor_div q.2.im))
    exact this
  have key := (tendsto_dyadic_floor_div q.1).prodMk_nhds h2
  simpa [dyadicRound, dyadicGridPoint] using key

/-- The function `circleValueAt ψ` is continuous at every point of the index set when `ψ` is continuous. -/
lemma continuousAt_circleValueAt {ψ : UnitDiskCircleIndex → ℝ} (hψ : Continuous ψ) {q : ℝ × ℂ}
    (hq : q ∈ UnitDiskCircleIndex) : ContinuousAt (circleValueAt ψ) q := by
  have hcon : ContinuousOn (circleValueAt ψ) UnitDiskCircleIndex := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hres : UnitDiskCircleIndex.domRestrict (circleValueAt ψ) = ψ := by
      funext x
      simp [Set.domRestrict_apply, circleValueAt, x.2]
    rw [hres]
    exact hψ
  exact hcon.continuousAt (isOpen_unitDiskCircleIndex.mem_nhds hq)

/-- **Step B1 (circle-average representative on the index set).** If the family `ψ` of circle averages is
continuous on `UnitDiskCircleIndex`, then `ψ̃(ε, x) = ψ(ε, x)` at every index point `(ε, x)`: the representative
is the limit superior of the dyadic evaluations, which converge to `ψ(ε, x)` by continuity. -/
theorem circleAverageRep_eq_of_continuous {ψ : UnitDiskCircleIndex → ℝ} (hψ : Continuous ψ) {ε : ℝ} {x : ℂ}
    (h : (ε, x) ∈ UnitDiskCircleIndex) : circleAverageRep ψ ε x = ψ ⟨(ε, x), h⟩ := by
  unfold circleAverageRep
  have hlim := (continuousAt_circleValueAt hψ h).tendsto.comp (tendsto_dyadicGridPoint (ε, x))
  refine (hlim.limsup_eq).trans ?_
  simp [circleValueAt, h]

end MatedCRT.KilledOccupation
