import MatedCRT.FirstPass.Derived.MarkovTimeChangeAdapted

/-!
# Good skeletons of the clock functionals of a Markovian time-changed planar Brownian motion

For a family of measurable functionals `F_s` of the clock-read path (`IsMarkovTCBM.exists_adaptedClock`), the
half-clock `A_t = F_{2t} / 2` of the planar Brownian path is defined for each real `t` only up to a null set.
Its skeleton along the nonnegative rationals, `q ↦ (1/2) F_{2q} f`, determines a continuous nondecreasing
clock exactly when it is a *good skeleton*: nondecreasing, zero at `0`, with a locally uniform modulus of
continuity stated with countable quantifiers.

* `clockSkel`, `GoodSkeleton`, `clockGoodSet`: the skeleton, the good skeletons, and the set of clock-read
  paths whose skeleton is good;
* `measurableSet_clockGoodSet`: the set of paths with a good skeleton is measurable;
* `goodSkeleton_of_continuous`: a skeleton that agrees along the rationals with a continuous nondecreasing
  function vanishing at `0` is good;
* `ae_shift_mem_clockGoodSet`: for a good crossing clock and the shift identity, almost surely every
  shifted clock-read path `q ↦ (clock-read path) (t + q)` has a good skeleton.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

/-- The skeleton of the half-clock along the nonnegative rationals: `q ↦ (1/2) F_{2q} f`, negative values
cut to `0`. -/
noncomputable def clockSkel (F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ)
    (f : ℝ≥0 → EuclideanSpace ℝ (Fin 2)) (q : ℚ≥0) : ℝ≥0 :=
  Real.toNNReal (2⁻¹ * F (2 * (q : ℝ≥0)) f)

/-- A good skeleton: zero at `0`, nondecreasing, with a locally uniform modulus of continuity with countable
quantifiers (the hypothesis of `LatticeProb.continuous_nnratRightInf`). -/
def GoodSkeleton (a : ℚ≥0 → ℝ≥0) : Prop :=
  a 0 = 0 ∧ (∀ p q : ℚ≥0, p ≤ q → a p ≤ a q) ∧
    ∀ N k : ℕ, ∃ j : ℕ, ∀ p q : ℚ≥0, (p : ℝ) ≤ N → (q : ℝ) ≤ N →
      |(p : ℝ) - q| < 1 / ((j : ℝ) + 1) → |(a p : ℝ) - (a q : ℝ)| ≤ 1 / ((k : ℝ) + 1)

theorem GoodSkeleton.monotone {a : ℚ≥0 → ℝ≥0} (h : GoodSkeleton a) : Monotone a :=
  fun p q hpq => h.2.1 p q hpq

/-- The clock-read paths whose half-clock skeleton is good. -/
def clockGoodSet (F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ) :
    Set (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) :=
  {f | GoodSkeleton (clockSkel F f)}

/-- **The set of paths with a good skeleton is measurable.** -/
theorem measurableSet_clockGoodSet {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hF : ∀ s, Measurable (F s)) : MeasurableSet (clockGoodSet F) := by
  have hm : ∀ q : ℚ≥0, Measurable fun f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) => clockSkel F f q :=
    fun q => measurable_real_toNNReal.comp ((hF _).const_mul _)
  have hc : ∀ q : ℚ≥0, Measurable fun f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) =>
      ((clockSkel F f q : ℝ≥0) : ℝ) := fun q => measurable_coe_nnreal_real.comp (hm q)
  have h1 : MeasurableSet {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) | clockSkel F f 0 = 0} :=
    measurableSet_eq_fun (hm 0) measurable_const
  have h2 : MeasurableSet {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) |
      ∀ p q : ℚ≥0, p ≤ q → clockSkel F f p ≤ clockSkel F f q} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
      measurableSet_le (hm p) (hm q)
  have h3 : MeasurableSet {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2) | ∀ N k : ℕ, ∃ j : ℕ, ∀ p q : ℚ≥0,
      (p : ℝ) ≤ N → (q : ℝ) ≤ N → |(p : ℝ) - q| < 1 / ((j : ℝ) + 1) →
        |(clockSkel F f p : ℝ) - (clockSkel F f q : ℝ)| ≤ 1 / ((k : ℝ) + 1)} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    refine MeasurableSet.iInter fun N => MeasurableSet.iInter fun k => MeasurableSet.iUnion fun j =>
      MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le (continuous_abs.measurable.comp ((hc p).sub (hc q))) measurable_const
  exact h1.inter (h2.inter h3)

/-- **A skeleton that agrees with a continuous nondecreasing function vanishing at `0` is good.** -/
theorem goodSkeleton_of_continuous {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    {f : ℝ≥0 → EuclideanSpace ℝ (Fin 2)} {b : ℝ≥0 → ℝ} (hmono : Monotone b) (hcont : Continuous b)
    (h0 : b 0 = 0) (hf : ∀ q : ℚ≥0, F (2 * (q : ℝ≥0)) f = b (2 * (q : ℝ≥0))) :
    GoodSkeleton (clockSkel F f) := by
  have hb0 : ∀ u, 0 ≤ b u := fun u => h0 ▸ hmono zero_le
  have hsk : ∀ q : ℚ≥0, ((clockSkel F f q : ℝ≥0) : ℝ) = 2⁻¹ * b (2 * (q : ℝ≥0)) := by
    intro q
    unfold clockSkel
    rw [hf q, Real.coe_toNNReal _ (mul_nonneg (by norm_num) (hb0 _))]
  refine ⟨?_, ?_, ?_⟩
  · apply NNReal.coe_injective
    rw [hsk 0]
    simp [h0]
  · intro p q hpq
    rw [← NNReal.coe_le_coe, hsk, hsk]
    have hpq' : (p : ℝ≥0) ≤ q := NNRat.cast_le.mpr hpq
    exact mul_le_mul_of_nonneg_left (hmono (by gcongr)) (by norm_num)
  · intro N k
    have hε : (0 : ℝ) < 2 / ((k : ℝ) + 1) := by positivity
    have huc : UniformContinuousOn b (Set.Icc (0 : ℝ≥0) (2 * (N : ℝ≥0))) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hcont.continuousOn
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp huc _ hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (half_pos hδ)
    refine ⟨j, fun p q hp hq hpq => ?_⟩
    have hpN : (p : ℝ≥0) ≤ N := by exact_mod_cast hp
    have hqN : (q : ℝ≥0) ≤ N := by exact_mod_cast hq
    have hp' : 2 * (p : ℝ≥0) ∈ Set.Icc (0 : ℝ≥0) (2 * (N : ℝ≥0)) := ⟨zero_le, by gcongr⟩
    have hq' : 2 * (q : ℝ≥0) ∈ Set.Icc (0 : ℝ≥0) (2 * (N : ℝ≥0)) := ⟨zero_le, by gcongr⟩
    have hd : dist (2 * (p : ℝ≥0)) (2 * (q : ℝ≥0)) < δ := by
      have e : ∀ r : ℚ≥0, ((r : ℝ≥0) : ℝ) = (r : ℝ) := fun r => by norm_cast
      rw [NNReal.dist_eq]
      push_cast
      simp only [e]
      have : |(2 : ℝ) * (p : ℝ) - 2 * (q : ℝ)| = 2 * |(p : ℝ) - q| := by
        rw [← mul_sub, abs_mul, abs_two]
      rw [this]
      linarith
    have h := hδ' _ hp' _ hq' hd
    rw [Real.dist_eq] at h
    rw [hsk p, hsk q, ← mul_sub, abs_mul]
    have h2 : |(2⁻¹ : ℝ)| = 2⁻¹ := abs_of_pos (by norm_num)
    rw [h2]
    calc 2⁻¹ * |b (2 * (p : ℝ≥0)) - b (2 * (q : ℝ≥0))| ≤ 2⁻¹ * (2 / ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h.le (by norm_num)
      _ = 1 / ((k : ℝ) + 1) := by ring

/-- **Almost surely every shifted clock-read path has a good skeleton.**  For a measure `μ` on paths such
that almost surely the crossing clock is good, and the shift identity holds for the functionals `F`, almost
surely, for every shift `t`, the path `q ↦ (clock-read path) (t + q)` lies in `clockGoodSet F`. -/
theorem ae_shift_mem_clockGoodSet {μ : Measure C(ℝ≥0, EuclideanSpace ℝ (Fin 2))} {m : ℝ≥0∞}
    {F : ℝ≥0 → (ℝ≥0 → EuclideanSpace ℝ (Fin 2)) → ℝ}
    (hgood : ∀ᵐ x ∂μ, LatticeProb.GoodClock (LatticeProb.crossClock m fun u => x u))
    (hS : ∀ t s : ℝ≥0, ∀ᵐ x ∂μ, (LatticeProb.pathClockInv m x (t + s)).toReal =
      (LatticeProb.pathClockInv m x t).toReal +
        F s fun q => LatticeProb.clockPath m (fun u => x u) (t + q)) (t : ℝ≥0) :
    ∀ᵐ x ∂μ, (fun q => LatticeProb.clockRead m x (t + q)) ∈ clockGoodSet F := by
  have hq : ∀ᵐ x ∂μ, ∀ q : ℚ≥0, (LatticeProb.pathClockInv m x (t + 2 * (q : ℝ≥0))).toReal =
      (LatticeProb.pathClockInv m x t).toReal +
        F (2 * (q : ℝ≥0)) fun r => LatticeProb.clockPath m (fun u => x u) (t + r) :=
    ae_all_iff.2 fun q => hS t (2 * (q : ℝ≥0))
  filter_upwards [hgood, hq] with x hg hx
  have hAmono : Monotone fun u : ℝ≥0 => (LatticeProb.pathClockInv m x u).toReal :=
    fun u v h => NNReal.coe_le_coe.2 (hg.monotone_clockInv_toNNReal h)
  have hAcont : Continuous fun u : ℝ≥0 => (LatticeProb.pathClockInv m x u).toReal :=
    hg.continuous_clockInv_toReal (LatticeProb.crossClock_mono m _)
  refine goodSkeleton_of_continuous
    (b := fun u => (LatticeProb.pathClockInv m x (t + u)).toReal -
      (LatticeProb.pathClockInv m x t).toReal) ?_ ?_ ?_ fun q => ?_
  · exact fun u v h => sub_le_sub_right (hAmono (add_le_add le_rfl h)) _
  · exact (hAcont.comp (continuous_const.add continuous_id)).sub continuous_const
  · simp
  · have := hx q
    change F (2 * (q : ℝ≥0)) (fun r => LatticeProb.clockPath m (fun u => x u) (t + r)) = _
    linarith

end MatedCRT
