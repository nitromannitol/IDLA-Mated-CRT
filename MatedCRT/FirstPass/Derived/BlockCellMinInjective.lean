import MatedCRT.Proofs.MatingOfTrees.BrownianLocalMin
import MatedCRT.FirstPass.Derived.BlockEdgeCount
import LatticeProb.Prob.BrownianFrequentPositivity

/-!
# The cell minima of a correlated Brownian coordinate are pairwise distinct

For a correlated two-sided Brownian law `μ` and a cell size `ε > 0`, almost surely for each coordinate the cell minima
`bmCellMin ε (lrCoord i · p) k`, `k ∈ ℤ`, are pairwise distinct (`ae_bmCellMin_injective`).

Proof. Almost surely, at each of the countably many cell endpoints the path takes smaller values immediately to the right
and immediately to the left: the recentered forward increments are a Brownian motion (`shiftedCoordinate_isBrownianReal`)
which is almost surely positive at arbitrarily small times, and so is the negative of the recentered backward increments
(`backwardCoordinate_isBrownianReal`, covariance computed from `twoSidedMin_of_le`). So the minimum over a cell is
attained in the open interior of the cell, hence at a local minimum of the path. The interiors of different cells are
disjoint, and distinct local minima have distinct values almost surely (`ae_locMinDistinct`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set MatedCRTHarmonic.MatedCRT
open scoped NNReal

noncomputable section

namespace MatedCRT

/-- The recentered backward increments `t ↦ X(a - t) - X(a)` of the coordinate `i` at the time `a`. -/
def backwardCoordinate (i : Fin 2) (a : ℝ) : ℝ≥0 → Path2 → ℝ :=
  fun t ω => lrCoord i (a - (t : ℝ)) ω - lrCoord i a ω

/-- The coordinate `ω ↦ lrCoord i t ω` is measurable. -/
theorem measurable_lrCoord (i : Fin 2) (t : ℝ) : Measurable fun ω : Path2 => lrCoord i t ω := by
  unfold lrCoord
  split_ifs
  · exact measurable_fst.comp (ContinuousMap.measurable_eval t)
  · exact measurable_snd.comp (ContinuousMap.measurable_eval t)

/-- The coordinate paths are continuous. -/
theorem continuous_lrCoord (i : Fin 2) (ω : Path2) : Continuous fun t : ℝ => lrCoord i t ω := by
  unfold lrCoord
  split_ifs
  · exact continuous_fst.comp ω.continuous
  · exact continuous_snd.comp ω.continuous

/-- For `x ≤ y` the two-sided Brownian kernel is `x⁺ + y⁻`. -/
theorem twoSidedMin_of_le {x y : ℝ} (hxy : x ≤ y) :
    twoSidedMin x y = max x 0 + max (-y) 0 := by
  unfold twoSidedMin
  rw [min_eq_left (max_le_max hxy le_rfl), min_eq_right (max_le_max (neg_le_neg hxy) le_rfl)]

theorem twoSidedMin_comm' (x y : ℝ) : twoSidedMin x y = twoSidedMin y x := by
  simp only [twoSidedMin, min_comm]

theorem max_sub_max_neg' (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring

/-- The backward increments of the two-sided Brownian covariance are the ordinary Brownian covariance. -/
theorem twoSidedMin_backward_increment {a s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    twoSidedMin (a - s) (a - t) - twoSidedMin (a - s) a - twoSidedMin a (a - t) +
      twoSidedMin a a = s := by
  have h1 := twoSidedMin_of_le (x := a - t) (y := a - s) (by linarith)
  have h2 := twoSidedMin_of_le (x := a - s) (y := a) (by linarith)
  have h3 := twoSidedMin_of_le (x := a - t) (y := a) (by linarith)
  have h4 := twoSidedMin_of_le (x := a) (y := a) le_rfl
  have h5 := max_sub_max_neg' (a - s)
  have h6 := max_sub_max_neg' a
  rw [twoSidedMin_comm' (a - s) (a - t), twoSidedMin_comm' a (a - t), h1, h2, h3, h4]
  linarith

/-- Recentered backward increments of either correlated coordinate form a standard Brownian motion. -/
theorem backwardCoordinate_isBrownianReal {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (a : ℝ) :
    IsBrownianReal (backwardCoordinate i a) μ := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let X : ℝ → Path2 → ℝ := fun t ω => lrCoord i t ω
  have hX : IsGaussianProcess X μ := hμ.isGaussianProcess.comp_right (fun t : ℝ => (i, t))
  have hback : IsGaussianProcess
      (fun t : ℝ≥0 => fun ω => X (a - (t : ℝ)) ω - X a ω) μ := by
    exact (hX.shift a).comp_right (fun t : ℝ≥0 => -(t : ℝ))
  have hmean : ∀ t : ℝ≥0, ∫ ω, X (a - (t : ℝ)) ω - X a ω ∂μ = 0 := by
    intro t
    have h1 : Integrable (X (a - (t : ℝ))) μ :=
      (hX.hasGaussianLaw_eval (a - (t : ℝ))).memLp_two.integrable (by norm_num)
    have h2 : Integrable (X a) μ := (hX.hasGaussianLaw_eval a).memLp_two.integrable (by norm_num)
    rw [integral_sub h1 h2, hμ.integral_eq_zero i (a - (t : ℝ)), hμ.integral_eq_zero i a, sub_self]
  have hcov : ∀ s t : ℝ≥0, s ≤ t →
      cov[fun ω => X (a - (s : ℝ)) ω - X a ω,
        fun ω => X (a - (t : ℝ)) ω - X a ω; μ] = s := by
    intro s t hst
    have hs : MemLp (X (a - (s : ℝ))) 2 μ :=
      (hX.hasGaussianLaw_eval (a - (s : ℝ))).memLp_two
    have ht : MemLp (X (a - (t : ℝ))) 2 μ :=
      (hX.hasGaussianLaw_eval (a - (t : ℝ))).memLp_two
    have ha : MemLp (X a) 2 μ := (hX.hasGaussianLaw_eval a).memLp_two
    rw [covariance_fun_sub_fun_sub hs ha ht ha,
      hμ.covariance_eq i i (a - (s : ℝ)) (a - (t : ℝ)),
      hμ.covariance_eq i i (a - (s : ℝ)) a,
      hμ.covariance_eq i i a (a - (t : ℝ)), hμ.covariance_eq i i a a]
    have hl : lrCov γ i i = 1 := by simp [lrCov]
    simp only [hl, one_mul]
    exact twoSidedMin_backward_increment s.2 (by exact_mod_cast hst)
  have hpre : IsPreBrownianReal (backwardCoordinate i a) μ := by
    apply hback.isPreBrownianReal_of_covariance hmean
    intro s t hst
    simpa [backwardCoordinate, X] using hcov s t hst
  refine ⟨hpre, ?_⟩
  apply ae_of_all
  intro ω
  have hx : Continuous (fun t : ℝ => lrCoord i t ω) := continuous_lrCoord i ω
  change Continuous (fun t : ℝ≥0 => lrCoord i (a - (t : ℝ)) ω - lrCoord i a ω)
  exact (hx.comp (continuous_const.sub continuous_subtype_val)).sub continuous_const

/-- Almost surely, immediately to the right of the time `a` the coordinate takes values below its value at `a`. -/
theorem ae_forall_exists_lt_right {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) (a : ℝ) :
    ∀ᵐ ω ∂μ, ∀ δ > 0, ∃ t, a < t ∧ t < a + δ ∧ lrCoord i t ω < lrCoord i a ω := by
  have hB := (shiftedCoordinate_isBrownianReal hμ i a).neg
  have hm : ∀ t, Measurable ((-shiftedCoordinate i a) t) := fun t =>
    ((measurable_lrCoord i (a + (t : ℝ))).sub (measurable_lrCoord i a)).neg
  filter_upwards [LatticeProb.ae_frequently_pos_of_isBrownianReal_blumenthal hB hm] with ω hω δ hδ
  have hU : Set.Ioo (0 : ℝ≥0) (Real.toNNReal δ) ∈ 𝓝[>] (0 : ℝ≥0) :=
    Ioo_mem_nhdsGT (Real.toNNReal_pos.2 hδ)
  obtain ⟨t, hpos, ht0, htδ⟩ := (hω.and_eventually (eventually_mem_set.2 hU)).exists
  have htδ' : (t : ℝ) < δ := by
    have h := NNReal.coe_lt_coe.2 htδ
    rwa [Real.coe_toNNReal δ hδ.le] at h
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  refine ⟨a + (t : ℝ), by linarith, by linarith, ?_⟩
  simp only [Pi.neg_apply, shiftedCoordinate] at hpos
  linarith

/-- Almost surely, immediately to the left of the time `a` the coordinate takes values below its value at `a`. -/
theorem ae_forall_exists_lt_left {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) (a : ℝ) :
    ∀ᵐ ω ∂μ, ∀ δ > 0, ∃ t, a - δ < t ∧ t < a ∧ lrCoord i t ω < lrCoord i a ω := by
  have hB := (backwardCoordinate_isBrownianReal hμ i a).neg
  have hm : ∀ t, Measurable ((-backwardCoordinate i a) t) := fun t =>
    ((measurable_lrCoord i (a - (t : ℝ))).sub (measurable_lrCoord i a)).neg
  filter_upwards [LatticeProb.ae_frequently_pos_of_isBrownianReal_blumenthal hB hm] with ω hω δ hδ
  have hU : Set.Ioo (0 : ℝ≥0) (Real.toNNReal δ) ∈ 𝓝[>] (0 : ℝ≥0) :=
    Ioo_mem_nhdsGT (Real.toNNReal_pos.2 hδ)
  obtain ⟨t, hpos, ht0, htδ⟩ := (hω.and_eventually (eventually_mem_set.2 hU)).exists
  have htδ' : (t : ℝ) < δ := by
    have h := NNReal.coe_lt_coe.2 htδ
    rwa [Real.coe_toNNReal δ hδ.le] at h
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  refine ⟨a - (t : ℝ), by linarith, by linarith, ?_⟩
  simp only [Pi.neg_apply, backwardCoordinate] at hpos
  linarith

/-- A continuous function that dips below its endpoint values immediately inside both endpoints of `[a, b]` attains
the minimum over `[a, b]` at a local minimum in the open interval. -/
theorem exists_interior_localMin {X : ℝ → ℝ} (hX : Continuous X) {a b : ℝ} (hab : a < b)
    (hfa : ∀ δ > 0, ∃ t, a < t ∧ t < a + δ ∧ X t < X a)
    (hfb : ∀ δ > 0, ∃ t, b - δ < t ∧ t < b ∧ X t < X b) :
    ∃ c, a < c ∧ c < b ∧ IsLocalMin X c ∧ sInf (X '' Set.Icc a b) = X c := by
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab.le) hX.continuousOn
  have hca : c ≠ a := by
    rintro rfl
    obtain ⟨t, h1, h2, h3⟩ := hfa (b - c) (by linarith)
    exact absurd (hmin ⟨h1.le, by linarith⟩) (not_le.2 h3)
  have hcb : c ≠ b := by
    rintro rfl
    obtain ⟨t, h1, h2, h3⟩ := hfb (c - a) (by linarith)
    exact absurd (hmin ⟨by linarith, h2.le⟩) (not_le.2 h3)
  have hc1 : a < c := lt_of_le_of_ne hc.1 (Ne.symm hca)
  have hc2 : c < b := lt_of_le_of_ne hc.2 hcb
  refine ⟨c, hc1, hc2, hmin.isLocalMin (Icc_mem_nhds hc1 hc2), ?_⟩
  exact IsLeast.csInf_eq ⟨Set.mem_image_of_mem X hc, by
    rintro _ ⟨y, hy, rfl⟩
    exact hmin hy⟩

/-- **The cell minima of a correlated Brownian coordinate are pairwise distinct.** Almost surely, for each
coordinate the map `k ↦ bmCellMin ε X k` is injective on `ℤ`. -/
theorem ae_bmCellMin_injective {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ p ∂μ, ∀ i : Fin 2, Function.Injective (bmCellMin ε fun t => lrCoord i t p) := by
  have hend : ∀ᵐ p ∂μ, ∀ i : Fin 2, ∀ k : ℤ,
      (∀ δ > 0, ∃ t, ε * k - ε < t ∧ t < ε * k - ε + δ ∧
        lrCoord i t p < lrCoord i (ε * k - ε) p) ∧
      (∀ δ > 0, ∃ t, ε * k - δ < t ∧ t < ε * k ∧ lrCoord i t p < lrCoord i (ε * k) p) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun k =>
      (ae_forall_exists_lt_right hμ i (ε * k - ε)).and (ae_forall_exists_lt_left hμ i (ε * k))
  filter_upwards [hend, ae_locMinDistinct hμ] with p hp hd i
  have hc : ∀ k : ℤ, ∃ c, ε * k - ε < c ∧ c < ε * k ∧ IsLocalMin (lrCoord i · p) c ∧
      bmCellMin ε (fun t => lrCoord i t p) k = lrCoord i c p := by
    intro k
    obtain ⟨c, h1, h2, h3, h4⟩ := exists_interior_localMin (continuous_lrCoord i p)
      (by linarith : ε * k - ε < ε * k) (hp i k).1 (hp i k).2
    exact ⟨c, h1, h2, h3, h4⟩
  have hlt : ∀ j k : ℤ, j < k →
      bmCellMin ε (fun t => lrCoord i t p) j ≠ bmCellMin ε (fun t => lrCoord i t p) k := by
    intro j k hjk
    obtain ⟨cj, hj1, hj2, hj3, hj4⟩ := hc j
    obtain ⟨ck, hk1, hk2, hk3, hk4⟩ := hc k
    have hjk' : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    have hne : cj ≠ ck := by
      have : ε * ((j : ℝ) + 1) ≤ ε * k := mul_le_mul_of_nonneg_left hjk' hε.le
      intro h
      subst h
      nlinarith
    rw [hj4, hk4]
    exact hd i cj ck hne hj3 hk3
  intro j k h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hjk
  · exact hlt j k hjk h
  · exact hlt k j hjk h.symm

/-- `ae_bmCellMin_injective` for every correlated two-sided Brownian law and every cell size. -/
theorem bmCellMin_injective_ae {γ : ℝ} :
    ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ ε > 0,
      ∀ᵐ p ∂μ, ∀ i : Fin 2, Function.Injective (bmCellMin ε fun t => lrCoord i t p) :=
  fun _ hμ _ hε => ae_bmCellMin_injective hμ hε

end MatedCRT
