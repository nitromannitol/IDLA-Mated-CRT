import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraReflection
import LatticeProb.Prob.BrownianMax
import LatticeProb.Prob.CorrelatedBMRationalDescent
import LatticeProb.Prob.CorrelatedBMWindowIndependence
import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Analysis.CorrelatedBMHolder

/-!
# The upper bound for the probability of a cell in Shimura's argument

For the `γ`-correlated two-sided Brownian pair `(L, R)` and a mesh `δ = 1/n`, the event `A^n_k`
that cell `[(k - 1)/n, k/n]` carries a minimum of `L` on the preceding window of length `2` and a
minimum of `R` on the following window has probability at most `C / n`, with `C` independent of
the law, of `n ≥ 1` and of `k` (Shimura, Lemma 1, upper half).

* By recentring at `(k - 1)/n` (`cellEvent_eq_preimage`) the event for cell `k` is the preimage of
  the event for the first cell under a map carrying a correlated Brownian law to a correlated
  Brownian law.
* On the first cell, let `j` be the least integer with `sup_{[0, δ]} |L - L 0|, sup_{[0, δ]}
  |R - R 0| ≤ j √δ`.  The event forces `L ≥ L 0 - j √δ` on `[δ - 2, 0]` and
  `R ≥ R δ - 2 j √δ` on `[δ, 2]`, and the cell oscillation exceeds `(j - 1) √δ`.
* The oscillation on the cell, the past on `[δ - 2, 0]` and the future on `[δ, 2]` depend on the
  increments over three windows with disjoint interiors, hence are independent.  The past and the
  future are controlled by the reflection barrier, the oscillation by the maximal inequality for
  Brownian motion, and the resulting series in `j` converges.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MatedCRT.PeanosphereTriplePoints

open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2 lrCoord shiftedCoordinate
  shiftedCoordinate_isBrownianReal)
open LatticeProb.CorrelatedBM (coneIncr reversedCoordinate reversedCoordinate_isBrownianReal
  measurable_lrCoord_path continuous_lrCoord_time recenterPath continuous_recenterPath
  isCorrelatedBM2_map_recenterPath iIndepFun_increment_windows)

/-! ### Real analysis -/

private lemma forall_rat_imp_forall_real {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a < b)
    (h : ∀ q : ℚ, (q : ℝ) ∈ Icc a b → 0 ≤ g q) : ∀ u ∈ Icc a b, 0 ≤ g u := by
  have hS : IsClosed {u : ℝ | 0 ≤ g u} := isClosed_le continuous_const hg
  have hdense : Dense (range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  have h1 : Ioo a b ⊆ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) :=
    hdense.open_subset_closure_inter isOpen_Ioo
  have h2 : Ioo a b ∩ range ((↑) : ℚ → ℝ) ⊆ {u | 0 ≤ g u} := by
    rintro _ ⟨hu, q, rfl⟩
    exact h q (Ioo_subset_Icc_self hu)
  have h3 : Icc a b ⊆ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) := by
    rw [← closure_Ioo hab.ne]
    exact closure_minimal h1 isClosed_closure
  exact fun u hu => (closure_minimal h2 hS) (h3 hu)

/-- Clamp a rational into `[l, r]`. -/
private noncomputable def clampT (l r : ℝ) (q : ℚ) : ℝ := max l (min r (q : ℝ))

private lemma clampT_mem {l r : ℝ} (h : l ≤ r) (q : ℚ) : clampT l r q ∈ Icc l r :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

private lemma clampT_of_mem {l r : ℝ} {q : ℚ} (h : (q : ℝ) ∈ Icc l r) : clampT l r q = q := by
  unfold clampT
  rw [min_eq_right h.2, max_eq_right h.1]

private lemma nonneg_of_forall_clamp {g : ℝ → ℝ} (hg : Continuous g) {l r : ℝ} (hlr : l < r)
    (h : ∀ q : ℚ, 0 ≤ g (clampT l r q)) : ∀ u ∈ Icc l r, 0 ≤ g u :=
  forall_rat_imp_forall_real hg hlr fun q hq => by
    have := h q
    rwa [clampT_of_mem hq] at this

/-! ### The first cell in normalised coordinates -/

/-- Shimura's event on the first cell of mesh `δ`, for functions vanishing at `0`. -/
private def UnitCell (δ : ℝ) (X Y : ℝ → ℝ) : Prop :=
  (∃ s ∈ Icc 0 δ, ∀ u ∈ Icc (δ - 2) 0, X s ≤ X u) ∧ ∃ s ∈ Icc 0 δ, ∀ u ∈ Icc δ 2, Y s ≤ Y u

private lemma unitCell_congr {δ : ℝ} {X X' Y Y' : ℝ → ℝ} (hX : ∀ t, X t = X' t)
    (hY : ∀ t, Y t = Y' t) : UnitCell δ X Y ↔ UnitCell δ X' Y' := by
  simp only [UnitCell, hX, hY]

private lemma shimuraCell_iff (n k : ℕ) (X Y : ℝ → ℝ) :
    ShimuraCell n k X Y ↔
      UnitCell (1 / (n : ℝ)) (fun t => X (((k : ℝ) - 1) / n + t) - X (((k : ℝ) - 1) / n))
        (fun t => Y (((k : ℝ) - 1) / n + t) - Y (((k : ℝ) - 1) / n)) := by
  set c : ℝ := ((k : ℝ) - 1) / n with hc
  set δ : ℝ := 1 / (n : ℝ) with hδ
  have hk : (k : ℝ) / n = c + δ := by rw [hc, hδ]; ring
  unfold ShimuraCell UnitCell
  rw [hk]
  constructor
  · rintro ⟨⟨s, hs, hsX⟩, ⟨s', hs', hsY⟩⟩
    refine ⟨⟨s - c, ⟨by linarith [hs.1], by linarith [hs.2]⟩, fun u hu => ?_⟩,
      ⟨s' - c, ⟨by linarith [hs'.1], by linarith [hs'.2]⟩, fun u hu => ?_⟩⟩
    · have := hsX (c + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
      beta_reduce
      rw [add_sub_cancel]
      exact sub_le_sub_right this _
    · have := hsY (c + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
      beta_reduce
      rw [add_sub_cancel]
      exact sub_le_sub_right this _
  · rintro ⟨⟨s, hs, hsX⟩, ⟨s', hs', hsY⟩⟩
    refine ⟨⟨c + s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, fun u hu => ?_⟩,
      ⟨c + s', ⟨by linarith [hs'.1], by linarith [hs'.2]⟩, fun u hu => ?_⟩⟩
    · have := hsX (u - c) ⟨by linarith [hu.1], by linarith [hu.2]⟩
      beta_reduce at this
      rw [add_sub_cancel] at this
      exact (sub_le_sub_iff_right _).1 this
    · have := hsY (u - c) ⟨by linarith [hu.1], by linarith [hu.2]⟩
      beta_reduce at this
      rw [add_sub_cancel] at this
      exact (sub_le_sub_iff_right _).1 this

private lemma recenter_apply (c e : ℝ) (p : Path2) (t : ℝ) :
    recenterPath c e p t = p (c + e * t) - p c := rfl

private lemma cellEvent_eq_preimage (n k : ℕ) :
    cellEvent n k = recenterPath (((k : ℝ) - 1) / n) 1 ⁻¹' cellEvent n 1 := by
  ext p
  simp only [cellEvent, mem_ofPred_eq, mem_preimage]
  rw [shimuraCell_iff, shimuraCell_iff]
  apply unitCell_congr <;> intro t <;> simp [recenter_apply]

private lemma lrCoord_zero (t : ℝ) (ω : Path2) : lrCoord 0 t ω = (ω t).1 := by simp [lrCoord]

private lemma lrCoord_one (t : ℝ) (ω : Path2) : lrCoord 1 t ω = (ω t).2 := by simp [lrCoord]

private lemma exists_cover {δ : ℝ} (hδ : 0 < δ) {X Y : ℝ → ℝ} (hX : Continuous X)
    (hY : Continuous Y) (hX0 : X 0 = 0) (h : UnitCell δ X Y) :
    ∃ j : ℕ, (¬ ∀ s ∈ Icc 0 δ, |X s| ≤ ((j : ℝ) - 1) * Real.sqrt δ ∧
        |Y s| ≤ ((j : ℝ) - 1) * Real.sqrt δ) ∧
      (∀ u ∈ Icc (δ - 2) 0, -((j : ℝ) * Real.sqrt δ) ≤ X u) ∧
      ∀ u ∈ Icc δ 2, -(2 * ((j : ℝ) * Real.sqrt δ)) ≤ Y u - Y δ := by
  classical
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hex : ∃ j : ℕ, ∀ s ∈ Icc 0 δ,
      |X s| ≤ (j : ℝ) * Real.sqrt δ ∧ |Y s| ≤ (j : ℝ) * Real.sqrt δ := by
    obtain ⟨CX, hCX⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := δ)).exists_bound_of_continuousOn
      hX.continuousOn
    obtain ⟨CY, hCY⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := δ)).exists_bound_of_continuousOn
      hY.continuousOn
    obtain ⟨j, hj⟩ := exists_nat_ge (max CX CY / Real.sqrt δ)
    have h2 : max CX CY ≤ j * Real.sqrt δ := (div_le_iff₀ hsq).1 hj
    refine ⟨j, fun s hs => ⟨?_, ?_⟩⟩
    · have := hCX s hs
      rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_left _ _).trans h2)
    · have := hCY s hs
      rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_right _ _).trans h2)
  have hmin : ∃ j : ℕ, (∀ s ∈ Icc 0 δ, |X s| ≤ (j : ℝ) * Real.sqrt δ ∧
      |Y s| ≤ (j : ℝ) * Real.sqrt δ) ∧ ∀ m < j, ¬ ∀ s ∈ Icc 0 δ,
      |X s| ≤ (m : ℝ) * Real.sqrt δ ∧ |Y s| ≤ (m : ℝ) * Real.sqrt δ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  obtain ⟨j, hjP, hjmin⟩ := hmin
  obtain ⟨⟨s0, hs0, hsX⟩, ⟨s1, hs1, hsY⟩⟩ := h
  refine ⟨j, ?_, ?_, ?_⟩
  · intro hall
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      have := (hall 0 ⟨le_rfl, hδ.le⟩).1
      rw [hX0, abs_zero] at this
      simp at this
      linarith
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      refine hjmin m (Nat.lt_succ_self m) fun s hs => ?_
      have := hall s hs
      simpa [Nat.cast_succ] using this
  · intro u hu
    have h1 := hsX u hu
    have h2 := neg_abs_le (X s0)
    have h3 := (hjP s0 hs0).1
    linarith
  · intro u hu
    have h1 := hsY u hu
    have h2 := neg_abs_le (Y s1)
    have h3 := (hjP s1 hs1).2
    have h4 := neg_abs_le (Y δ)
    have h5 := (hjP δ ⟨hδ.le, le_rfl⟩).2
    have h6 := le_abs_self (Y δ)
    linarith

/-! ### The events -/

/-- No time of the past window `[δ - 2, 0]` is below `L 0 - a`. -/
private def Pev (δ a : ℝ) : Set Path2 :=
  {ω | ∀ u ∈ Icc (δ - 2) 0, -a ≤ lrCoord 0 u ω - lrCoord 0 0 ω}

/-- The oscillation of `(L, R)` on `[0, δ]` exceeds `b`. -/
private def Gev (δ b : ℝ) : Set Path2 :=
  {ω | ¬ ∀ s ∈ Icc 0 δ, |lrCoord 0 s ω - lrCoord 0 0 ω| ≤ b ∧
    |lrCoord 1 s ω - lrCoord 1 0 ω| ≤ b}

/-- `R` on the future window `[δ, 2]` stays above `R δ - 2 a`. -/
private def Fev (δ a : ℝ) : Set Path2 :=
  {ω | ∀ u ∈ Icc δ 2, -(2 * a) ≤ lrCoord 1 u ω - lrCoord 1 δ ω}

/-! ### Probability bounds -/

private lemma measure_pev_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (j : ℕ) :
    μ (Pev δ (j * Real.sqrt δ)) ≤ ENNReal.ofReal (((j : ℝ) + 1) * Real.sqrt δ) := by
  have := hμ.isProbabilityMeasure
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hTc : ((Real.toNNReal (2 - δ) : ℝ≥0) : ℝ) = 2 - δ := Real.coe_toNNReal _ (by linarith)
  have hT : 0 < Real.toNNReal (2 - δ) := Real.toNNReal_pos.2 (by linarith)
  have hB := reversedCoordinate_isBrownianReal hμ 0 0
  have ha : 0 ≤ ((j : ℝ) + 1) * Real.sqrt δ := by positivity
  refine (measure_mono ?_).trans ((measure_forall_gt_neg_le hB hT ha).trans ?_)
  · intro ω hω s hs
    have hs' : (s : ℝ) ≤ 2 - δ := by
      have := NNReal.coe_le_coe.2 hs
      rwa [hTc] at this
    have h1 := hω (0 - s) ⟨by linarith, by linarith [NNReal.coe_nonneg s]⟩
    have h0 : reversedCoordinate 0 0 0 ω = 0 := by simp [reversedCoordinate]
    have hsub : reversedCoordinate 0 0 s ω = lrCoord 0 (0 - s) ω - lrCoord 0 0 ω := rfl
    rw [h0, hsub, sub_zero]
    nlinarith
  · apply ENNReal.ofReal_le_ofReal
    refine mul_le_of_le_one_right ha ?_
    refine Real.sqrt_le_one.2 ?_
    rw [hTc, div_le_one (by nlinarith [Real.pi_gt_three])]
    nlinarith [Real.pi_gt_three]

private lemma measure_fev_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (j : ℕ) :
    μ (Fev δ (j * Real.sqrt δ)) ≤ ENNReal.ofReal ((2 * (j : ℝ) + 1) * Real.sqrt δ) := by
  have := hμ.isProbabilityMeasure
  have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hTc : ((Real.toNNReal (2 - δ) : ℝ≥0) : ℝ) = 2 - δ := Real.coe_toNNReal _ (by linarith)
  have hT : 0 < Real.toNNReal (2 - δ) := Real.toNNReal_pos.2 (by linarith)
  have hB := shiftedCoordinate_isBrownianReal hμ 1 δ
  have ha : 0 ≤ (2 * (j : ℝ) + 1) * Real.sqrt δ := by positivity
  refine (measure_mono ?_).trans ((measure_forall_gt_neg_le hB hT ha).trans ?_)
  · intro ω hω s hs
    have hs' : (s : ℝ) ≤ 2 - δ := by
      have := NNReal.coe_le_coe.2 hs
      rwa [hTc] at this
    have h1 := hω (δ + s) ⟨by linarith [NNReal.coe_nonneg s], by linarith⟩
    have h0 : shiftedCoordinate 1 δ 0 ω = 0 := by simp [shiftedCoordinate]
    have hsub : shiftedCoordinate 1 δ s ω = lrCoord 1 (δ + s) ω - lrCoord 1 δ ω := rfl
    rw [h0, hsub, sub_zero]
    nlinarith
  · apply ENNReal.ofReal_le_ofReal
    refine mul_le_of_le_one_right ha ?_
    refine Real.sqrt_le_one.2 ?_
    rw [hTc, div_le_one (by nlinarith [Real.pi_gt_three])]
    nlinarith [Real.pi_gt_three]

private lemma shifted_zero_toNNReal (i : Fin 2) (t : ℝ) (ω : Path2) (ht : 0 ≤ t) :
    shiftedCoordinate i 0 (Real.toNNReal t) ω = lrCoord i t ω - lrCoord i 0 ω := by
  simp [shiftedCoordinate, Real.coe_toNNReal _ ht]

private lemma shifted_zero_zero (i : Fin 2) (ω : Path2) : shiftedCoordinate i 0 0 ω = 0 := by
  simp [shiftedCoordinate]

private lemma measure_gev_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {δ : ℝ}
    (hδ : 0 < δ) (j : ℕ) :
    μ (Gev δ (((j : ℝ) - 1) * Real.sqrt δ)) ≤
      ENNReal.ofReal (8 * Real.exp (-(((j : ℝ) - 1) ^ 2 / 32))) := by
  have := hμ.isProbabilityMeasure
  by_cases hj : 2 ≤ j
  · have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
    set a : ℝ := ((j : ℝ) - 1) * Real.sqrt δ with ha_def
    have ha : 0 < a := mul_pos (by linarith) (Real.sqrt_pos.2 hδ)
    have hT : ((Real.toNNReal δ : ℝ≥0) : ℝ) = δ := Real.coe_toNNReal _ hδ.le
    have hbound : ∀ i : Fin 2, μ {ω | ∃ s : ℝ≥0, s ≤ Real.toNNReal δ ∧
        a ≤ |shiftedCoordinate i 0 s ω - shiftedCoordinate i 0 0 ω|} ≤
        4 * ENNReal.ofReal (Real.exp (-(((j : ℝ) - 1) ^ 2 / 32))) := by
      intro i
      have hm : ∀ t, Measurable (shiftedCoordinate i 0 t) := fun t =>
        (measurable_lrCoord_path i _).sub (measurable_lrCoord_path i _)
      refine (LatticeProb.measure_exists_abs_sub_ge_le (shiftedCoordinate_isBrownianReal hμ i 0)
        hm (Real.toNNReal δ) ha).trans ?_
      have : a ^ 2 / (32 * ((Real.toNNReal δ : ℝ≥0) : ℝ)) = ((j : ℝ) - 1) ^ 2 / 32 := by
        rw [hT, ha_def, mul_pow, Real.sq_sqrt hδ.le]
        field_simp
      rw [this]
    have hsub : Gev δ a ⊆ {ω | ∃ s : ℝ≥0, s ≤ Real.toNNReal δ ∧
          a ≤ |shiftedCoordinate 0 0 s ω - shiftedCoordinate 0 0 0 ω|} ∪
        {ω | ∃ s : ℝ≥0, s ≤ Real.toNNReal δ ∧
          a ≤ |shiftedCoordinate 1 0 s ω - shiftedCoordinate 1 0 0 ω|} := by
      intro ω hω
      by_contra hcon
      apply hω
      intro s hs
      refine ⟨?_, ?_⟩
      · by_contra hlt
        refine hcon (Or.inl ⟨Real.toNNReal s, Real.toNNReal_le_toNNReal hs.2, ?_⟩)
        rw [shifted_zero_toNNReal 0 s ω hs.1, shifted_zero_zero, sub_zero]
        exact (not_le.1 hlt).le
      · by_contra hlt
        refine hcon (Or.inr ⟨Real.toNNReal s, Real.toNNReal_le_toNNReal hs.2, ?_⟩)
        rw [shifted_zero_toNNReal 1 s ω hs.1, shifted_zero_zero, sub_zero]
        exact (not_le.1 hlt).le
    calc μ (Gev δ a) ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ 4 * ENNReal.ofReal (Real.exp (-(((j : ℝ) - 1) ^ 2 / 32))) +
          4 * ENNReal.ofReal (Real.exp (-(((j : ℝ) - 1) ^ 2 / 32))) :=
        add_le_add (hbound 0) (hbound 1)
      _ = ENNReal.ofReal (8 * Real.exp (-(((j : ℝ) - 1) ^ 2 / 32))) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ← add_mul]
        norm_num
  · have hj2 : j < 2 := by omega
    have hx : ((j : ℝ) - 1) ^ 2 ≤ 1 := by interval_cases j <;> norm_num
    have h1 : -(1 / 32 : ℝ) ≤ -(((j : ℝ) - 1) ^ 2 / 32) := by linarith
    have h2 := Real.add_one_le_exp (-(1 / 32 : ℝ))
    have h3 := Real.exp_le_exp.2 h1
    calc μ (Gev δ (((j : ℝ) - 1) * Real.sqrt δ)) ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (8 * Real.exp (-(((j : ℝ) - 1) ^ 2 / 32))) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-! ### Independence -/

/-- The left endpoints of the past, cell and future windows. -/
private noncomputable def winL3 (δ : ℝ) : Fin 3 → ℝ := ![δ - 2, 0, δ]

/-- The right endpoints of the past, cell and future windows. -/
private noncomputable def winR3 (δ : ℝ) : Fin 3 → ℝ := ![0, δ, 2]

private lemma winL3_zero (δ : ℝ) : winL3 δ 0 = δ - 2 := rfl
private lemma winL3_one (δ : ℝ) : winL3 δ 1 = 0 := rfl
private lemma winL3_two (δ : ℝ) : winL3 δ 2 = δ := rfl
private lemma winR3_zero (δ : ℝ) : winR3 δ 0 = 0 := rfl
private lemma winR3_one (δ : ℝ) : winR3 δ 1 = δ := rfl
private lemma winR3_two (δ : ℝ) : winR3 δ 2 = 2 := rfl

/-- The increments of the window `i`, read at the rational times clamped into the window. -/
private noncomputable def Obs (δ : ℝ) (i : Fin 3) (ω : Path2) (p : Fin 2 × ℚ) : ℝ :=
  coneIncr p.1 (clampT (winL3 δ i) (winR3 δ i) p.2) (winL3 δ i) ω

private def SP (a : ℝ) : Set (Fin 2 × ℚ → ℝ) := ⋂ q : ℚ, {x | -a ≤ x (0, q) - x (0, 0)}

private def SG (b : ℝ) : Set (Fin 2 × ℚ → ℝ) :=
  (⋂ q : ℚ, {x | |x (0, q)| ≤ b ∧ |x (1, q)| ≤ b})ᶜ

private def SF (a : ℝ) : Set (Fin 2 × ℚ → ℝ) := ⋂ q : ℚ, {x | -(2 * a) ≤ x (1, q)}

private lemma measurableSet_SP (a : ℝ) : MeasurableSet (SP a) :=
  MeasurableSet.iInter fun q => measurableSet_le measurable_const
    (by fun_prop : Measurable fun x : Fin 2 × ℚ → ℝ => x (0, q) - x (0, 0))

private lemma measurableSet_SG (b : ℝ) : MeasurableSet (SG b) :=
  (MeasurableSet.iInter fun q =>
    (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply (0, q)))
      measurable_const).inter
    (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply (1, q)))
      measurable_const)).compl

private lemma measurableSet_SF (a : ℝ) : MeasurableSet (SF a) :=
  MeasurableSet.iInter fun q => measurableSet_le measurable_const (measurable_pi_apply (1, q))

private lemma pev_eq {δ : ℝ} (_hδ : 0 < δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    Pev δ a = Obs δ 0 ⁻¹' SP a := by
  have hc0 : clampT (δ - 2) 0 0 = 0 := by
    have := clampT_of_mem (l := δ - 2) (r := 0) (q := 0) ⟨by norm_num; linarith, by norm_num⟩
    simpa using this
  ext ω
  simp only [Pev, SP, Obs, coneIncr, winL3_zero, winR3_zero, mem_ofPred_eq, mem_preimage,
    mem_iInter]
  constructor
  · intro h q
    rw [hc0]
    have := h _ (clampT_mem (by linarith) q)
    linarith
  · intro h u hu
    have hg : Continuous fun u => lrCoord 0 u ω - lrCoord 0 0 ω + a :=
      ((continuous_lrCoord_time 0 ω).sub continuous_const).add continuous_const
    have := nonneg_of_forall_clamp hg (l := δ - 2) (r := 0) (by linarith) (fun q => by
      have hq := h q
      rw [hc0] at hq
      show 0 ≤ lrCoord 0 (clampT (δ - 2) 0 q) ω - lrCoord 0 0 ω + a
      linarith) u hu
    linarith

private lemma fev_eq {δ : ℝ} (_hδ : 0 < δ) (hδ1 : δ ≤ 1) (a : ℝ) :
    Fev δ a = Obs δ 2 ⁻¹' SF a := by
  ext ω
  simp only [Fev, SF, Obs, coneIncr, winL3_two, winR3_two, mem_ofPred_eq, mem_preimage,
    mem_iInter]
  constructor
  · intro h q
    exact h _ (clampT_mem (by linarith) q)
  · intro h u hu
    have hg : Continuous fun u => lrCoord 1 u ω - lrCoord 1 δ ω + 2 * a :=
      ((continuous_lrCoord_time 1 ω).sub continuous_const).add continuous_const
    have := nonneg_of_forall_clamp hg (l := δ) (r := 2) (by linarith) (fun q => by
      have hq := h q
      show 0 ≤ lrCoord 1 (clampT δ 2 q) ω - lrCoord 1 δ ω + 2 * a
      linarith) u hu
    linarith

private lemma gev_eq {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (b : ℝ) :
    Gev δ b = Obs δ 1 ⁻¹' SG b := by
  ext ω
  simp only [Gev, SG, Obs, coneIncr, winL3_one, winR3_one, mem_ofPred_eq, mem_preimage,
    mem_compl_iff, mem_iInter]
  refine not_congr ?_
  constructor
  · intro h q
    have := h _ (clampT_mem hδ.le q)
    exact this
  · intro h s hs
    have hg0 : Continuous fun u => b - |lrCoord 0 u ω - lrCoord 0 0 ω| :=
      continuous_const.sub (continuous_abs.comp
        ((continuous_lrCoord_time 0 ω).sub continuous_const))
    have hg1 : Continuous fun u => b - |lrCoord 1 u ω - lrCoord 1 0 ω| :=
      continuous_const.sub (continuous_abs.comp
        ((continuous_lrCoord_time 1 ω).sub continuous_const))
    have h0 := nonneg_of_forall_clamp hg0 (l := 0) (r := δ) hδ (fun q => by
      have := (h q).1
      show 0 ≤ b - |lrCoord 0 (clampT 0 δ q) ω - lrCoord 0 0 ω|
      linarith) s hs
    have h1 := nonneg_of_forall_clamp hg1 (l := 0) (r := δ) hδ (fun q => by
      have := (h q).2
      show 0 ≤ b - |lrCoord 1 (clampT 0 δ q) ω - lrCoord 1 0 ω|
      linarith) s hs
    exact ⟨by linarith, by linarith⟩

private lemma measure_inter_three {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (a b : ℝ) :
    μ (Pev δ a ∩ Gev δ b ∩ Fev δ a) = μ (Pev δ a) * μ (Gev δ b) * μ (Fev δ a) := by
  have := hμ.isProbabilityMeasure
  have hsep : ∀ i j : Fin 3, i ≠ j → winR3 δ i ≤ winL3 δ j ∨ winR3 δ j ≤ winL3 δ i := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Or.inl le_rfl
    · exact Or.inl hδ.le
    · exact Or.inr le_rfl
    · exact absurd rfl hij
    · exact Or.inl le_rfl
    · exact Or.inr hδ.le
    · exact Or.inr le_rfl
    · exact absurd rfl hij
  have hle : ∀ i, winL3 δ i ≤ winR3 δ i := by
    intro i
    fin_cases i
    · show δ - 2 ≤ 0
      linarith
    · show (0 : ℝ) ≤ δ
      exact hδ.le
    · show δ ≤ 2
      linarith
  have hind : iIndepFun (Obs δ) μ :=
    (iIndepFun_increment_windows hμ (winL3 δ) (winR3 δ) hsep).comp
      (fun i (x : Fin 2 × Icc (winL3 δ i) (winR3 δ i) → ℝ) (p : Fin 2 × ℚ) =>
        x (p.1, ⟨clampT (winL3 δ i) (winR3 δ i) p.2, clampT_mem (hle i) p.2⟩))
      fun i => measurable_pi_iff.2 fun p => measurable_pi_apply _
  let S : Fin 3 → Set (Fin 2 × ℚ → ℝ) := ![SP a, SG b, SF a]
  have hS : ∀ i, MeasurableSet (S i) := by
    intro i
    fin_cases i
    · exact measurableSet_SP a
    · exact measurableSet_SG b
    · exact measurableSet_SF a
  have key := hind.measure_inter_preimage_eq_mul Finset.univ (sets := S) (fun i _ => hS i)
  have hset : (⋂ i ∈ (Finset.univ : Finset (Fin 3)), Obs δ i ⁻¹' S i) =
      Obs δ 0 ⁻¹' SP a ∩ Obs δ 1 ⁻¹' SG b ∩ Obs δ 2 ⁻¹' SF a := by
    ext ω
    simp only [mem_iInter, Finset.mem_univ, true_implies, mem_inter_iff, mem_preimage]
    constructor
    · intro h
      exact ⟨⟨h 0, h 1⟩, h 2⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩ i
      fin_cases i
      exacts [h0, h1, h2]
  have h3 := key
  rw [hset, Fin.prod_univ_three] at h3
  rw [pev_eq hδ hδ1, gev_eq hδ hδ1, fev_eq hδ hδ1]
  exact h3

/-! ### The series -/

/-- The weights of the series bounding the probability of a cell. -/
private noncomputable def wt (j : ℕ) : ℝ :=
  ((j : ℝ) + 1) * (2 * (j : ℝ) + 1) * (8 * Real.exp (-(((j : ℝ) - 1) ^ 2 / 32)))

private lemma wt_nonneg (j : ℕ) : 0 ≤ wt j := by
  unfold wt
  positivity

private lemma summable_wt : Summable wt := by
  set r : ℝ := Real.exp (-(1 / 32)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    have := Real.exp_lt_exp.2 (show -(1 / 32 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at this
  have hnr : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0.le]
  have s0 := summable_geometric_of_lt_one hr0.le hr1
  have s1 := summable_pow_mul_geometric_of_norm_lt_one 1 hnr
  have s2 := summable_pow_mul_geometric_of_norm_lt_one 2 hnr
  have hE := Real.exp_pos (1 / 32)
  have hbound : ∀ j : ℕ, wt j ≤ 16 * Real.exp (1 / 32) *
      (((j : ℝ) ^ 2 * r ^ j) + 2 * ((j : ℝ) ^ 1 * r ^ j) + r ^ j) := by
    intro j
    have hrj : 0 ≤ r ^ j := pow_nonneg hr0.le j
    have h1 : Real.exp (-(((j : ℝ) - 1) ^ 2 / 32)) ≤ Real.exp (1 / 32) * r ^ j := by
      have hx : (j : ℝ) - 1 ≤ ((j : ℝ) - 1) ^ 2 := by
        rcases Nat.lt_or_ge j 2 with hj | hj
        · interval_cases j <;> norm_num
        · have : (2 : ℝ) ≤ j := by exact_mod_cast hj
          nlinarith
      calc Real.exp (-(((j : ℝ) - 1) ^ 2 / 32)) ≤ Real.exp (-(((j : ℝ) - 1) / 32)) :=
            Real.exp_le_exp.2 (by linarith)
        _ = Real.exp (1 / 32) * r ^ j := by
            rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            ring
    have hM : 0 ≤ Real.exp (1 / 32) * r ^ j := mul_nonneg hE.le hrj
    have hjM : 0 ≤ (j : ℝ) * (Real.exp (1 / 32) * r ^ j) := mul_nonneg (Nat.cast_nonneg j) hM
    calc wt j = ((j : ℝ) + 1) * (2 * j + 1) * 8 * Real.exp (-(((j : ℝ) - 1) ^ 2 / 32)) := by
          unfold wt
          ring
      _ ≤ ((j : ℝ) + 1) * (2 * j + 1) * 8 * (Real.exp (1 / 32) * r ^ j) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 16 * Real.exp (1 / 32) * (((j : ℝ) ^ 2 * r ^ j) + 2 * ((j : ℝ) ^ 1 * r ^ j) + r ^ j) := by
          nlinarith [hM, hjM]
  exact Summable.of_nonneg_of_le wt_nonneg hbound
    (((s2.add (s1.mul_left 2)).add s0).mul_left (16 * Real.exp (1 / 32)))

/-! ### The first cell -/

private lemma measure_cellEvent_one_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {n : ℕ} (hn : 1 ≤ n) : μ (cellEvent n 1) ≤ ENNReal.ofReal ((∑' j : ℕ, wt j) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set δ : ℝ := 1 / (n : ℝ) with hδ_def
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ_def, div_le_one hn']
    exact_mod_cast hn
  have hcov : cellEvent n 1 ⊆ ⋃ j : ℕ, (Pev δ (j * Real.sqrt δ) ∩
      Gev δ (((j : ℝ) - 1) * Real.sqrt δ) ∩ Fev δ (j * Real.sqrt δ)) := by
    intro ω hω
    have hcell := (shimuraCell_iff n 1 (fun t => (ω t).1) (fun t => (ω t).2)).1 hω
    have hU : UnitCell δ (fun t => lrCoord 0 t ω - lrCoord 0 0 ω)
        (fun t => lrCoord 1 t ω - lrCoord 1 0 ω) := by
      refine (unitCell_congr (fun t => ?_) (fun t => ?_)).1 hcell
      · simp [lrCoord_zero]
      · simp [lrCoord_one]
    obtain ⟨j, hj1, hj2, hj3⟩ := exists_cover hδ
      (X := fun t => lrCoord 0 t ω - lrCoord 0 0 ω) (Y := fun t => lrCoord 1 t ω - lrCoord 1 0 ω)
      ((continuous_lrCoord_time 0 ω).sub continuous_const)
      ((continuous_lrCoord_time 1 ω).sub continuous_const) (by simp) hU
    refine mem_iUnion.2 ⟨j, ⟨⟨hj2, hj1⟩, ?_⟩⟩
    intro u hu
    have := hj3 u hu
    linarith
  have hterm : ∀ j : ℕ, μ (Pev δ (j * Real.sqrt δ) ∩ Gev δ (((j : ℝ) - 1) * Real.sqrt δ) ∩
      Fev δ (j * Real.sqrt δ)) ≤ ENNReal.ofReal (wt j * δ) := by
    intro j
    rw [measure_inter_three hμ hδ hδ1]
    calc _ ≤ ENNReal.ofReal (((j : ℝ) + 1) * Real.sqrt δ) *
          ENNReal.ofReal (8 * Real.exp (-(((j : ℝ) - 1) ^ 2 / 32))) *
          ENNReal.ofReal ((2 * (j : ℝ) + 1) * Real.sqrt δ) :=
          mul_le_mul' (mul_le_mul' (measure_pev_le hμ hδ hδ1 j) (measure_gev_le hμ hδ j))
            (measure_fev_le hμ hδ hδ1 j)
      _ = ENNReal.ofReal (wt j * δ) := by
          rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((j : ℝ) + 1) * Real.sqrt δ by positivity),
            ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((j : ℝ) + 1) * Real.sqrt δ *
              (8 * Real.exp (-(((j : ℝ) - 1) ^ 2 / 32))) by positivity)]
          congr 1
          have := Real.mul_self_sqrt hδ.le
          unfold wt
          linear_combination (((j : ℝ) + 1) * (2 * (j : ℝ) + 1) *
            (8 * Real.exp (-(((j : ℝ) - 1) ^ 2 / 32)))) * this
  calc μ (cellEvent n 1) ≤ μ (⋃ j : ℕ, (Pev δ (j * Real.sqrt δ) ∩
        Gev δ (((j : ℝ) - 1) * Real.sqrt δ) ∩ Fev δ (j * Real.sqrt δ))) := measure_mono hcov
    _ ≤ ∑' j : ℕ, μ (Pev δ (j * Real.sqrt δ) ∩ Gev δ (((j : ℝ) - 1) * Real.sqrt δ) ∩
        Fev δ (j * Real.sqrt δ)) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (wt j * δ) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, wt j * δ) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (wt_nonneg j) hδ.le)
          (summable_wt.mul_right δ)).symm
    _ = ENNReal.ofReal ((∑' j : ℕ, wt j) / n) := by
        rw [tsum_mul_right, hδ_def]
        congr 1
        ring

/-- **The upper bound for the probability of a cell** (Shimura, Lemma 1, upper half): for every
law of the `γ`-correlated pair, every mesh `1/n` and every cell, `P(A^n_k) ≤ C / n`. -/
theorem shimuraCellUpper_holds (γ : ℝ) :
    ∃ C : ℝ, ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ,
      μ (cellEvent n k) ≤ ENNReal.ofReal (C / n) := by
  refine ⟨∑' j : ℕ, wt j, fun μ hμ n hn k => ?_⟩
  rw [cellEvent_eq_preimage n k]
  refine (Measure.le_map_apply (continuous_recenterPath _ _).measurable.aemeasurable _).trans ?_
  exact measure_cellEvent_one_le (isCorrelatedBM2_map_recenterPath hμ _ 1 (by simp)) hn

/-- The cell bound of Shimura's argument. -/
theorem shimuraCellBounds_holds (γ : ℝ) : ShimuraCellBounds γ := by
  obtain ⟨C, hC⟩ := shimuraCellUpper_holds γ
  unfold ShimuraCellBounds
  exact ⟨C, 1, fun μ hμ n hn k _ _ => hC μ hμ n hn k⟩

end MatedCRT.PeanosphereTriplePoints
