import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps
import LatticeProb.Prob.BrownianLevyReflection
import LatticeProb.Prob.CorrelatedBMWhitening
import LatticeProb.Prob.CorrelatedBMRecenter
import LatticeProb.Analysis.CorrelatedBMHolder
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.TransferScaling
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2Unique

/-!
# Two pieces of the occupation estimate in Shimura's argument

For the `γ`-correlated Brownian pair `(L, R)` with `0 < γ < 2` (paths in `Path2`):

* `le_measure_survivalR`: after a deterministic time `c₀` the coordinate `R` stays above
  `R c₀ - x` on `[c₀, c₀ + T]` with probability at least `x / (16 √T)` when `x ^ 2 ≤ T`.  This is
  the survival bound of Lévy's reflection inequality (`LatticeProb.le_measure_forall_ge_neg`) for
  the recentred coordinate `shiftedCoordinate 1 c₀`, which is a Brownian motion.
* `exists_pos_le_measure_polygon`: there is a constant `c₂ > 0`, independent of the law, of the
  base time `a` and of the scale `e > 0`, such that on the cell `[a, a + e ^ 2]` the pair
  `(L, R)` makes the four moves
  `L` drops by `2 e`, `R` rises by `2 e` above its starting value, `R` stays above `R a - 4 e` and
  ends above `R a - e` with probability at least `c₂`.

For the second statement, the whitening `whitenAt γ 0` turns `(L, R)` into the uncorrelated pair
(`isCorrelatedBM2_map_whitenAt`), and `PlanarTubePositive` says that the whitened pair follows a
straight path within a tube with positive probability.  The straight path is chosen so that `L`
decreases by `3` and `R` increases by `3`.  The tube event is contained in a measurable event
defined through rational times, and, after recentring and Brownian scaling
(`isCorrelatedBM2_map_recenterPath`, `isCorrelatedBM2_map_unitRescalePath`), its probability does
not depend on `a`, `e` or on the law, since the law of the correlated pair is unique
(`isCorrelatedBM2_unique_holds`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace MatedCRT.PeanosphereTriplePoints

open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2 lrCoord lrCov shiftedCoordinate
  shiftedCoordinate_isBrownianReal)
open LatticeProb.CorrelatedBM (measurable_lrCoord_path recenterPath continuous_recenterPath
  isCorrelatedBM2_map_recenterPath whitenAt continuous_whitenAt isCorrelatedBM2_map_whitenAt)
open MatedCRTHarmonic.MesoModel (unitRescalePath measurable_unitRescalePath
  isCorrelatedBM2_map_unitRescalePath)

/-! ### Survival of `R` after a deterministic time -/

/-- **Survival of `R` after the time `c₀`.**  For the `γ`-correlated pair, `R` stays above
`R c₀ - x` on `[c₀, c₀ + T]` with probability at least `x / (16 √T)`, if `0 < x` and
`x ^ 2 ≤ T`. -/
theorem le_measure_survivalR {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (c0 : ℝ)
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hxT : x ^ 2 ≤ T) :
    ENNReal.ofReal (x / (16 * Real.sqrt T)) ≤
      μ {p | ∀ u ∈ Icc c0 (c0 + T), (p c0).2 - x ≤ (p u).2} := by
  have := hμ.isProbabilityMeasure
  have hB := shiftedCoordinate_isBrownianReal hμ 1 c0
  have hm : ∀ t, Measurable (shiftedCoordinate 1 c0 t) := fun t =>
    (measurable_lrCoord_path 1 _).sub (measurable_lrCoord_path 1 _)
  have hTc : ((Real.toNNReal T : ℝ≥0) : ℝ) = T := Real.coe_toNNReal _ hT.le
  have h := LatticeProb.le_measure_forall_ge_neg hB hm (T := Real.toNNReal T) hx
    (by rw [hTc]; exact hxT)
  rw [hTc] at h
  refine h.trans (measure_mono ?_)
  intro ω hω u hu
  have h1 := hω (Real.toNNReal (u - c0)) (Real.toNNReal_le_toNNReal (by linarith [hu.2]))
  have e1 : shiftedCoordinate 1 c0 (Real.toNNReal (u - c0)) ω =
      lrCoord 1 u ω - lrCoord 1 c0 ω := by
    unfold shiftedCoordinate
    rw [Real.coe_toNNReal _ (sub_nonneg.2 hu.1), add_sub_cancel]
  have e0 : shiftedCoordinate 1 c0 0 ω = 0 := by simp [shiftedCoordinate]
  rw [e1, e0] at h1
  have l1 : ∀ (t : ℝ) (ω : Path2), lrCoord 1 t ω = (ω t).2 := fun t ω => by simp [lrCoord]
  rw [l1, l1] at h1
  show (ω c0).2 - x ≤ (ω u).2
  linarith

/-! ### The cell polygon -/

/-- The normalising constant `√(2 (1 + ρ))` of the sum coordinate in `whitenAt`. -/
private noncomputable def sigU (γ : ℝ) : ℝ := Real.sqrt (2 * (1 + lrCov γ 0 1))

/-- The normalising constant `√(2 (1 - ρ))` of the difference coordinate in `whitenAt`. -/
private noncomputable def sigV (γ : ℝ) : ℝ := Real.sqrt (2 * (1 - lrCov γ 0 1))

/-- For `0 < γ < 2` the correlation `lrCov γ 0 1` lies strictly between `-1` and `1`. -/
private lemma rho_bounds {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    -1 < lrCov γ 0 1 ∧ lrCov γ 0 1 < 1 := by
  have hl : lrCov γ 0 1 = -Real.cos (Real.pi * γ ^ 2 / 4) := by simp [lrCov]
  have hpi := Real.pi_pos
  have hγsq : γ ^ 2 < 4 := by nlinarith [mul_pos (sub_pos.2 hγ2) (by linarith : 0 < 2 + γ)]
  have hx0 : 0 < Real.pi * γ ^ 2 / 4 := by positivity
  have hx1 : Real.pi * γ ^ 2 / 4 < Real.pi := by nlinarith [mul_pos hpi (sub_pos.2 hγsq)]
  rw [hl]
  constructor
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hx1.le hx0
    rw [Real.cos_zero] at this
    linarith
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi hx0.le (le_refl Real.pi) hx1
    rw [Real.cos_pi] at this
    linarith

private lemma sigU_pos {γ : ℝ} (h : -1 < lrCov γ 0 1) : 0 < sigU γ :=
  Real.sqrt_pos.2 (by linarith)

private lemma sigV_pos {γ : ℝ} (h : lrCov γ 0 1 < 1) : 0 < sigV γ :=
  Real.sqrt_pos.2 (by linarith)

private lemma sigU_le {γ : ℝ} (h : lrCov γ 0 1 < 1) : sigU γ ≤ 2 :=
  Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩

private lemma sigV_le {γ : ℝ} (h : -1 < lrCov γ 0 1) : sigV γ ≤ 2 :=
  Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩

/-- A continuous function that is nonnegative at the rational points of `[0, 1]` is nonnegative on
`[0, 1]`. -/
private lemma nonneg_of_forall_rat {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) 1 → 0 ≤ g q) : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ g u := by
  have hS : IsClosed {u : ℝ | 0 ≤ g u} := isClosed_le continuous_const hg
  have hdense : Dense (range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  have h1 : Ioo (0 : ℝ) 1 ⊆ closure (Ioo (0 : ℝ) 1 ∩ range ((↑) : ℚ → ℝ)) :=
    hdense.open_subset_closure_inter isOpen_Ioo
  have h2 : Ioo (0 : ℝ) 1 ∩ range ((↑) : ℚ → ℝ) ⊆ {u | 0 ≤ g u} := by
    rintro _ ⟨hu, q, rfl⟩
    exact h q (Ioo_subset_Icc_self hu)
  have h3 : Icc (0 : ℝ) 1 ⊆ closure (Ioo (0 : ℝ) 1 ∩ range ((↑) : ℚ → ℝ)) := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact closure_minimal h1 isClosed_closure
  exact fun u hu => (closure_minimal h2 hS) (h3 hu)

/-- The whitened pair stays within `1 / 8` of the straight path `s ↦ s (0, -6 / σ_V)` at the
rational times of `[0, 1]`.  This is a measurable event containing the tube event. -/
private def SBig (γ : ℝ) : Set Path2 :=
  {w | ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) 1 →
    dist (w q - w 0) (((q : ℝ) / 1) • ((0 : ℝ), -6 / sigV γ)) ≤ 1 / 8}

/-- `SBig γ` is measurable: it is a countable intersection of measurable events. -/
private lemma measurableSet_SBig (γ : ℝ) : MeasurableSet (SBig γ) := by
  have e : SBig γ = ⋂ q : ℚ, {w : Path2 | (q : ℝ) ∈ Icc (0 : ℝ) 1 →
      dist (w q - w 0) (((q : ℝ) / 1) • ((0 : ℝ), -6 / sigV γ)) ≤ 1 / 8} := by
    ext w
    simp only [SBig, mem_ofPred_eq, mem_iInter]
  rw [e]
  refine MeasurableSet.iInter fun q => ?_
  by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) 1
  · simp only [hq, true_imp_iff]
    exact measurableSet_le (((ContinuousMap.measurable_eval _).sub
      (ContinuousMap.measurable_eval _)).dist measurable_const) measurable_const
  · simp [hq]

/-- If the whitened path at time `0` of a path `q` starting at `0` lies in `SBig γ`, then `L` and
`R` of `q` follow `-3 t` and `3 t` within `1 / 4` on `[0, 1]`. -/
private lemma whiten_bounds {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (q : Path2) (hq0 : q 0 = 0)
    (h : whitenAt γ 0 q ∈ SBig γ) :
    ∀ t ∈ Icc (0 : ℝ) 1, |(q t).1 + 3 * t| ≤ 1 / 4 ∧ |(q t).2 - 3 * t| ≤ 1 / 4 := by
  obtain ⟨hρ1, hρ2⟩ := rho_bounds hγ0 hγ2
  have hU := sigU_pos hρ1
  have hV := sigV_pos hρ2
  have hU2 := sigU_le hρ2
  have hV2 := sigV_le hρ1
  have hcont : Continuous fun s : ℝ => dist (whitenAt γ 0 q s - whitenAt γ 0 q 0)
      ((s / 1) • ((0 : ℝ), -6 / sigV γ)) :=
    (((whitenAt γ 0 q).continuous.sub continuous_const).dist
      ((continuous_id.div_const 1).smul continuous_const))
  have hall := nonneg_of_forall_rat (g := fun s : ℝ => 1 / 8 - dist
      (whitenAt γ 0 q s - whitenAt γ 0 q 0) ((s / 1) • ((0 : ℝ), -6 / sigV γ)))
    (continuous_const.sub hcont) (fun r hr => sub_nonneg.2 (h r hr))
  intro t ht
  have hd : dist (whitenAt γ 0 q t - whitenAt γ 0 q 0) ((t / 1) • ((0 : ℝ), -6 / sigV γ)) ≤
      1 / 8 := by
    have := hall t ht
    simp only [sub_nonneg] at this
    exact this
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hd
  obtain ⟨hd1, hd2⟩ := hd
  have k1 : (whitenAt γ 0 q t - whitenAt γ 0 q 0).1 = ((q t).1 + (q t).2) / sigU γ := by
    rw [Prod.fst_sub]
    show ((q (0 + t)).1 + (q (0 + t)).2 - ((q 0).1 + (q 0).2)) / sigU γ -
      ((q (0 + 0)).1 + (q (0 + 0)).2 - ((q 0).1 + (q 0).2)) / sigU γ = _
    simp [hq0]
  have k2 : (whitenAt γ 0 q t - whitenAt γ 0 q 0).2 = ((q t).1 - (q t).2) / sigV γ := by
    rw [Prod.snd_sub]
    show ((q (0 + t)).1 - (q (0 + t)).2 - ((q 0).1 - (q 0).2)) / sigV γ -
      ((q (0 + 0)).1 - (q (0 + 0)).2 - ((q 0).1 - (q 0).2)) / sigV γ = _
    simp [hq0]
  have hW1 : ((t / 1) • ((0 : ℝ), -6 / sigV γ)).1 = 0 := by simp
  have hW2 : ((t / 1) • ((0 : ℝ), -6 / sigV γ)).2 = t * (-6 / sigV γ) := by simp
  rw [k1, hW1, sub_zero, abs_div, abs_of_pos hU, div_le_iff₀ hU] at hd1
  have e2 : ((q t).1 - (q t).2) / sigV γ - t * (-6 / sigV γ) =
      ((q t).1 - (q t).2 + 6 * t) / sigV γ := by ring
  rw [k2, hW2, e2, abs_div, abs_of_pos hV, div_le_iff₀ hV] at hd2
  have a1 := abs_le.1 hd1
  have a2 := abs_le.1 hd2
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩ <;> linarith [a1.1, a1.2, a2.1, a2.2]

/-- The map sending a path to its recentred and rescaled cell path:
`t ↦ e⁻¹ (p (a + e ^ 2 t) - p a)`. -/
private noncomputable abbrev cellMap (a e : ℝ) : Path2 → Path2 :=
  unitRescalePath (e ^ 2) ∘ recenterPath a 1

private lemma cellMap_apply {a e : ℝ} (he : 0 < e) (p : Path2) (t : ℝ) :
    cellMap a e p t = e⁻¹ • (p (a + e ^ 2 * t) - p a) := by
  have h : Real.sqrt (e ^ 2) = e := Real.sqrt_sq he.le
  show (Real.sqrt (e ^ 2))⁻¹ • (p (a + 1 * (e ^ 2 * t)) - p a) = _
  rw [h, one_mul]

private lemma cellMap_zero {a e : ℝ} (he : 0 < e) (p : Path2) : cellMap a e p 0 = 0 := by
  rw [cellMap_apply he]
  simp

private lemma measurable_cellMap (a e : ℝ) : Measurable (cellMap a e) :=
  (measurable_unitRescalePath _).comp (continuous_recenterPath a 1).measurable

private lemma mul_inv_mul_aux {e X : ℝ} (he : 0 < e) : e * (e⁻¹ * X) = X := by
  field_simp

/-- The four moves of the polygon follow from the tube bounds on the rescaled cell path. -/
private lemma polygon_of_bounds {a e : ℝ} (he : 0 < e) (p : Path2)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1,
      |(cellMap a e p t).1 + 3 * t| ≤ 1 / 4 ∧ |(cellMap a e p t).2 - 3 * t| ≤ 1 / 4) :
    (∃ s ∈ Icc a (a + e ^ 2), (p s).1 ≤ (p a).1 - 2 * e) ∧
      (∃ s ∈ Icc a (a + e ^ 2), (p s).2 ≤ (p (a + e ^ 2)).2 - 2 * e) ∧
      (∀ s ∈ Icc a (a + e ^ 2), (p a).2 - 4 * e ≤ (p s).2) ∧
      (p a).2 - e ≤ (p (a + e ^ 2)).2 := by
  have key : ∀ t ∈ Icc (0 : ℝ) 1,
      |e⁻¹ * ((p (a + e ^ 2 * t)).1 - (p a).1) + 3 * t| ≤ 1 / 4 ∧
        |e⁻¹ * ((p (a + e ^ 2 * t)).2 - (p a).2) - 3 * t| ≤ 1 / 4 := by
    intro t ht
    have h := hb t ht
    have h1 : (cellMap a e p t).1 = e⁻¹ * ((p (a + e ^ 2 * t)).1 - (p a).1) := by
      rw [cellMap_apply he]; simp
    have h2 : (cellMap a e p t).2 = e⁻¹ * ((p (a + e ^ 2 * t)).2 - (p a).2) := by
      rw [cellMap_apply he]; simp
    rw [h1, h2] at h
    exact h
  have he2 : 0 ≤ e ^ 2 := sq_nonneg e
  obtain ⟨k1, k2⟩ := key 1 ⟨zero_le_one, le_rfl⟩
  simp only [mul_one] at k1 k2
  have hX1 : e * (e⁻¹ * ((p (a + e ^ 2)).1 - (p a).1)) ≤ e * (-11 / 4) :=
    mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 k1).2]) he.le
  have hX2 : e * (11 / 4) ≤ e * (e⁻¹ * ((p (a + e ^ 2)).2 - (p a).2)) :=
    mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 k2).1]) he.le
  rw [mul_inv_mul_aux he] at hX1 hX2
  refine ⟨⟨a + e ^ 2, ⟨by linarith, le_rfl⟩, by linarith⟩, ⟨a, ⟨le_rfl, by linarith⟩, by linarith⟩,
    ?_, by linarith⟩
  intro s hs
  have ht : (s - a) / e ^ 2 ∈ Icc (0 : ℝ) 1 := by
    have he2' : 0 < e ^ 2 := by positivity
    exact ⟨div_nonneg (by linarith [hs.1]) he2,
      (div_le_one he2').2 (by linarith [hs.2])⟩
  have hs' : a + e ^ 2 * ((s - a) / e ^ 2) = s := by
    have : e ^ 2 * ((s - a) / e ^ 2) = s - a := by field_simp
    linarith
  have k := (key _ ht).2
  rw [hs'] at k
  have hge : e * (-1 / 4) ≤ e * (e⁻¹ * ((p s).2 - (p a).2)) :=
    mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 k).1, ht.1]) he.le
  rw [mul_inv_mul_aux he] at hge
  linarith

/-- **The cell polygon.**  For `0 < γ < 2` there is a constant `c₂ > 0` such that for every law
`μ` of the `γ`-correlated pair, every `a` and every `e > 0`, with probability at least `c₂` on
the cell `[a, a + e ^ 2]`: `L` drops by `2 e` below `L a`, `R` at time `a` is at least `2 e` below
`R (a + e ^ 2)`, `R` stays above `R a - 4 e`, and `R (a + e ^ 2) ≥ R a - e`.  The proof uses
`PlanarTubePositive` for the whitened pair and the straight path along which `L` decreases by `3`
and `R` increases by `3`. -/
theorem exists_pos_le_measure_polygon {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hT : PlanarTubePositive) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ a e : ℝ, 0 < e →
      ENNReal.ofReal c₂ ≤ μ {p | (∃ s ∈ Icc a (a + e ^ 2), (p s).1 ≤ (p a).1 - 2 * e) ∧
        (∃ s ∈ Icc a (a + e ^ 2), (p s).2 ≤ (p (a + e ^ 2)).2 - 2 * e) ∧
        (∀ s ∈ Icc a (a + e ^ 2), (p a).2 - 4 * e ≤ (p s).2) ∧
        (p a).2 - e ≤ (p (a + e ^ 2)).2} := by
  by_cases hex : ∃ ν : Measure Path2, IsCorrelatedBM2 γ ν
  · obtain ⟨ν, hν⟩ := hex
    have := hν.isProbabilityMeasure
    have hMmeas : MeasurableSet (whitenAt γ 0 ⁻¹' SBig γ) :=
      (continuous_whitenAt γ 0).measurable (measurableSet_SBig γ)
    have hMpos : 0 < ν (whitenAt γ 0 ⁻¹' SBig γ) := by
      have hν' := isCorrelatedBM2_map_whitenAt hγ0 hγ2 0 hν
      have h1 := hT _ hν' 1 ((0 : ℝ), -6 / sigV γ) (1 / 8) one_pos (by norm_num)
      have hsub : {p : Path2 | ∀ s ∈ Icc (0 : ℝ) 1,
          dist (p s - p 0) ((s / 1) • ((0 : ℝ), -6 / sigV γ)) < 1 / 8} ⊆ SBig γ :=
        fun w hw r hr => (hw r hr).le
      calc (0 : ℝ≥0∞) < _ := h1
        _ ≤ (ν.map (whitenAt γ 0)) (SBig γ) := measure_mono hsub
        _ = ν (whitenAt γ 0 ⁻¹' SBig γ) :=
          Measure.map_apply (continuous_whitenAt γ 0).measurable (measurableSet_SBig γ)
    refine ⟨(ν (whitenAt γ 0 ⁻¹' SBig γ)).toReal,
      ENNReal.toReal_pos hMpos.ne' (measure_ne_top _ _), ?_⟩
    intro μ hμ a e he
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hF : IsCorrelatedBM2 γ (μ.map (cellMap a e)) := by
      have h1 := isCorrelatedBM2_map_recenterPath hμ a 1 (by norm_num)
      have h2 := isCorrelatedBM2_map_unitRescalePath (ε := e ^ 2) (by positivity) h1
      rwa [Measure.map_map (measurable_unitRescalePath _)
        (continuous_recenterPath a 1).measurable] at h2
    have hEq : μ.map (cellMap a e) = ν :=
      MatedCRTHarmonic.isCorrelatedBM2_unique_holds γ _ _ hF hν
    calc ν (whitenAt γ 0 ⁻¹' SBig γ) = (μ.map (cellMap a e)) (whitenAt γ 0 ⁻¹' SBig γ) := by
          rw [hEq]
      _ = μ (cellMap a e ⁻¹' (whitenAt γ 0 ⁻¹' SBig γ)) :=
          Measure.map_apply (measurable_cellMap a e) hMmeas
      _ ≤ _ := by
          refine measure_mono fun p hp => ?_
          have hp' : whitenAt γ 0 (cellMap a e p) ∈ SBig γ := hp
          exact polygon_of_bounds he p
            (whiten_bounds hγ0 hγ2 _ (cellMap_zero he p) hp')
  · exact ⟨1, one_pos, fun μ hμ => absurd ⟨μ, hμ⟩ hex⟩

end MatedCRT.PeanosphereTriplePoints
