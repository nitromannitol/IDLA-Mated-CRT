import MatedCRT.FirstPass.Derived.AnnealedMedianLimit
import MatedCRT.FirstPass.Derived.ExitTimeMedianStrictDerived
import MatedCRT.FirstPass.Derived.BLPathFunctionalDUnif
import MatedCRT.FirstPass.S3t.ContinuumUnderDiscrete
import MatedCRT.Proofs.LBM.LocalUniformDistance
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.PathEnvelope

/-!
# The exit-time median of the origin mixture of an identified limit law

Let `ν` be the law of `(D, Λ D)`, where `Λ D` is a random path-law field whose value at the origin integrates every
bounded Lipschitz path functional `F` (for the local uniform distance) as the quenched law of the rescaled Liouville
Brownian motion `X_t = B_{φ⁻¹(m₀ t)}` started at `0` (Berestycki–Gwynne (2020), Thm. 1.2 and §7.3).  This file derives,
from this identification alone, the two hypotheses `hreg` and `hstrict` of
`medianOf_exitCdf_originPathLaw_eq_one` for the origin mixture `originPathLaw ν`:

* `ae_regularExit_originPathLaw_of_identification`: `originPathLaw ν`-almost every path exits `B_{1/2}` regularly;
* `half_lt_exitCdf_originPathLaw_of_medianOf_lt`: the exit-time distribution function of `originPathLaw ν` is
  strictly above `1/2` to the right of its lower median;
* `medianOf_exitCdf_originPathLaw_eq_one_of_identification`: hence the lower median is `1`.

Bounded Lipschitz functionals reach the exit events through the truncated running maximum
`M_s f = sup_{t ∈ [0, s]} min(|f t|, 1)`, which is `2^{⌈s⌉+1}`-Lipschitz for the local uniform distance
(`abs_truncRunningMax_sub_le`): for continuous `f`, the exit time of `B_{1/2}` is at most `s` iff `M_s f ≥ 1/2`
(`pathExitTime_ball_le_iff`), and a non-regular exit is caught by a pair of rational times `q < r` with
`M_q f ≥ 1/2 ≥ M_r f` (`exists_rat_half_le_min_of_not_regularExit`, `not_regularExit_of_half_le_min`).  The piecewise
linear cutoffs `halfCutoff k (M f)` decrease to the indicators of these closed events, and dominated convergence on
both sides of the identification transfers their probabilities (`measure_mem_eq_of_integral_eq`).  Measurability of
the functionals of the rescaled path under planar Brownian motion is not assumed: the identification of the integral
of `(F + 2)/3`, whose integral against a probability measure is at least `1/3`, already forces integrability
(`aestronglyMeasurable_of_integral_affine_eq`).

The exit-time distribution function of `originPathLaw ν` is then the annealed distribution function
`G (m₀ s)` of the Liouville Brownian exit time (`exitCdf_originPathLaw_eq_lintegral_of_identification`), and the
strict increase of `G` beyond its median `m₀` (`MatedCRTEnv.IsValid.half_lt_lintegral_exitTime_le_of_m₀_lt`) gives
`medianOf = 1` and `hstrict` (`medianOf_exitCdf_originPathLaw_eq_one_of_eq_map`).
-/

open MeasureTheory Filter Topology Set Metric LatticeProb HarmonicBalls
open MarkovProcess (ContinuousPath)
open MatedCRT.TruncatedLaws (RegularExit)
open scoped NNReal ENNReal BoundedContinuousFunction

attribute [local instance] LatticeProb.dUnifMetricSpace

namespace MatedCRT.FirstPass.Derived

variable {Ω : Type} [MeasurableSpace Ω]

/-! ### The truncated running maximum -/

/-- The *truncated running maximum* `M_s f = sup_{t ∈ [0, s]} min(|f t|, 1)` of a path `f : [0, ∞) → ℂ`. -/
noncomputable def truncRunningMax (s : ℝ≥0) (f : ℝ≥0 → ℂ) : ℝ :=
  ⨆ t : Icc (0 : ℝ≥0) s, min ‖f t‖ 1

theorem bddAbove_truncRunningMax (s : ℝ≥0) (f : ℝ≥0 → ℂ) :
    BddAbove (range fun t : Icc (0 : ℝ≥0) s => min ‖f t‖ 1) :=
  ⟨1, by rintro _ ⟨t, rfl⟩; exact min_le_right _ _⟩

theorem le_truncRunningMax {s t : ℝ≥0} (f : ℝ≥0 → ℂ) (ht : t ≤ s) :
    min ‖f t‖ 1 ≤ truncRunningMax s f :=
  le_ciSup (bddAbove_truncRunningMax s f) (⟨t, bot_le, ht⟩ : Icc (0 : ℝ≥0) s)

theorem truncRunningMax_le_one (s : ℝ≥0) (f : ℝ≥0 → ℂ) : truncRunningMax s f ≤ 1 := by
  have : Nonempty (Icc (0 : ℝ≥0) s) := ⟨⟨0, le_rfl, bot_le⟩⟩
  exact ciSup_le fun _ => min_le_right _ _

theorem truncRunningMax_nonneg (s : ℝ≥0) (f : ℝ≥0 → ℂ) : 0 ≤ truncRunningMax s f :=
  (le_min (norm_nonneg _) zero_le_one).trans (le_truncRunningMax f (bot_le : (0 : ℝ≥0) ≤ s))

/-- The truncated running maximum up to time `s` is `2^{⌈s⌉+1}`-Lipschitz for the local uniform distance (one-sided
form). -/
theorem truncRunningMax_le_add (s : ℝ≥0) (f g : ℝ≥0 → ℂ) :
    truncRunningMax s f ≤ truncRunningMax s g + 2 ^ (⌈s⌉₊ + 1) * localUniformDist f g := by
  have : Nonempty (Icc (0 : ℝ≥0) s) := ⟨⟨0, le_rfl, bot_le⟩⟩
  refine ciSup_le fun t => ?_
  have hk : (t : ℝ≥0) ≤ ((⌈s⌉₊ + 1 : ℕ) : ℝ≥0) :=
    t.2.2.trans ((Nat.le_ceil s).trans (by exact_mod_cast Nat.le_succ _))
  have hw := weighted_min_dist_le_localUniformDist f g ⌈s⌉₊ hk
  have h2 : (2 : ℝ) ^ (⌈s⌉₊ + 1) * (2 : ℝ)⁻¹ ^ (⌈s⌉₊ + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
  have h1 : min 1 (dist (f t) (g t)) ≤ 2 ^ (⌈s⌉₊ + 1) * localUniformDist f g := by
    calc min 1 (dist (f t) (g t))
        = 2 ^ (⌈s⌉₊ + 1) * ((2 : ℝ)⁻¹ ^ (⌈s⌉₊ + 1) * min 1 (dist (f t) (g t))) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 ^ (⌈s⌉₊ + 1) * localUniformDist f g :=
          mul_le_mul_of_nonneg_left hw (by positivity)
  have hab : ‖f t‖ - ‖g t‖ ≤ dist (f t) (g t) := by
    rw [dist_eq_norm]
    exact norm_sub_norm_le _ _
  have h4 := le_truncRunningMax g t.2.2
  have h3 : min ‖f t‖ 1 ≤ min ‖g t‖ 1 + min 1 (dist (f t) (g t)) := by
    rcases min_cases ‖g t‖ 1 with ⟨hb, -⟩ | ⟨hb, -⟩ <;>
      rcases min_cases (1 : ℝ) (dist (f t) (g t)) with ⟨hd, -⟩ | ⟨hd, -⟩ <;>
      linarith [min_le_left ‖f t‖ 1, min_le_right ‖f t‖ 1, norm_nonneg (g t),
        dist_nonneg (x := f t) (y := g t)]
  linarith

/-- The truncated running maximum up to time `s` is `2^{⌈s⌉+1}`-Lipschitz for the local uniform distance. -/
theorem abs_truncRunningMax_sub_le (s : ℝ≥0) (f g : ℝ≥0 → ℂ) :
    |truncRunningMax s f - truncRunningMax s g| ≤ 2 ^ (⌈s⌉₊ + 1) * localUniformDist f g := by
  have h1 := truncRunningMax_le_add s f g
  have h2 := truncRunningMax_le_add s g f
  rw [localUniformDist_comm g f] at h2
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- The truncated running maximum is a bounded Lipschitz path functional. -/
theorem isBoundedLipschitzPathFunctional_truncRunningMax (s : ℝ≥0) :
    IsBoundedLipschitzPathFunctional (truncRunningMax s) :=
  ⟨fun f => abs_le.2 ⟨by linarith [truncRunningMax_nonneg s f], truncRunningMax_le_one s f⟩, _,
    abs_truncRunningMax_sub_le s⟩

theorem continuous_truncRunningMax (s : ℝ≥0) :
    Continuous fun g : ContinuousPath ℂ => truncRunningMax s ⇑g :=
  continuous_blPathFunctional (isBoundedLipschitzPathFunctional_truncRunningMax s)

/-- The functional `min (M_q f) (1 - M_r f)` is Lipschitz for the local uniform distance. -/
theorem abs_min_truncRunningMax_sub_le (q r : ℝ≥0) (f g : ℝ≥0 → ℂ) :
    |min (truncRunningMax q f) (1 - truncRunningMax r f) -
        min (truncRunningMax q g) (1 - truncRunningMax r g)| ≤
      (2 ^ (⌈q⌉₊ + 1) + 2 ^ (⌈r⌉₊ + 1)) * localUniformDist f g := by
  have hd := localUniformDist_nonneg f g
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · refine (abs_truncRunningMax_sub_le q f g).trans ?_
    rw [add_mul]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hd)
  · rw [show 1 - truncRunningMax r f - (1 - truncRunningMax r g) =
      -(truncRunningMax r f - truncRunningMax r g) by ring, abs_neg]
    refine (abs_truncRunningMax_sub_le r f g).trans ?_
    rw [add_mul]
    exact le_add_of_nonneg_left (mul_nonneg (by positivity) hd)

/-- For a continuous path, the exit time of `B_{1/2}` is at most `s` iff the truncated running maximum up to time `s`
is at least `1/2`. -/
theorem pathExitTime_ball_le_iff {f : ℝ≥0 → ℂ} (hf : Continuous f) (s : ℝ≥0) :
    pathExitTime (ball (0 : ℂ) (1 / 2)) f ≤ s ↔ 1 / 2 ≤ truncRunningMax s f := by
  have hiff := ExitTimeCdf.lt_pathExitTime_iff (U := ball (0 : ℂ) (1 / 2)) isOpen_ball
    (g := (ContinuousMap.mk f hf : C(ℝ≥0, ℂ))) (s := s)
  constructor
  · intro h
    have hnot : ¬ ∀ t ≤ s, f t ∈ ball (0 : ℂ) (1 / 2) := fun hall => (not_lt.2 h) (hiff.2 hall)
    obtain ⟨t, ht, hft⟩ : ∃ t ≤ s, f t ∉ ball (0 : ℂ) (1 / 2) := by
      by_contra hc
      exact hnot fun t ht => not_not.1 fun hn => hc ⟨t, ht, hn⟩
    rw [mem_ball_zero_iff, not_lt] at hft
    exact (le_min hft (by norm_num)).trans (le_truncRunningMax f ht)
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hall := hiff.1 hlt
    have hcont : Continuous fun t : ℝ≥0 => min ‖f t‖ (1 : ℝ) := hf.norm.min continuous_const
    obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (⟨0, le_rfl, bot_le⟩ : (Icc (0 : ℝ≥0) s).Nonempty) hcont.continuousOn
    have hM : truncRunningMax s f ≤ min ‖f t₀‖ 1 := by
      have : Nonempty (Icc (0 : ℝ≥0) s) := ⟨⟨0, le_rfl, bot_le⟩⟩
      exact ciSup_le fun t => isMaxOn_iff.1 hmax t t.2
    have h1 : ‖f t₀‖ < 1 / 2 := mem_ball_zero_iff.1 (hall t₀ ht₀.2)
    have h2 := min_le_left ‖f t₀‖ 1
    linarith

/-- The rescaled Liouville Brownian path `t ↦ B_{φ⁻¹(m t)}` has truncated running maximum at least `1/2` up to time
`s` iff the Liouville Brownian exit time of `B_{1/2}` is at most `m s`. -/
theorem half_le_truncRunningMax_rescaledLBMPath_iff {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {m : ℝ} (hm : 0 < m)
    {b : ContinuousPath ℂ} (hF : IsTimeChangeClock (F b)) (s : ℝ≥0) :
    1 / 2 ≤ truncRunningMax s (rescaledLBMPath F m b) ↔
      lbmExitTime F (ball (0 : ℂ) (1 / 2)) b ≤ ENNReal.ofReal (m * s) := by
  have hL := continuous_liouvilleBrownianPath hF
  have hc : m.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hm).ne'
  have hc0 : (m.toNNReal : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
  rw [← pathExitTime_ball_le_iff (continuous_rescaledLBMPath (m := m) hF) s]
  have h1 : pathExitTime (ball (0 : ℂ) (1 / 2)) (rescaledLBMPath F m b) =
      pathExitTime (ball (0 : ℂ) (1 / 2)) (liouvilleBrownianPath F b) / (m.toNNReal : ℝ≥0∞) :=
    exitTime_timeScalePath (ball (0 : ℂ) (1 / 2)) hc (ContinuousMap.mk _ hL : C(ℝ≥0, ℂ))
  have h2 : ENNReal.ofReal (m * s) = (s : ℝ≥0∞) * (m.toNNReal : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul hm.le, ENNReal.ofReal_coe_nnreal, mul_comm]
    rfl
  show pathExitTime (ball (0 : ℂ) (1 / 2)) (rescaledLBMPath F m b) ≤ (s : ℝ≥0∞) ↔
    pathExitTime (ball (0 : ℂ) (1 / 2)) (liouvilleBrownianPath F b) ≤ ENNReal.ofReal (m * s)
  rw [h1, ENNReal.div_le_iff_le_mul (Or.inl hc0) (Or.inl ENNReal.coe_ne_top), h2]

/-! ### Regular exit through rational times -/

/-- A continuous path that is outside `B_{1/2}` before time `q` and in the closed disc `\bar B_{1/2}` up to the later
time `r` does not exit `B_{1/2}` regularly. -/
theorem not_regularExit_of_half_le_min {f : ℝ≥0 → ℂ} (hf : Continuous f) {q r : ℝ} (hq : 0 < q) (hqr : q < r)
    (h : 1 / 2 ≤ min (truncRunningMax q.toNNReal f) (1 - truncRunningMax r.toNNReal f)) :
    ¬ RegularExit (ball (0 : ℂ) (1 / 2)) f := by
  obtain ⟨h1, h2⟩ := le_min_iff.1 h
  have hle := (pathExitTime_ball_le_iff hf q.toNNReal).2 h1
  have hne : pathExitTime (ball (0 : ℂ) (1 / 2)) f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ≥0, pathExitTime (ball (0 : ℂ) (1 / 2)) f = τ :=
    ⟨_, (ENNReal.coe_toNNReal hne).symm⟩
  have hτq : τ ≤ q.toNNReal := by
    rw [hτ] at hle
    exact ENNReal.coe_le_coe.1 hle
  have hqr' : q.toNNReal < r.toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq.le, Real.coe_toNNReal _ (hq.trans hqr).le]
    exact hqr
  have hbound : ∀ t ≤ r.toNNReal, ‖f t‖ ≤ 1 / 2 := fun t ht => by
    have h3 := le_truncRunningMax f ht
    have h4 : min ‖f t‖ 1 ≤ 1 / 2 := by linarith
    rcases min_le_iff.1 h4 with h5 | h5
    · exact h5
    · norm_num at h5
  rw [RegularExit, hτ, ENNReal.toNNReal_coe]
  rintro (htop | hfreq)
  · exact ENNReal.coe_ne_top htop
  · refine Filter.not_frequently.2 ?_ hfreq
    filter_upwards [Ioo_mem_nhdsGT (hτq.trans_lt hqr')] with t ht
    rw [not_not, closure_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0), mem_closedBall_zero_iff]
    exact hbound t ht.2.le

/-- A continuous path that does not exit `B_{1/2}` regularly is outside `B_{1/2}` before a rational time `q > 0` and
in the closed disc `\bar B_{1/2}` up to a later rational time `r`. -/
theorem exists_rat_half_le_min_of_not_regularExit {g : ContinuousPath ℂ}
    (hg : ¬ RegularExit (ball (0 : ℂ) (1 / 2)) ⇑g) :
    ∃ p : ℚ × ℚ, (0 < p.1 ∧ p.1 < p.2) ∧
      1 / 2 ≤ min (truncRunningMax ((p.1 : ℝ).toNNReal) ⇑g) (1 - truncRunningMax ((p.2 : ℝ).toNNReal) ⇑g) := by
  rw [RegularExit, not_or] at hg
  obtain ⟨hne, hnf⟩ := hg
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ≥0, pathExitTime (ball (0 : ℂ) (1 / 2)) ⇑g = τ :=
    ⟨_, (ENNReal.coe_toNNReal hne).symm⟩
  rw [hτ, ENNReal.toNNReal_coe] at hnf
  have hev : ∀ᶠ t in 𝓝[>] τ, g t ∈ closure (ball (0 : ℂ) (1 / 2)) :=
    (Filter.not_frequently.1 hnf).mono fun _ ht => not_not.1 ht
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  obtain ⟨q, hτq, hqu⟩ := exists_rat_btwn (NNReal.coe_lt_coe.2 hu)
  obtain ⟨r, hqr, hru⟩ := exists_rat_btwn hqu
  have hq0 : (0 : ℝ) < q := τ.coe_nonneg.trans_lt hτq
  have hr0 : (0 : ℝ) < r := hq0.trans hqr
  have hcl : closure (ball (0 : ℂ) (1 / 2)) = closedBall 0 (1 / 2) := closure_ball 0 (by norm_num)
  have hclτ : g τ ∈ closure (ball (0 : ℂ) (1 / 2)) :=
    isClosed_closure.mem_of_tendsto ((g.continuous.tendsto τ).mono_left nhdsWithin_le_nhds) hev
  refine ⟨(q, r), ⟨Rat.cast_pos.1 hq0, Rat.cast_lt.1 hqr⟩, le_min ?_ ?_⟩
  · show (1 / 2 : ℝ) ≤ truncRunningMax ((q : ℝ).toNNReal) ⇑g
    refine (pathExitTime_ball_le_iff g.continuous _).1 ?_
    rw [hτ]
    refine ENNReal.coe_le_coe.2 ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0.le]
    exact hτq.le
  · show (1 / 2 : ℝ) ≤ 1 - truncRunningMax ((r : ℝ).toNNReal) ⇑g
    have hM : truncRunningMax ((r : ℝ).toNNReal) ⇑g ≤ 1 / 2 := by
      have : Nonempty (Icc (0 : ℝ≥0) ((r : ℝ).toNNReal)) := ⟨⟨0, le_rfl, bot_le⟩⟩
      refine ciSup_le fun t => min_le_of_left_le ?_
      have ht : ((t : ℝ≥0) : ℝ) ≤ r := by
        have h := t.2.2
        rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0.le] at h
      rcases lt_trichotomy (t : ℝ≥0) τ with htτ | htτ | htτ
      · have hlt : ((t : ℝ≥0) : ℝ≥0∞) < pathExitTime (ball (0 : ℂ) (1 / 2)) ⇑g := by
          rw [hτ]
          exact ENNReal.coe_lt_coe.2 htτ
        exact (mem_ball_zero_iff.1 ((ExitTimeCdf.lt_pathExitTime_iff isOpen_ball).1 hlt t le_rfl)).le
      · rw [htτ]
        have h := hclτ
        rw [hcl, mem_closedBall_zero_iff] at h
        exact h
      · have htu : (t : ℝ≥0) < u := NNReal.coe_lt_coe.1 (ht.trans_lt hru)
        have h : g t ∈ closure (ball (0 : ℂ) (1 / 2)) := hsub ⟨htτ, htu⟩
        rw [hcl, mem_closedBall_zero_iff] at h
        exact h
    linarith

/-! ### Piecewise linear cutoffs -/

/-- The piecewise linear cutoff `x ↦ min(max(1 + k (x - 1/2), 0), 1)`, which decreases to `1_{x ≥ 1/2}` as `k → ∞`. -/
noncomputable def halfCutoff (k : ℕ) (x : ℝ) : ℝ :=
  max (min (1 + k * (x - 1 / 2)) 1) 0

theorem abs_halfCutoff_le (k : ℕ) (x : ℝ) : |halfCutoff k x| ≤ 1 := by
  have h0 : 0 ≤ halfCutoff k x := le_max_right _ _
  have h1 : halfCutoff k x ≤ 1 := max_le (min_le_right _ _) zero_le_one
  exact abs_le.2 ⟨by linarith, h1⟩

theorem abs_halfCutoff_sub_le (k : ℕ) (x y : ℝ) : |halfCutoff k x - halfCutoff k y| ≤ k * |x - y| := by
  unfold halfCutoff
  refine (abs_max_sub_max_le_abs _ _ _).trans ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _),
    show 1 + (k : ℝ) * (x - 1 / 2) - (1 + k * (y - 1 / 2)) = k * (x - y) by ring, abs_mul, Nat.abs_cast]

theorem tendsto_halfCutoff_indicator {α : Type*} (Φ : α → ℝ) (x : α) :
    Tendsto (fun k : ℕ => halfCutoff k (Φ x)) atTop (𝓝 ({y | 1 / 2 ≤ Φ y}.indicator 1 x)) := by
  by_cases hx : 1 / 2 ≤ Φ x
  · rw [Set.indicator_of_mem (show x ∈ {y | 1 / 2 ≤ Φ y} from hx), Pi.one_apply]
    refine tendsto_const_nhds.congr fun k => ?_
    show 1 = halfCutoff k (Φ x)
    have hk : 0 ≤ (k : ℝ) * (Φ x - 1 / 2) := mul_nonneg k.cast_nonneg (by linarith)
    have h3 : (1 : ℝ) ≤ 1 + (k : ℝ) * (Φ x - 1 / 2) := by linarith
    unfold halfCutoff
    rw [min_eq_right h3, max_eq_left zero_le_one]
  · rw [Set.indicator_of_notMem (show x ∉ {y | 1 / 2 ≤ Φ y} from hx)]
    have hpos : 0 < 1 / 2 - Φ x := by linarith [not_le.1 hx]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈(1 / 2 - Φ x)⁻¹⌉₊] with k hk
    show 0 = halfCutoff k (Φ x)
    have hk' : (1 / 2 - Φ x)⁻¹ ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have h1 : 1 ≤ (k : ℝ) * (1 / 2 - Φ x) := by
      have h := mul_le_mul_of_nonneg_right hk' hpos.le
      rwa [inv_mul_cancel₀ hpos.ne'] at h
    have h2 : (k : ℝ) * (Φ x - 1 / 2) = -((k : ℝ) * (1 / 2 - Φ x)) := by ring
    have h3 : min (1 + (k : ℝ) * (Φ x - 1 / 2)) 1 ≤ 0 := min_le_of_left_le (by linarith)
    unfold halfCutoff
    rw [max_eq_right h3]

/-- A cutoff of a Lipschitz functional is a bounded Lipschitz path functional. -/
theorem isBoundedLipschitzPathFunctional_halfCutoff_comp {Φ : (ℝ≥0 → ℂ) → ℝ} {L : ℝ}
    (hΦ : ∀ f g, |Φ f - Φ g| ≤ L * localUniformDist f g) (k : ℕ) :
    IsBoundedLipschitzPathFunctional fun f => halfCutoff k (Φ f) :=
  ⟨fun _ => abs_halfCutoff_le k _, k * L, fun f g => (abs_halfCutoff_sub_le k _ _).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hΦ f g) k.cast_nonneg)⟩

/-- The affine image `(F + 2)/3` of a bounded Lipschitz path functional, with values in `[1/3, 1]`. -/
theorem isBoundedLipschitzPathFunctional_affine {F : (ℝ≥0 → ℂ) → ℝ}
    (hF : IsBoundedLipschitzPathFunctional F) :
    IsBoundedLipschitzPathFunctional fun f => (F f + 2) / 3 := by
  obtain ⟨hb, L, hL⟩ := hF
  refine ⟨fun f => ?_, L / 3, fun f g => ?_⟩
  · have h := abs_le.1 (hb f)
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  · rw [show (F f + 2) / 3 - (F g + 2) / 3 = (F f - F g) / 3 by ring, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have h := hL f g
    calc |F f - F g| / 3 ≤ L * localUniformDist f g / 3 := by gcongr
      _ = L / 3 * localUniformDist f g := by ring

/-! ### Transfer of closed events through bounded Lipschitz functionals -/

/-- If bounded functionals `F k` of `Y` converge pointwise to the indicator of `A` and are almost everywhere strongly
measurable, their integrals converge to the probability that `Y ∈ A`. -/
theorem tendsto_integral_measureReal_of_tendsto_indicator {β : Type*} [MeasurableSpace β]
    {ρ : Measure β} [IsProbabilityMeasure ρ] {Y : β → ℝ≥0 → ℂ} {F : ℕ → (ℝ≥0 → ℂ) → ℝ}
    (hF : ∀ k f, |F k f| ≤ 1) {A : Set (ℝ≥0 → ℂ)}
    (hlim : ∀ f, Tendsto (fun k => F k f) atTop (𝓝 (A.indicator 1 f)))
    (hm : ∀ k, AEStronglyMeasurable (fun b => F k (Y b)) ρ) :
    Tendsto (fun k => ∫ b, F k (Y b) ∂ρ) atTop (𝓝 (ρ.real {b | Y b ∈ A})) := by
  have hlim' : ∀ᵐ b ∂ρ, Tendsto (fun k => F k (Y b)) atTop
      (𝓝 (A.indicator (1 : (ℝ≥0 → ℂ) → ℝ) (Y b))) :=
    ae_of_all _ fun b => hlim (Y b)
  have hmI : AEStronglyMeasurable (fun b => A.indicator (1 : (ℝ≥0 → ℂ) → ℝ) (Y b)) ρ :=
    aestronglyMeasurable_of_tendsto_ae atTop hm hlim'
  have hset : {b | Y b ∈ A} = (fun b => A.indicator (1 : (ℝ≥0 → ℂ) → ℝ) (Y b)) ⁻¹' {1} := by
    ext b
    by_cases h : Y b ∈ A <;> simp [h]
  have hnm : NullMeasurableSet {b | Y b ∈ A} ρ := by
    rw [hset]
    exact hmI.aemeasurable.nullMeasurableSet_preimage (measurableSet_singleton 1)
  have hI : ∫ b, A.indicator (1 : (ℝ≥0 → ℂ) → ℝ) (Y b) ∂ρ = ρ.real {b | Y b ∈ A} := by
    have h : (fun b => A.indicator (1 : (ℝ≥0 → ℂ) → ℝ) (Y b)) =
        {b | Y b ∈ A}.indicator fun _ => (1 : ℝ) := by
      ext b
      by_cases h : Y b ∈ A <;> simp [h]
    rw [h, integral_indicator₀ hnm, setIntegral_const, smul_eq_mul, mul_one]
  rw [← hI]
  exact tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hm (integrable_const 1)
    (fun k => ae_of_all _ fun b => by rw [Real.norm_eq_abs]; exact hF k (Y b)) hlim'

/-- If the integral of `(F + 2)/3` of `Y` under `ρ` equals its integral against a probability measure `μ`, then
`F ∘ Y` is `ρ`-almost everywhere strongly measurable: the common value is at least `1/3`, so it is not the value `0`
of a non-integrable function. -/
theorem aestronglyMeasurable_of_integral_affine_eq {β : Type*} [MeasurableSpace β] {ρ : Measure β}
    {μ : Measure (ContinuousPath ℂ)} [IsProbabilityMeasure μ] {Y : β → ℝ≥0 → ℂ} {F : (ℝ≥0 → ℂ) → ℝ}
    (hF : ∀ f, |F f| ≤ 1) (hG : IsBoundedLipschitzPathFunctional fun f => (F f + 2) / 3)
    (h : ∫ b, (F (Y b) + 2) / 3 ∂ρ = ∫ g, (F g + 2) / 3 ∂μ) :
    AEStronglyMeasurable (fun b => F (Y b)) ρ := by
  have hint : Integrable (fun g : ContinuousPath ℂ => (F g + 2) / 3) μ :=
    (blPathFunctionalBCF hG).integrable μ
  have hpos : 0 < ∫ g, (F g + 2) / 3 ∂μ := by
    have hle : ∀ g : ContinuousPath ℂ, (1 / 3 : ℝ) ≤ (F g + 2) / 3 := fun g => by
      have h1 := (abs_le.1 (hF g)).1
      linarith
    calc (0 : ℝ) < ∫ _g, (1 / 3 : ℝ) ∂μ := by simp
      _ ≤ ∫ g, (F g + 2) / 3 ∂μ := integral_mono (integrable_const _) hint hle
  have hYint : Integrable (fun b => (F (Y b) + 2) / 3) ρ := by
    by_contra hc
    rw [integral_undef hc] at h
    exact hpos.ne h
  have hkey : (fun b => F (Y b)) = fun b => 3 * ((F (Y b) + 2) / 3) - 2 := funext fun b => by ring
  have hc : Continuous fun x : ℝ => 3 * x - 2 := by fun_prop
  rw [hkey]
  exact hc.comp_aestronglyMeasurable hYint.aestronglyMeasurable

/-- **Transfer of an event through bounded Lipschitz functionals.**  If the integrals of bounded Lipschitz functionals
`F k` and `(F k + 2)/3` of `Y` under `ρ` agree with their integrals against a probability measure `μ` on continuous
paths, and `F k` converges pointwise to the indicator of `A`, then `ρ (Y ∈ A) = μ (A)`. -/
theorem measure_mem_eq_of_integral_eq {β : Type*} [MeasurableSpace β] {ρ : Measure β} [IsProbabilityMeasure ρ]
    {μ : Measure (ContinuousPath ℂ)} [IsProbabilityMeasure μ] {Y : β → ℝ≥0 → ℂ}
    {F : ℕ → (ℝ≥0 → ℂ) → ℝ} (hF : ∀ k, IsBoundedLipschitzPathFunctional (F k))
    (hG : ∀ k, IsBoundedLipschitzPathFunctional fun f => (F k f + 2) / 3)
    {A : Set (ℝ≥0 → ℂ)} (hlim : ∀ f, Tendsto (fun k => F k f) atTop (𝓝 (A.indicator 1 f)))
    (heq : ∀ k, ∫ b, F k (Y b) ∂ρ = ∫ g, F k g ∂μ)
    (heq' : ∀ k, ∫ b, (F k (Y b) + 2) / 3 ∂ρ = ∫ g, (F k g + 2) / 3 ∂μ) :
    ρ {b | Y b ∈ A} = μ {g : ContinuousPath ℂ | ⇑g ∈ A} := by
  have h1 := tendsto_integral_measureReal_of_tendsto_indicator (fun k => (hF k).1) hlim
    (fun k => aestronglyMeasurable_of_integral_affine_eq (hF k).1 (hG k) (heq' k))
  have h2 := tendsto_integral_measureReal_of_tendsto_indicator (ρ := μ)
    (Y := fun g : ContinuousPath ℂ => ⇑g) (fun k => (hF k).1) hlim
    (fun k => (continuous_blPathFunctional (hF k)).aestronglyMeasurable)
  have h3 := tendsto_nhds_unique (h1.congr heq) h2
  rwa [measureReal_def, measureReal_def,
    ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)] at h3

/-- **Transfer through the identification.**  If the origin value of the path-law field `Λ (D ω)` integrates every
bounded Lipschitz path functional as the quenched law of the rescaled Liouville Brownian motion from `0`, then for
every sequence of bounded Lipschitz functionals converging pointwise to the indicator of `A`, almost surely the
rescaled Liouville Brownian motion is in `A` with probability `Λ (D ω) 0 (A)`. -/
theorem ae_measure_rescaledLBMPath_mem_eq {Data : Type*} {S : MatedCRTEnv Ω} {D : Ω → Data}
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))}
    (hΛ : ∀ F (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
      ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion 0
        = ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) 0 : Measure (ContinuousPath ℂ)))
    {F : ℕ → (ℝ≥0 → ℂ) → ℝ} (hF : ∀ k, IsBoundedLipschitzPathFunctional (F k))
    {A : Set (ℝ≥0 → ℂ)} (hlim : ∀ f, Tendsto (fun k => F k f) atTop (𝓝 (A.indicator 1 f))) :
    ∀ᵐ ω ∂S.P, planarBrownianMotion 0 {b | rescaledLBMPath (S.clock ω) S.m₀ b ∈ A} =
      (Λ (D ω) 0 : Measure (ContinuousPath ℂ)) {g | ⇑g ∈ A} := by
  have hG : ∀ k, IsBoundedLipschitzPathFunctional fun f => (F k f + 2) / 3 := fun k =>
    isBoundedLipschitzPathFunctional_affine (hF k)
  filter_upwards [ae_all_iff.2 fun k => hΛ (F k) (hF k), ae_all_iff.2 fun k => hΛ _ (hG k)] with ω h1 h2
  exact measure_mem_eq_of_integral_eq (ρ := planarBrownianMotion 0)
    (μ := (Λ (D ω) 0 : Measure (ContinuousPath ℂ))) (Y := rescaledLBMPath (S.clock ω) S.m₀) hF hG hlim h1 h2

/-- The origin mixture of the law of `(D, Λ D)` charges a measurable set of paths as the mean of the origin values. -/
theorem originPathLaw_apply_of_eq_map {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data]
    [BorelSpace Data] {P : Measure Ω} {D : Ω → Data} (hD : Measurable D)
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛm : Measurable Λ)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    (hν : ν = P.map fun ω => (D ω, Λ (D ω))) {E : Set (ContinuousPath ℂ)} (hE : MeasurableSet E) :
    originPathLaw ν E = ∫⁻ ω, (Λ (D ω) 0 : Measure (ContinuousPath ℂ)) E ∂P := by
  subst hν
  have hκE : Measurable fun p : Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)) =>
      ((p.2 0 : ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) E :=
    (Measure.measurable_coe hE).comp measurable_originPathLawKernel
  have hmap : Measurable fun ω => (D ω, Λ (D ω)) := hD.prodMk (hΛm.comp hD)
  rw [originPathLaw, Measure.bind_apply hE measurable_originPathLawKernel.aemeasurable]
  exact lintegral_map hκE hmap

/-! ### The two hypotheses of `medianOf_exitCdf_originPathLaw_eq_one` -/

/-- **Regular exit under the origin mixture (`hreg`).**  Under the identification of `ν` as the law of `(D, Λ D)`,
with `Λ (D ω) 0` the quenched law of the rescaled Liouville Brownian motion from `0`, `originPathLaw ν`-almost every
path exits `B_{1/2}` regularly. -/
theorem ae_regularExit_originPathLaw_of_identification
    {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {D : Ω → Data} (hD : Measurable D)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛm : Measurable Λ)
    (hν : ν = S.P.map fun ω => (D ω, Λ (D ω)))
    (hΛ : ∀ F (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
      ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion 0
        = ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) 0 : Measure (ContinuousPath ℂ)))
    (hexit : BrownianOutwardExcursionAtExitStep) :
    ∀ᵐ g : ContinuousPath ℂ ∂(originPathLaw ν), RegularExit (Metric.ball (0 : ℂ) (1 / 2)) ⇑g := by
  let Φ : ℚ × ℚ → (ℝ≥0 → ℂ) → ℝ := fun p f =>
    min (truncRunningMax ((p.1 : ℝ).toNNReal) f) (1 - truncRunningMax ((p.2 : ℝ).toNNReal) f)
  have hreg0 := TruncatedLaws.ae_regularExit_rescaledLBM_noMassHyp hS (y := 0) (z := 0) (r := 1 / 2)
    (mem_ball_self (by norm_num)) hexit
  have hcont0 := TruncatedLaws.ae_continuous_rescaledLBMPath Ω S hS 0
  have hnull : ∀ p : ℚ × ℚ, 0 < p.1 → p.1 < p.2 →
      originPathLaw ν {g : ContinuousPath ℂ | 1 / 2 ≤ Φ p ⇑g} = 0 := by
    intro p hq hqr
    have hE : MeasurableSet {g : ContinuousPath ℂ | 1 / 2 ≤ Φ p ⇑g} :=
      measurableSet_le measurable_const ((continuous_truncRunningMax _).min
        (continuous_const.sub (continuous_truncRunningMax _))).measurable
    rw [originPathLaw_apply_of_eq_map hD hΛm hν hE]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    have hfam := ae_measure_rescaledLBMPath_mem_eq hΛ (F := fun k f => halfCutoff k (Φ p f))
      (fun k => isBoundedLipschitzPathFunctional_halfCutoff_comp (Φ := Φ p)
        (abs_min_truncRunningMax_sub_le ((p.1 : ℝ).toNNReal) ((p.2 : ℝ).toNNReal)) k)
      (fun f => tendsto_halfCutoff_indicator (Φ p) f)
    filter_upwards [hfam, hreg0, hcont0] with ω hω hR hC
    refine hω.symm.trans (measure_mono_null ?_ (ae_iff.1 (hR.and hC)))
    intro b hb
    show ¬ _
    intro hbad
    exact not_regularExit_of_half_le_min hbad.2 (Rat.cast_pos.2 hq) (Rat.cast_lt.2 hqr) hb hbad.1
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null fun p => measure_iUnion_null fun hp =>
    hnull p (And.left hp) (And.right hp))
  intro g hg
  obtain ⟨p, hp, hmem⟩ := exists_rat_half_le_min_of_not_regularExit hg
  exact mem_iUnion.2 ⟨p, mem_iUnion.2 ⟨hp, hmem⟩⟩

/-- **The exit-time distribution function of the origin mixture.**  Under the identification, the distribution
function of the exit time of `B_{1/2}` under `originPathLaw ν` is `s ↦ G (m₀ s)`, where `G` is the annealed
distribution function of the Liouville Brownian exit time of `B_{1/2}` from `0`. -/
theorem exitCdf_originPathLaw_eq_lintegral_of_identification
    {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : Ω → Data} (hD : Measurable D)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛm : Measurable Λ)
    (hν : ν = S.P.map fun ω => (D ω, Λ (D ω)))
    (hΛ : ∀ F (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
      ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion 0
        = ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) 0 : Measure (ContinuousPath ℂ)))
    (s : ℝ) (hs : 0 ≤ s) :
    exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν) s =
      ∫⁻ ω, planarBrownianMotion 0
        {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal (S.m₀ * s)} ∂S.P := by
  have hm : 0 < S.m₀ := hS.m₀_pos hγ hγ2
  have hE : MeasurableSet {g : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax s.toNNReal ⇑g} :=
    measurableSet_le measurable_const (continuous_truncRunningMax _).measurable
  have hset : exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν) s =
      originPathLaw ν {g : ContinuousPath ℂ | 1 / 2 ≤ truncRunningMax s.toNNReal ⇑g} := by
    unfold exitCdf
    congr 1
    ext g
    exact pathExitTime_ball_le_iff g.continuous s.toNNReal
  rw [hset, originPathLaw_apply_of_eq_map hD hΛm hν hE]
  refine lintegral_congr_ae ?_
  have hfam := ae_measure_rescaledLBMPath_mem_eq hΛ
    (F := fun k f => halfCutoff k (truncRunningMax s.toNNReal f))
    (fun k => isBoundedLipschitzPathFunctional_halfCutoff_comp (Φ := truncRunningMax s.toNNReal)
      (abs_truncRunningMax_sub_le s.toNNReal) k)
    (fun f => tendsto_halfCutoff_indicator (truncRunningMax s.toNNReal) f)
  filter_upwards [hfam, hS.isLQGClock] with ω hω hclk
  refine hω.symm.trans (measure_congr (Filter.eventuallyEqSet_iff.2 ?_))
  filter_upwards [(hclk 0).2] with b hb
  have h := half_le_truncRunningMax_rescaledLBMPath_iff hm hb s.toNNReal
  rw [Real.coe_toNNReal s hs] at h
  exact h

/-- **The lower median of the exit time of the origin mixture is one**, directly from the identification: the
distribution function is `s ↦ G (m₀ s)`, `m₀` is the lower median of `G`, and `G` exceeds `1/2` strictly beyond
`m₀`. -/
theorem medianOf_exitCdf_originPathLaw_eq_one_of_eq_map
    {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : Ω → Data} (hD : Measurable D)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛm : Measurable Λ)
    (hν : ν = S.P.map fun ω => (D ω, Λ (D ω)))
    (hΛ : ∀ F (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
      ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion 0
        = ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) 0 : Measure (ContinuousPath ℂ))) :
    medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν)) = 1 := by
  have hm : 0 < S.m₀ := hS.m₀_pos hγ hγ2
  set G : ℝ → ℝ≥0∞ := fun r => ∫⁻ ω, planarBrownianMotion 0
    {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal r} ∂S.P
  set H : ℝ → ℝ≥0∞ := exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν)
  have hH : ∀ s, 0 ≤ s → H s = G (S.m₀ * s) := fun s hs =>
    exitCdf_originPathLaw_eq_lintegral_of_identification hS hγ hγ2 hD hΛm hν hΛ s hs
  have hm₀ : S.m₀ = sInf {x : ℝ | 0 ≤ x ∧ (1 / 2 : ℝ≥0∞) ≤ G x} := rfl
  have hlow : ∀ m, 0 ≤ m → (1 / 2 : ℝ≥0∞) ≤ H m → 1 ≤ m := by
    intro m hm0 hmH
    by_contra hlt
    rw [not_le] at hlt
    rw [hH m hm0] at hmH
    have hmem : S.m₀ * m ∈ {x : ℝ | 0 ≤ x ∧ (1 / 2 : ℝ≥0∞) ≤ G x} := ⟨mul_nonneg hm.le hm0, hmH⟩
    have hle : S.m₀ ≤ S.m₀ * m := (le_of_eq hm₀).trans (csInf_le ⟨0, fun x hx => hx.1⟩ hmem)
    have hlt' : S.m₀ * m < S.m₀ * 1 := mul_lt_mul_of_pos_left hlt hm
    linarith
  have hup : ∀ m, 1 < m → 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ H m := fun m hm1 =>
    ⟨by linarith, by
      rw [hH m (by linarith)]
      exact (hS.half_lt_lintegral_exitTime_le_of_m₀_lt hγ hγ2 _ (lt_mul_of_one_lt_right hm hm1)).le⟩
  have hmed : medianOf H = sInf {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ H m} := rfl
  rw [hmed]
  apply le_antisymm
  · by_contra h
    rw [not_le] at h
    have hmem : (1 + sInf {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ H m}) / 2 ∈
        {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ H m} := hup _ (by linarith)
    have hbdd : BddBelow {m : ℝ | 0 ≤ m ∧ (1 / 2 : ℝ≥0∞) ≤ H m} := ⟨0, fun x hx => hx.1⟩
    have hle := csInf_le hbdd hmem
    linarith
  · exact le_csInf ⟨2, hup 2 one_lt_two⟩ fun m hm => hlow m hm.1 hm.2

/-- **Strict increase beyond the median under the origin mixture (`hstrict`).**  Under the identification, the
exit-time distribution function of `originPathLaw ν` from `B_{1/2}` is strictly above `1/2` to the right of its lower
median. -/
theorem half_lt_exitCdf_originPathLaw_of_medianOf_lt
    {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : Ω → Data} (hD : Measurable D)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))}
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛm : Measurable Λ)
    (hν : ν = S.P.map fun ω => (D ω, Λ (D ω)))
    (hΛ : ∀ F (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
      ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion 0
        = ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) 0 : Measure (ContinuousPath ℂ))) :
    ∀ s, medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν)) < s →
      (1 / 2 : ℝ≥0∞) < exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν) s := by
  intro s hs
  rw [medianOf_exitCdf_originPathLaw_eq_one_of_eq_map hS hγ hγ2 hD hΛm hν hΛ] at hs
  rw [exitCdf_originPathLaw_eq_lintegral_of_identification hS hγ hγ2 hD hΛm hν hΛ s (by linarith)]
  exact hS.half_lt_lintegral_exitTime_le_of_m₀_lt hγ hγ2 _
    (lt_mul_of_one_lt_right (hS.m₀_pos hγ hγ2) hs)

/-- **The exit-time median of the origin mixture of the limit law is one**, with the hypotheses `hreg` and `hstrict`
of `medianOf_exitCdf_originPathLaw_eq_one` discharged from the identification of `ν` as the law of `(D, Λ D)`
(`ae_regularExit_originPathLaw_of_identification`, `half_lt_exitCdf_originPathLaw_of_medianOf_lt`). -/
theorem medianOf_exitCdf_originPathLaw_eq_one_of_identification
    {Data : Type*} [TopologicalSpace Data] [MeasurableSpace Data] [BorelSpace Data]
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) {η' : Ω → C(ℝ, ℂ)} (hη' : Measurable η')
    (hae : ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω) {e : ℕ → ℝ} (he0 : ∀ n, 0 < e n) (he : Tendsto e atTop (𝓝 0))
    (hmod : ∀ R a : ℝ, 0 < a → ∃ δ > 0, ∀ᶠ n in atTop,
      S.P {ω | ENNReal.ofReal a < walkLawModulus S η' (e n) R δ ω} ≤ ENNReal.ofReal a)
    {a : ℕ → Ω → ℤ} (ha : ∀ n, Measurable (a n))
    (hav : ∀ n, ∀ᵐ ω ∂S.P, a n ω = vertexOf (e n) (S.η ω) 0)
    {D : Ω → Data} (hD : Measurable D)
    {ν : Measure (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ)))} [IsProbabilityMeasure ν]
    (hconv : ∀ f : (Data × C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))) →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f (D ω, interpWalkLaw S η' (e n) ω) ∂S.P) atTop (𝓝 (∫ p, f p ∂ν)))
    {Λ : Data → C(ℂ, ProbabilityMeasure (ContinuousPath ℂ))} (hΛm : Measurable Λ)
    (hν : ν = S.P.map fun ω => (D ω, Λ (D ω)))
    (hΛ : ∀ F (hF : IsBoundedLipschitzPathFunctional F), ∀ᵐ ω ∂S.P,
      ∫ b, F (rescaledLBMPath (S.clock ω) S.m₀ b) ∂planarBrownianMotion 0
        = ∫ q, blPathFunctionalBCF hF q ∂(Λ (D ω) 0 : Measure (ContinuousPath ℂ)))
    (hexit : BrownianOutwardExcursionAtExitStep)
    (hmε : Tendsto (fun n => S.mε (e n)) atTop atTop) :
    medianOf (exitCdf (Metric.ball (0 : ℂ) (1 / 2)) (originPathLaw ν)) = 1 :=
  medianOf_exitCdf_originPathLaw_eq_one hS hη' hae he0 he hmod ha hav hD hconv
    (ae_regularExit_originPathLaw_of_identification hS hD hΛm hν hΛ hexit)
    (half_lt_exitCdf_originPathLaw_of_medianOf_lt hS hγ hγ2 hD hΛm hν hΛ) hmε

end MatedCRT.FirstPass.Derived
