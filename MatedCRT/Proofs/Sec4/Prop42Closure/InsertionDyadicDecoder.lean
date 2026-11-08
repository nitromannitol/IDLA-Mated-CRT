import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionCoordinate
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.PiSystem

/-!
# Measurable dyadic decoder on continuous circle processes (steps3:501-528)

The written constructor (steps3:501-528) takes the dyadic vague limit of the approximations
`2^{-kγ²/2} exp{γ[u(2^{-k},z) - α log max(2^{-k},|z|)]} dz` on the continuous positive-radius processes
`u ∈ 𝒞`, uses only countably many compactly supported tests, and sets the decoder to the vague limit on the
Borel convergence set and to `0` off it. This file formalizes that constructor on `ContCircle`, the continuous
processes with the evaluation σ-algebra. The limit measure is produced by the Riesz–Markov–Kakutani theorem.

Terminology: vague convergence of Radon measures and the dyadic insertion limit (Duplantier–Sheffield 2011,
Prop. 1.1; Berestycki–Powell); test functions are compactly supported continuous functions (Armitage–Gardiner).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT

/-- The continuous positive-radius processes `𝒞` of steps3:501-528: the domain of the measurable decoder. Its
measurable structure is the subtype σ-algebra of the product σ-algebra, i.e. the evaluation σ-algebra. -/
abbrev ContCircle := {u : Set.Ioi (0 : ℝ) × ℂ → ℝ // Continuous u}

/-- Dyadic density of the insertion-`α` approximation at scale `2^{-k}` (steps3:501-506):
`2^{-kγ²/2} exp{γ[u(2^{-k},z) - α log max(2^{-k},|z|)]}`, written with the positive part `log⁺` of `|z|/2^{-k}`. -/
noncomputable def dyadicDens (γ α : ℝ) (k : ℕ) (u : ContCircle) (z : ℂ) : ℝ :=
  dyadicScale k ^ (γ ^ 2 / 2) *
    Real.exp (γ * (procExt u.1 (dyadicScale k) z -
      α * (Real.log (dyadicScale k) + Real.posLog ((dyadicScale k)⁻¹ * ‖z‖))))

/-- The dyadic approximation measure of the α-field of a continuous process `u` at scale `2^{-k}`. -/
noncomputable def dyadicApprox (γ α : ℝ) (u : ContCircle) (k : ℕ) : Measure ℂ :=
  lqgApprox γ (fieldCircleAverage α (procExt u.1)) (dyadicScale k)

/-- The test integral `∫ f d(dyadicApprox)` along the dyadic scales. -/
noncomputable def dyadicTest (γ α : ℝ) (f : ℂ → ℝ) (u : ContCircle) (k : ℕ) : ℝ :=
  ∫ z, f z ∂(dyadicApprox γ α u k)

theorem dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := by
  unfold dyadicScale
  positivity

theorem procExt_pos_eq (u : Set.Ioi (0 : ℝ) × ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    procExt u r z = u (⟨r, hr⟩, z) := by
  simp [procExt, hr]

/-- The α-field circle average at positive radius in closed form: `h_r(z) - α log max(r,|z|)`
(from the circle-average identity `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`). -/
theorem fieldCircleAverage_eq_posLog {α r : ℝ} {h : ℝ → ℂ → ℝ} (hr : 0 < r) (z : ℂ) :
    fieldCircleAverage α h r z = h r z - α * (Real.log r + Real.posLog (r⁻¹ * ‖z‖)) := by
  have h0 := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z) (R := r) hr.ne'
  simp only [sub_zero] at h0
  unfold fieldCircleAverage
  rw [h0]

/-- Joint measurability of `(u, z) ↦ u(r, z)` on `ContCircle × ℂ` (a Carathéodory function: continuous in `z`,
measurable in `u`). -/
theorem measurable_procExt_eval {r : ℝ} (hr : 0 < r) :
    Measurable (fun p : ContCircle × ℂ => procExt p.1.1 r p.2) := by
  have hU : Measurable (Function.uncurry fun (z : ℂ) (w : ContCircle) => procExt w.1 r z) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun w => ?_) (fun z => ?_)
    · show Continuous (fun z : ℂ => procExt w.1 r z)
      have : (fun z : ℂ => procExt w.1 r z) = fun z => w.1 (⟨r, hr⟩, z) := by
        funext z
        exact procExt_pos_eq w.1 hr z
      rw [this]
      exact w.2.comp (Continuous.prodMk continuous_const continuous_id)
    · show Measurable (fun w : ContCircle => procExt w.1 r z)
      have : (fun w : ContCircle => procExt w.1 r z) = fun w => w.1 (⟨r, hr⟩, z) := by
        funext w
        exact procExt_pos_eq w.1 hr z
      rw [this]
      exact (measurable_pi_apply ((⟨r, hr⟩ : Set.Ioi (0 : ℝ)), z)).comp measurable_subtype_coe
  exact hU.comp measurable_swap

theorem measurable_dyadicDens (γ α : ℝ) (k : ℕ) :
    Measurable (fun p : ContCircle × ℂ => dyadicDens γ α k p.1 p.2) := by
  have h1 : Measurable (fun p : ContCircle × ℂ => procExt p.1.1 (dyadicScale k) p.2) :=
    measurable_procExt_eval (dyadicScale_pos k)
  have h2 : Measurable (fun p : ContCircle × ℂ => Real.posLog ((dyadicScale k)⁻¹ * ‖p.2‖)) :=
    Real.continuous_posLog.measurable.comp (measurable_const.mul measurable_snd.norm)
  unfold dyadicDens
  exact (measurable_const.pow_const _).mul (Real.measurable_exp.comp (measurable_const.mul
    (h1.sub (measurable_const.mul (measurable_const.add h2)))))

theorem dyadicApprox_eq (γ α : ℝ) (u : ContCircle) (k : ℕ) :
    dyadicApprox γ α u k = volume.withDensity (fun z => ENNReal.ofReal (dyadicDens γ α k u z)) := by
  unfold dyadicApprox lqgApprox dyadicDens
  simp only [fieldCircleAverage_eq_posLog (dyadicScale_pos k)]

theorem dyadicTest_eq_integral (γ α : ℝ) (f : ℂ → ℝ) (u : ContCircle) (k : ℕ) :
    dyadicTest γ α f u k = ∫ z, (ENNReal.ofReal (dyadicDens γ α k u z)).toReal • f z := by
  unfold dyadicTest
  rw [dyadicApprox_eq, integral_withDensity_eq_integral_toReal_smul₀]
  · exact ((measurable_dyadicDens γ α k).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal.aemeasurable
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-- The test integrals of the dyadic approximations are measurable in the process `u`. -/
theorem measurable_dyadicTest (γ α : ℝ) {f : ℂ → ℝ} (hf : Continuous f) (k : ℕ) :
    Measurable (fun u : ContCircle => dyadicTest γ α f u k) := by
  have hF : StronglyMeasurable
      (fun p : ContCircle × ℂ => (ENNReal.ofReal (dyadicDens γ α k p.1 p.2)).toReal • f p.2) := by
    refine Measurable.stronglyMeasurable ?_
    exact ((measurable_dyadicDens γ α k).ennreal_ofReal.ennreal_toReal).smul (hf.measurable.comp measurable_snd)
  have hG := hF.integral_prod_right' (ν := volume)
  have hfun : (fun u : ContCircle => dyadicTest γ α f u k) =
      fun u => ∫ z, (ENNReal.ofReal (dyadicDens γ α k u z)).toReal • f z :=
    funext fun u => dyadicTest_eq_integral γ α f u k
  rw [hfun]
  exact hG.measurable

/-! ## Radial retraction and cutoff: extension of tests from a closed ball -/

/-- Radial retraction onto the closed ball of radius `R`: the identity on the ball, radial projection outside. -/
noncomputable def radialRetr (R : ℝ) (z : ℂ) : ℂ := min 1 (R / ‖z‖) • z

/-- Radial cutoff: `1` on the closed ball of radius `R`, `0` outside the closed ball of radius `R + 1`. -/
noncomputable def radialCutoff (R : ℝ) (z : ℂ) : ℝ := max 0 (min 1 (R + 1 - ‖z‖))

theorem radialRetr_eq_self {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) : radialRetr R z = z := by
  unfold radialRetr
  by_cases h0 : z = 0
  · subst h0
    simp
  · have hpos : 0 < ‖z‖ := norm_pos_iff.2 h0
    have h1 : 1 ≤ R / ‖z‖ := by
      rw [le_div_iff₀ hpos]
      linarith
    rw [min_eq_left h1, one_smul]

theorem norm_radialRetr_of_lt {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : R < ‖z‖) :
    ‖radialRetr R z‖ = R := by
  unfold radialRetr
  have hpos : 0 < ‖z‖ := lt_trans hR hz
  have h1 : R / ‖z‖ ≤ 1 := by
    rw [div_le_one hpos]
    exact hz.le
  rw [min_eq_right h1, norm_smul, Real.norm_of_nonneg (div_nonneg hR.le hpos.le)]
  exact div_mul_cancel₀ R hpos.ne'

theorem norm_radialRetr_le {R : ℝ} (hR : 0 ≤ R) (z : ℂ) : ‖radialRetr R z‖ ≤ R := by
  unfold radialRetr
  rw [norm_smul, Real.norm_of_nonneg (le_min zero_le_one (div_nonneg hR (norm_nonneg z)))]
  rcases eq_or_ne ‖z‖ 0 with h | h
  · simp [h, hR]
  · calc min 1 (R / ‖z‖) * ‖z‖ ≤ (R / ‖z‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg z)
      _ = R := div_mul_cancel₀ R h

theorem radialRetr_mem_closedBall {R : ℝ} (hR : 0 ≤ R) (z : ℂ) :
    radialRetr R z ∈ Metric.closedBall (0 : ℂ) R := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_radialRetr_le hR z

theorem continuous_radialRetr {R : ℝ} (hR : 0 < R) : Continuous (radialRetr R) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    refine continuousAt_id.congr ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with w hw
    have hw' : ‖w‖ ≤ R := by
      rw [mem_ball_zero_iff] at hw
      exact hw.le
    exact (radialRetr_eq_self hw').symm
  · exact (continuousAt_const.min (continuousAt_const.div continuous_norm.continuousAt
      (norm_ne_zero_iff.2 hz))).smul continuousAt_id

theorem continuous_radialCutoff (R : ℝ) : Continuous (radialCutoff R) :=
  (continuous_const).max ((continuous_const.min (continuous_const.sub continuous_norm)))

theorem radialCutoff_eq_one {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) : radialCutoff R z = 1 := by
  unfold radialCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem radialCutoff_eq_zero {R : ℝ} {z : ℂ} (hz : R + 1 < ‖z‖) : radialCutoff R z = 0 := by
  unfold radialCutoff
  rw [min_eq_right (by linarith : R + 1 - ‖z‖ ≤ 1), max_eq_left (by linarith)]

theorem radialCutoff_nonneg (R : ℝ) (z : ℂ) : 0 ≤ radialCutoff R z :=
  le_max_left _ _

theorem radialCutoff_le_one (R : ℝ) (z : ℂ) : radialCutoff R z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- Extension of `g ∈ C(closedBall 0 R, ℝ)` to `ℂ`: the radial retraction composed with `g`, cut off at radius
`R + 1`. It agrees with `g` on the closed ball of radius `R` and vanishes outside the closed ball of radius `R+1`. -/
noncomputable def extendCut (R : ℝ) (hR : 0 ≤ R) (g : C(Metric.closedBall (0 : ℂ) R, ℝ)) (z : ℂ) : ℝ :=
  radialCutoff R z * g ⟨radialRetr R z, radialRetr_mem_closedBall hR z⟩

theorem continuous_extendCut {R : ℝ} (hR : 0 < R) (g : C(Metric.closedBall (0 : ℂ) R, ℝ)) :
    Continuous (extendCut R hR.le g) :=
  (continuous_radialCutoff R).mul
    (g.continuous.comp (Continuous.subtype_mk (continuous_radialRetr hR) _))

theorem hasCompactSupport_extendCut {R : ℝ} (hR : 0 ≤ R) (g : C(Metric.closedBall (0 : ℂ) R, ℝ)) :
    HasCompactSupport (extendCut R hR g) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 1))
  intro z hz
  have hlt : R + 1 < ‖z‖ := by
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    exact hz
  unfold extendCut
  rw [radialCutoff_eq_zero hlt, zero_mul]

/-! ## The countable dense family of compactly supported tests -/

/-- The compactly supported test function on `ℂ` attached to `g ∈ C(closedBall 0 (m+2), ℝ)`. -/
noncomputable def extendTest (m : ℕ) (g : C(Metric.closedBall (0 : ℂ) ((m : ℝ) + 2), ℝ)) :
    CompactlySupportedContinuousMap ℂ ℝ where
  toContinuousMap := ⟨extendCut ((m : ℝ) + 2) (by positivity) g,
    continuous_extendCut (by positivity) g⟩
  hasCompactSupport' := hasCompactSupport_extendCut (by positivity) g

/-- A countable dense subset of `C(closedBall 0 (m+2), ℝ)` (separability of the continuous functions on a
compact metric space). -/
noncomputable def levelDense (m : ℕ) : Set C(Metric.closedBall (0 : ℂ) ((m : ℝ) + 2), ℝ) :=
  (TopologicalSpace.exists_countable_dense C(Metric.closedBall (0 : ℂ) ((m : ℝ) + 2), ℝ)).choose

theorem levelDense_countable (m : ℕ) : (levelDense m).Countable :=
  (TopologicalSpace.exists_countable_dense C(Metric.closedBall (0 : ℂ) ((m : ℝ) + 2), ℝ)).choose_spec.1

theorem levelDense_dense (m : ℕ) : Dense (levelDense m) :=
  (TopologicalSpace.exists_countable_dense C(Metric.closedBall (0 : ℂ) ((m : ℝ) + 2), ℝ)).choose_spec.2

/-- The countable family of compactly supported tests (steps3:501-528, "countable dense collection of compact
tests together with cutoff tests on a compact exhaustion"). -/
noncomputable def testFamily : Set (CompactlySupportedContinuousMap ℂ ℝ) :=
  ⋃ m : ℕ, (extendTest m) '' (levelDense m)

theorem testFamily_countable : testFamily.Countable :=
  Set.countable_iUnion fun m => (levelDense_countable m).image _

theorem extendTest_mem_testFamily (m : ℕ) {g : C(Metric.closedBall (0 : ℂ) ((m : ℝ) + 2), ℝ)}
    (hg : g ∈ levelDense m) : extendTest m g ∈ testFamily :=
  Set.mem_iUnion.2 ⟨m, Set.mem_image_of_mem _ hg⟩

theorem extendTest_apply (m : ℕ) (g : C(Metric.closedBall (0 : ℂ) ((m : ℝ) + 2), ℝ)) (z : ℂ) :
    extendTest m g z = extendCut ((m : ℝ) + 2) (by positivity) g z := rfl

theorem continuous_dyadicDens (γ α : ℝ) (k : ℕ) (u : ContCircle) :
    Continuous (fun z => dyadicDens γ α k u z) := by
  have hc : Continuous (fun z : ℂ => procExt u.1 (dyadicScale k) z) := by
    have : (fun z : ℂ => procExt u.1 (dyadicScale k) z) =
        fun z => u.1 (⟨dyadicScale k, dyadicScale_pos k⟩, z) := by
      funext z
      exact procExt_pos_eq u.1 (dyadicScale_pos k) z
    rw [this]
    exact u.2.comp (Continuous.prodMk continuous_const continuous_id)
  unfold dyadicDens
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
    (hc.sub (continuous_const.mul (continuous_const.add
      (Real.continuous_posLog.comp (continuous_const.mul continuous_norm)))))))

theorem isLocallyFiniteMeasure_dyadicApprox (γ α : ℝ) (u : ContCircle) (k : ℕ) :
    IsLocallyFiniteMeasure (dyadicApprox γ α u k) := by
  rw [dyadicApprox_eq]
  exact IsLocallyFiniteMeasure.withDensity_ofReal (continuous_dyadicDens γ α k u)

theorem exists_natBall_tsupport (f : CompactlySupportedContinuousMap ℂ ℝ) :
    ∃ m : ℕ, tsupport f ⊆ Metric.closedBall (0 : ℂ) m := by
  obtain ⟨r, hr⟩ := (f.hasCompactSupport.isCompact.isBounded).subset_closedBall (0 : ℂ)
  obtain ⟨m, hm⟩ := exists_nat_ge r
  exact ⟨m, hr.trans (Metric.closedBall_subset_closedBall hm)⟩

theorem eq_zero_of_norm_gt {f : ℂ → ℝ} {m : ℝ} (hf : tsupport f ⊆ Metric.closedBall (0 : ℂ) m)
    {z : ℂ} (hz : m < ‖z‖) : f z = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hzt
  have h := hf hzt
  rw [Metric.mem_closedBall, dist_zero_right] at h
  linarith

/-- Mean-value-type bound: `|∫ h dν| ≤ δ ν(B)` for `|h| ≤ δ` and `h = 0` off `B`. -/
theorem abs_integral_le_mul_measure {ν : Measure ℂ} {h : ℂ → ℝ} {B : Set ℂ} {δ : ℝ}
    (hB : MeasurableSet B) (hh : ∀ z, |h z| ≤ δ) (hzero : ∀ z, z ∉ B → h z = 0)
    (hfin : ν B ≠ ⊤) :
    |∫ z, h z ∂ν| ≤ δ * (ν B).toReal := by
  have hIB : Integrable (B.indicator fun _ => δ) ν :=
    (integrable_indicator_iff hB).2 (integrableOn_const hfin)
  have key : ‖∫ z, h z ∂ν‖ ≤ ∫ z, B.indicator (fun _ => δ) z ∂ν := by
    refine norm_integral_le_of_norm_le hIB (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      exact (Real.norm_eq_abs _).le.trans (hh z)
    · rw [Set.indicator_of_notMem hz, hzero z hz, norm_zero]
  rw [integral_indicator_const δ hB, Real.norm_eq_abs, smul_eq_mul] at key
  rw [mul_comm]
  exact key

/-- The convergence of the dyadic test integrals of `f` along the dyadic scales. -/
def DyadicConvergent (γ α : ℝ) (f : ℂ → ℝ) (u : ContCircle) : Prop :=
  ∃ L : ℝ, Tendsto (fun k : ℕ => dyadicTest γ α f u k) atTop (𝓝 L)

/-- Uniform local mass bound along the dyadic scales: `sup_k ν_k(B(0,ρ)) < ∞` for every radius `ρ`. -/
def DyadicMassBounded (γ α : ℝ) (u : ContCircle) : Prop :=
  ∀ ρ : ℕ, ∃ N : ℕ, ∀ k : ℕ, dyadicApprox γ α u k (Metric.closedBall (0 : ℂ) ρ) ≤ (N : ℝ≥0∞)

/-- The convergence set of the decoder (steps3:501-528): convergence on the countable test family together with
uniform local mass bounds. -/
def DyadicConvSet (γ α : ℝ) : Set ContCircle :=
  {u | (∀ f ∈ testFamily, DyadicConvergent γ α f u) ∧ DyadicMassBounded γ α u}

/-- Density of the countable test family (steps3:501-528): every compactly supported test supported in
`closedBall 0 m` is uniformly approximated, within `δ`, by a member of `testFamily` vanishing beyond radius `m+3`. -/
theorem exists_testFamily_approx (f : CompactlySupportedContinuousMap ℂ ℝ) {m : ℕ}
    (hm : tsupport f ⊆ Metric.closedBall (0 : ℂ) m) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g ∈ testFamily, (∀ z, |f z - g z| ≤ δ) ∧ ∀ z, (m : ℝ) + 3 < ‖z‖ → g z = 0 := by
  have hR0 : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
  let F : C(Metric.closedBall (0 : ℂ) ((m : ℝ) + 2), ℝ) :=
    ⟨fun z => f z.1, f.continuous.comp continuous_subtype_val⟩
  obtain ⟨g0, hg0, hdist⟩ := (levelDense_dense m).exists_dist_lt F hδ
  have hF : ∀ w : Metric.closedBall (0 : ℂ) ((m : ℝ) + 2), |f w.1 - g0 w| ≤ δ := by
    intro w
    have h1 := ContinuousMap.dist_apply_le_dist (f := F) (g := g0) w
    rw [Real.dist_eq] at h1
    exact h1.trans hdist.le
  refine ⟨extendTest m g0, extendTest_mem_testFamily m hg0, ?_, ?_⟩
  · intro z
    rw [extendTest_apply]
    unfold extendCut
    rcases le_or_gt ‖z‖ ((m : ℝ) + 2) with h1 | h1
    · have hz : z ∈ Metric.closedBall (0 : ℂ) ((m : ℝ) + 2) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact h1
      rw [radialCutoff_eq_one h1, one_mul]
      have hretr : (⟨radialRetr ((m : ℝ) + 2) z, radialRetr_mem_closedBall hR0 z⟩ :
          Metric.closedBall (0 : ℂ) ((m : ℝ) + 2)) = ⟨z, hz⟩ :=
        Subtype.ext (radialRetr_eq_self h1)
      rw [hretr]
      exact hF ⟨z, hz⟩
    · have hw : ‖radialRetr ((m : ℝ) + 2) z‖ = (m : ℝ) + 2 :=
        norm_radialRetr_of_lt (by positivity) h1
      have hwmem := radialRetr_mem_closedBall hR0 z
      have hfw : f (radialRetr ((m : ℝ) + 2) z) = 0 :=
        eq_zero_of_norm_gt hm (by rw [hw]; linarith)
      have hgw : |g0 ⟨radialRetr ((m : ℝ) + 2) z, hwmem⟩| ≤ δ := by
        have h2 : |f (radialRetr ((m : ℝ) + 2) z) - g0 ⟨radialRetr ((m : ℝ) + 2) z, hwmem⟩| ≤ δ :=
          hF ⟨radialRetr ((m : ℝ) + 2) z, hwmem⟩
        rw [hfw, zero_sub, abs_neg] at h2
        exact h2
      rw [eq_zero_of_norm_gt hm (by linarith : (m : ℝ) < ‖z‖), zero_sub, abs_neg, abs_mul,
        abs_of_nonneg (radialCutoff_nonneg _ z)]
      calc radialCutoff ((m : ℝ) + 2) z * |g0 ⟨radialRetr ((m : ℝ) + 2) z, hwmem⟩|
          ≤ 1 * |g0 ⟨radialRetr ((m : ℝ) + 2) z, hwmem⟩| :=
            mul_le_mul_of_nonneg_right (radialCutoff_le_one _ z) (abs_nonneg _)
        _ ≤ δ := by
            rw [one_mul]
            exact hgw
  · intro z hz
    rw [extendTest_apply]
    unfold extendCut
    rw [radialCutoff_eq_zero (R := (m : ℝ) + 2) (z := z) (by linarith), zero_mul]

/-- Uniform local mass bound from a vague limit: if the test integrals of all continuous compactly supported functions
converge along the dyadic scales, then the approximating masses of balls are bounded. -/
theorem dyadicMassBounded_of_tendsto {γ α : ℝ} {u : ContCircle} {m : Measure ℂ}
    (hm : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k : ℕ => dyadicTest γ α f u k) atTop (𝓝 (∫ z, f z ∂m))) :
    DyadicMassBounded γ α u := by
  intro ρ
  have hcont : Continuous (radialCutoff (ρ : ℝ)) := continuous_radialCutoff _
  have hcs : HasCompactSupport (radialCutoff (ρ : ℝ)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ((ρ : ℝ) + 1))
    intro z hz
    apply radialCutoff_eq_zero
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    exact hz
  obtain ⟨B, hB⟩ := (hm _ hcont hcs).bddAbove_range
  obtain ⟨N, hN⟩ := exists_nat_ge B
  refine ⟨N, fun k => ?_⟩
  have := isLocallyFiniteMeasure_dyadicApprox γ α u k
  have hint : Integrable (radialCutoff (ρ : ℝ)) (dyadicApprox γ α u k) :=
    hcont.integrable_of_hasCompactSupport hcs
  have hnonneg : 0 ≤ᵐ[dyadicApprox γ α u k] radialCutoff (ρ : ℝ) :=
    Eventually.of_forall (radialCutoff_nonneg _)
  have h1 : dyadicApprox γ α u k (Metric.closedBall (0 : ℂ) ρ) ≤
      ∫⁻ z, ENNReal.ofReal (radialCutoff (ρ : ℝ) z) ∂(dyadicApprox γ α u k) := by
    rw [← lintegral_indicator_one measurableSet_closedBall]
    apply lintegral_mono
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) ρ
    · have hz' : ‖z‖ ≤ (ρ : ℝ) := by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        exact hz
      rw [Set.indicator_of_mem hz, Pi.one_apply]
      show (1 : ℝ≥0∞) ≤ ENNReal.ofReal (radialCutoff (ρ : ℝ) z)
      rw [radialCutoff_eq_one hz', ENNReal.ofReal_one]
    · rw [Set.indicator_of_notMem hz]
      exact zero_le
  have h2 : ∫⁻ z, ENNReal.ofReal (radialCutoff (ρ : ℝ) z) ∂(dyadicApprox γ α u k) =
      ENNReal.ofReal (dyadicTest γ α (radialCutoff (ρ : ℝ)) u k) := by
    unfold dyadicTest
    rw [ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  calc dyadicApprox γ α u k (Metric.closedBall (0 : ℂ) ρ)
      ≤ ENNReal.ofReal (dyadicTest γ α (radialCutoff (ρ : ℝ)) u k) := h1.trans_eq h2
    _ ≤ ENNReal.ofReal N := ENNReal.ofReal_le_ofReal ((hB ⟨k, rfl⟩).trans hN)
    _ = (N : ℝ≥0∞) := ENNReal.ofReal_natCast N

/-- **Convergence for all tests from the countable family.** A point of the convergence set has convergent test
integrals for every compactly supported continuous test (steps3:501-528: "convergence for a countable dense collection
of compact tests, together with cutoff tests on a compact exhaustion, is equivalent to vague convergence"). -/
theorem dyadicConvergent_of_mem {γ α : ℝ} {u : ContCircle} (hu : u ∈ DyadicConvSet γ α)
    (f : CompactlySupportedContinuousMap ℂ ℝ) : DyadicConvergent γ α f u := by
  obtain ⟨hF, hM⟩ := hu
  obtain ⟨m, hm⟩ := exists_natBall_tsupport f
  obtain ⟨N, hN⟩ := hM (m + 3)
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  unfold DyadicConvergent
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  set δ : ℝ := ε / (4 * ((N : ℝ) + 1)) with hδdef
  have hδpos : 0 < δ := by positivity
  obtain ⟨g, hg, hfg, hgz⟩ := exists_testFamily_approx f hm hδpos
  obtain ⟨Lg, hLg⟩ := hF g hg
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.1 hLg.cauchySeq (ε / 2) (by positivity)
  have hbound : ∀ k : ℕ, |dyadicTest γ α f u k - dyadicTest γ α g u k| ≤ δ * N := by
    intro k
    have := isLocallyFiniteMeasure_dyadicApprox γ α u k
    have hfc : Continuous (fun z : ℂ => f z) := f.continuous
    have hfs : HasCompactSupport (fun z : ℂ => f z) := f.hasCompactSupport
    have hgc : Continuous (fun z : ℂ => g z) := g.continuous
    have hgs : HasCompactSupport (fun z : ℂ => g z) := g.hasCompactSupport
    have hdiff : dyadicTest γ α f u k - dyadicTest γ α g u k =
        ∫ z, (f z - g z) ∂(dyadicApprox γ α u k) := by
      unfold dyadicTest
      exact (integral_sub (hfc.integrable_of_hasCompactSupport hfs)
        (hgc.integrable_of_hasCompactSupport hgs)).symm
    have hfin : dyadicApprox γ α u k (Metric.closedBall (0 : ℂ) (((m + 3 : ℕ)) : ℝ)) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (hN k)
    rw [hdiff]
    refine (abs_integral_le_mul_measure (h := fun z => f z - g z) (δ := δ) measurableSet_closedBall
      ?_ ?_ hfin).trans ?_
    · intro z
      exact hfg z
    · intro z hz
      have hz' : (m : ℝ) + 3 < ‖z‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
        exact_mod_cast hz
      have hfz0 : f z = 0 := eq_zero_of_norm_gt hm (by linarith)
      rw [hfz0, hgz z hz', sub_zero]
    · apply mul_le_mul_of_nonneg_left _ hδpos.le
      have := (ENNReal.toReal_le_toReal hfin (ENNReal.natCast_ne_top N)).2 (hN k)
      simpa using this
  have hδN : δ * N < ε / 4 := by
    have hNlt : (N : ℝ) / ((N : ℝ) + 1) < 1 := by
      rw [div_lt_one hNpos]
      linarith
    have heq : δ * N = ε / 4 * ((N : ℝ) / ((N : ℝ) + 1)) := by
      rw [hδdef]
      field_simp
    rw [heq]
    exact mul_lt_of_lt_one_right (by positivity) hNlt
  refine ⟨K, fun a ha b hb => ?_⟩
  have hgC := hK a ha b hb
  rw [Real.dist_eq] at hgC ⊢
  have h1 := hbound a
  have h2 := hbound b
  have htri : |dyadicTest γ α f u a - dyadicTest γ α f u b| ≤
      |dyadicTest γ α f u a - dyadicTest γ α g u a| +
        |dyadicTest γ α g u a - dyadicTest γ α f u b| := abs_sub_le _ _ _
  have htri2 : |dyadicTest γ α g u a - dyadicTest γ α f u b| ≤
      |dyadicTest γ α g u a - dyadicTest γ α g u b| +
        |dyadicTest γ α g u b - dyadicTest γ α f u b| := abs_sub_le _ _ _
  have hsymm : |dyadicTest γ α g u b - dyadicTest γ α f u b| =
      |dyadicTest γ α f u b - dyadicTest γ α g u b| := abs_sub_comm _ _
  linarith

/-! ## The convergence set is Borel; the limit functional and the Riesz measure -/

theorem measurable_dyadicApprox_ball (γ α : ℝ) (k : ℕ) {B : Set ℂ} (hB : MeasurableSet B) :
    Measurable (fun u : ContCircle => dyadicApprox γ α u k B) := by
  have hdens := (measurable_dyadicDens γ α k).ennreal_ofReal
  have hset : MeasurableSet (Prod.snd ⁻¹' B : Set (ContCircle × ℂ)) := measurable_snd hB
  have hF : Measurable (fun p : ContCircle × ℂ =>
      B.indicator (fun z => ENNReal.ofReal (dyadicDens γ α k p.1 z)) p.2) := by
    have h := hdens.indicator hset
    have heq : (fun p : ContCircle × ℂ =>
        B.indicator (fun z => ENNReal.ofReal (dyadicDens γ α k p.1 z)) p.2) =
        (Prod.snd ⁻¹' B).indicator (fun p : ContCircle × ℂ => ENNReal.ofReal (dyadicDens γ α k p.1 p.2)) := by
      funext p
      rfl
    rw [heq]
    exact h
  have heq2 : (fun u : ContCircle => dyadicApprox γ α u k B) = fun u =>
      ∫⁻ z, B.indicator (fun z => ENNReal.ofReal (dyadicDens γ α k u z)) z := by
    funext u
    rw [dyadicApprox_eq, withDensity_apply _ hB, lintegral_indicator hB]
  rw [heq2]
  exact Measurable.lintegral_prod_right (ν := volume) hF

/-- The convergence set is Borel: countably many measurable convergence conditions and countably many mass
conditions (steps3:501-528, "the set where the sequence converges is Borel"). -/
theorem measurableSet_dyadicConvSet (γ α : ℝ) : MeasurableSet (DyadicConvSet γ α) := by
  have h1 : MeasurableSet {u : ContCircle | ∀ f ∈ testFamily, DyadicConvergent γ α f u} := by
    have heq : {u : ContCircle | ∀ f ∈ testFamily, DyadicConvergent γ α f u} =
        ⋂ f ∈ testFamily, {u : ContCircle | ∃ c : ℝ,
          Tendsto (fun k : ℕ => dyadicTest γ α f u k) atTop (𝓝 c)} := by
      ext u
      simp [DyadicConvergent]
    rw [heq]
    refine MeasurableSet.biInter testFamily_countable (fun f _ => ?_)
    have hfc : Continuous (fun z : ℂ => f z) := f.continuous
    exact measurableSet_exists_tendsto (fun k : ℕ => measurable_dyadicTest γ α hfc k)
  have h2 : MeasurableSet {u : ContCircle | DyadicMassBounded γ α u} := by
    have heq : {u : ContCircle | DyadicMassBounded γ α u} =
        ⋂ ρ : ℕ, ⋃ N : ℕ, ⋂ k : ℕ,
          {u : ContCircle | dyadicApprox γ α u k (Metric.closedBall (0 : ℂ) ρ) ≤ (N : ℝ≥0∞)} := by
      ext u
      simp only [DyadicMassBounded, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [heq]
    refine MeasurableSet.iInter fun ρ => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun k => ?_
    exact measurableSet_le (measurable_dyadicApprox_ball γ α k measurableSet_closedBall) measurable_const
  exact h1.inter h2

/-- The limit of the test integrals along the dyadic scales (meaningful on the convergence set). -/
noncomputable def dyadicLimit (γ α : ℝ) (f : ℂ → ℝ) (u : ContCircle) : ℝ :=
  limUnder atTop (fun k : ℕ => dyadicTest γ α f u k)

theorem tendsto_dyadicLimit {γ α : ℝ} {u : ContCircle} {f : ℂ → ℝ} (h : DyadicConvergent γ α f u) :
    Tendsto (fun k : ℕ => dyadicTest γ α f u k) atTop (𝓝 (dyadicLimit γ α f u)) := by
  obtain ⟨L, hL⟩ := h
  have hlim : dyadicLimit γ α f u = L := hL.limUnder_eq
  rw [hlim]
  exact hL

theorem dyadicLimit_add {γ α : ℝ} {u : ContCircle} (hu : u ∈ DyadicConvSet γ α)
    (f g : CompactlySupportedContinuousMap ℂ ℝ) :
    dyadicLimit γ α (⇑(f + g)) u = dyadicLimit γ α (⇑f) u + dyadicLimit γ α (⇑g) u := by
  have hfc : Continuous (fun z : ℂ => f z) := f.continuous
  have hgc : Continuous (fun z : ℂ => g z) := g.continuous
  have hfs : HasCompactSupport (fun z : ℂ => f z) := f.hasCompactSupport
  have hgs : HasCompactSupport (fun z : ℂ => g z) := g.hasCompactSupport
  have hsum : (fun k : ℕ => dyadicTest γ α (⇑(f + g)) u k) =
      fun k => dyadicTest γ α (⇑f) u k + dyadicTest γ α (⇑g) u k := by
    funext k
    have := isLocallyFiniteMeasure_dyadicApprox γ α u k
    exact integral_add (hfc.integrable_of_hasCompactSupport hfs) (hgc.integrable_of_hasCompactSupport hgs)
  have h1 := tendsto_dyadicLimit (dyadicConvergent_of_mem hu (f + g))
  have h2 := (tendsto_dyadicLimit (dyadicConvergent_of_mem hu f)).add
    (tendsto_dyadicLimit (dyadicConvergent_of_mem hu g))
  rw [hsum] at h1
  exact tendsto_nhds_unique h1 h2

theorem dyadicLimit_const_mul {γ α : ℝ} {u : ContCircle} (hu : u ∈ DyadicConvSet γ α) (c : ℝ)
    (f : CompactlySupportedContinuousMap ℂ ℝ) :
    dyadicLimit γ α (⇑(c • f)) u = c * dyadicLimit γ α (⇑f) u := by
  have hsmul : (fun k : ℕ => dyadicTest γ α (⇑(c • f)) u k) =
      fun k => c * dyadicTest γ α (⇑f) u k := by
    funext k
    unfold dyadicTest
    exact integral_const_mul c _
  have h1 := tendsto_dyadicLimit (dyadicConvergent_of_mem hu (c • f))
  have h2 := (tendsto_dyadicLimit (dyadicConvergent_of_mem hu f)).const_mul c
  rw [hsmul] at h1
  exact tendsto_nhds_unique h1 h2

theorem dyadicLimit_mono {γ α : ℝ} {u : ContCircle} (hu : u ∈ DyadicConvSet γ α)
    (f g : CompactlySupportedContinuousMap ℂ ℝ) (hfg : ∀ z, f z ≤ g z) :
    dyadicLimit γ α (⇑f) u ≤ dyadicLimit γ α (⇑g) u := by
  have hfc : Continuous (fun z : ℂ => f z) := f.continuous
  have hgc : Continuous (fun z : ℂ => g z) := g.continuous
  have hfs : HasCompactSupport (fun z : ℂ => f z) := f.hasCompactSupport
  have hgs : HasCompactSupport (fun z : ℂ => g z) := g.hasCompactSupport
  refine le_of_tendsto_of_tendsto (tendsto_dyadicLimit (dyadicConvergent_of_mem hu f))
    (tendsto_dyadicLimit (dyadicConvergent_of_mem hu g)) (Eventually.of_forall fun k => ?_)
  have := isLocallyFiniteMeasure_dyadicApprox γ α u k
  unfold dyadicTest
  exact integral_mono (hfc.integrable_of_hasCompactSupport hfs) (hgc.integrable_of_hasCompactSupport hgs)
    (fun z => hfg z)

/-- The positive linear functional `f ↦ lim_k ∫ f dν_k` on the convergence set (steps3:501-528). -/
noncomputable def dyadicFunctional (γ α : ℝ) (u : ContCircle) (hu : u ∈ DyadicConvSet γ α) :
    CompactlySupportedContinuousMap ℂ ℝ →ₚ[ℝ] ℝ where
  toFun f := dyadicLimit γ α (⇑f) u
  map_add' f g := dyadicLimit_add hu f g
  map_smul' c f := (dyadicLimit_const_mul hu c f).trans (by simp)
  monotone' f g hfg := dyadicLimit_mono hu f g (fun z => hfg z)

/-- The Riesz–Markov–Kakutani Radon measure of the limit functional (steps3:501-528, "the limit taken there"). -/
noncomputable def dyadicLimitMeasure (γ α : ℝ) (u : ContCircle) (hu : u ∈ DyadicConvSet γ α) : Measure ℂ :=
  RealRMK.rieszMeasure (dyadicFunctional γ α u hu)

theorem integral_dyadicLimitMeasure {γ α : ℝ} {u : ContCircle} (hu : u ∈ DyadicConvSet γ α)
    (f : CompactlySupportedContinuousMap ℂ ℝ) :
    ∫ z, f z ∂(dyadicLimitMeasure γ α u hu) = dyadicLimit γ α (⇑f) u :=
  RealRMK.integral_rieszMeasure (dyadicFunctional γ α u hu) f

/-! ## Inner approximations of open sets and the decoder -/

/-- The inner approximation `min(1, j · dist(z, Kᶜ))` of the indicator of `K`. -/
noncomputable def innerTest (K : Set ℂ) (j : ℕ) (z : ℂ) : ℝ :=
  min 1 ((j : ℝ) * Metric.infDist z Kᶜ)

theorem continuous_innerTest (K : Set ℂ) (j : ℕ) : Continuous (innerTest K j) :=
  continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))

theorem innerTest_nonneg (K : Set ℂ) (j : ℕ) (z : ℂ) : 0 ≤ innerTest K j z :=
  le_min zero_le_one (mul_nonneg (Nat.cast_nonneg j) Metric.infDist_nonneg)

theorem innerTest_le_one (K : Set ℂ) (j : ℕ) (z : ℂ) : innerTest K j z ≤ 1 :=
  min_le_left _ _

theorem innerTest_eq_zero_of_notMem {K : Set ℂ} (j : ℕ) {z : ℂ} (hz : z ∉ K) :
    innerTest K j z = 0 := by
  have h0 : Metric.infDist z Kᶜ = 0 := Metric.infDist_zero_of_mem (by simpa using hz)
  unfold innerTest
  rw [h0, mul_zero, min_eq_right zero_le_one]

theorem innerTest_mono (K : Set ℂ) {j j' : ℕ} (h : j ≤ j') (z : ℂ) : innerTest K j z ≤ innerTest K j' z :=
  min_le_min_left _ (mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) Metric.infDist_nonneg)

theorem hasCompactSupport_innerTest {K : Set ℂ} {ρ : ℝ} (hK : K ⊆ Metric.closedBall 0 ρ) (j : ℕ) :
    HasCompactSupport (innerTest K j) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ρ)
  intro z hz
  exact innerTest_eq_zero_of_notMem j (fun h => hz (hK h))

theorem compl_nonempty_of_subset_closedBall {K : Set ℂ} {ρ : ℝ} (hK : K ⊆ Metric.closedBall 0 ρ) :
    Kᶜ.Nonempty := by
  refine ⟨((|ρ| + 1 : ℝ) : ℂ), fun h => ?_⟩
  have h1 := hK h
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_of_nonneg (by positivity)] at h1
  linarith [le_abs_self ρ]

/-- The inner approximations of an open set `K` as compactly supported tests. -/
noncomputable def innerCC {K : Set ℂ} {ρ : ℝ} (hK : K ⊆ Metric.closedBall 0 ρ) (j : ℕ) :
    CompactlySupportedContinuousMap ℂ ℝ where
  toContinuousMap := ⟨innerTest K j, continuous_innerTest K j⟩
  hasCompactSupport' := hasCompactSupport_innerTest hK j

/-- **Monotone convergence for inner approximations.** For an open bounded set `K` and any measure finite on compacts,
`μ K = sup_j ∫ min(1, j·dist(·, Kᶜ)) dμ` (the inner regularity of the Radon measure on open sets). -/
theorem measure_eq_iSup_innerTest {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] {K : Set ℂ} {ρ : ℝ}
    (hKo : IsOpen K) (hK : K ⊆ Metric.closedBall 0 ρ) :
    μ K = ⨆ j : ℕ, ∫⁻ z, ENNReal.ofReal (innerTest K j z) ∂μ := by
  have hne : Kᶜ.Nonempty := compl_nonempty_of_subset_closedBall hK
  rw [← lintegral_indicator_one hKo.measurableSet]
  have hpt : ∀ z, K.indicator (1 : ℂ → ℝ≥0∞) z = ⨆ j : ℕ, ENNReal.ofReal (innerTest K j z) := by
    intro z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz, Pi.one_apply]
      have hpos : 0 < Metric.infDist z Kᶜ :=
        ((hKo.isClosed_compl).notMem_iff_infDist_pos hne).1 (fun h => h hz)
      obtain ⟨j, hj⟩ := exists_nat_ge (1 / Metric.infDist z Kᶜ)
      have hj1 : 1 ≤ (j : ℝ) * Metric.infDist z Kᶜ := (div_le_iff₀ hpos).1 hj
      apply le_antisymm
      · refine le_iSup_of_le j ?_
        rw [innerTest, min_eq_left hj1, ENNReal.ofReal_one]
      · refine iSup_le fun i => ?_
        exact ENNReal.ofReal_le_one.2 (innerTest_le_one K i z)
    · rw [Set.indicator_of_notMem hz]
      simp only [innerTest_eq_zero_of_notMem _ hz, ENNReal.ofReal_zero, iSup_const]
  simp_rw [hpt]
  rw [lintegral_iSup (fun j => (continuous_innerTest K j).measurable.ennreal_ofReal)]
  intro i j hij z
  exact ENNReal.ofReal_le_ofReal (innerTest_mono K hij z)

/-! ## The measurable dyadic decoder -/

/-- A continuous compactly supported function as a test of `C_c(ℂ, ℝ)`. -/
noncomputable def ccOfCont (f : ℂ → ℝ) (hf : Continuous f) (hcs : HasCompactSupport f) :
    CompactlySupportedContinuousMap ℂ ℝ where
  toContinuousMap := ⟨f, hf⟩
  hasCompactSupport' := hcs

instance isFiniteMeasureOnCompacts_dyadicLimitMeasure (γ α : ℝ) (u : ContCircle)
    (hu : u ∈ DyadicConvSet γ α) : IsFiniteMeasureOnCompacts (dyadicLimitMeasure γ α u hu) := by
  unfold dyadicLimitMeasure
  infer_instance

open scoped Classical in
/-- **The measurable dyadic decoder** (steps3:501-528, the constructor of `𝓜`): on the Borel convergence set
`DyadicConvSet`, the Radon measure of the limit functional (the vague limit of the dyadic approximations); zero off
the convergence set. -/
noncomputable def dyadicDecoder (γ α : ℝ) (u : ContCircle) : Measure ℂ :=
  if hu : u ∈ DyadicConvSet γ α then dyadicLimitMeasure γ α u hu else 0

theorem dyadicDecoder_of_mem {γ α : ℝ} {u : ContCircle} (hu : u ∈ DyadicConvSet γ α) :
    dyadicDecoder γ α u = dyadicLimitMeasure γ α u hu := by
  simp [dyadicDecoder, hu]

theorem dyadicDecoder_of_notMem {γ α : ℝ} {u : ContCircle} (hu : u ∉ DyadicConvSet γ α) :
    dyadicDecoder γ α u = 0 := by
  simp [dyadicDecoder, hu]

theorem dyadicDecoder_ball_ne_top (γ α : ℝ) (u : ContCircle) (n : ℕ) :
    dyadicDecoder γ α u (Metric.ball (0 : ℂ) n) ≠ ⊤ := by
  by_cases hu : u ∈ DyadicConvSet γ α
  · rw [dyadicDecoder_of_mem hu]
    exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  · rw [dyadicDecoder_of_notMem hu]
    simp

/-- The limit functional's measurability: the limit of the test integrals, zero off the convergence set. -/
theorem measurable_indicator_dyadicLimit (γ α : ℝ) (f : CompactlySupportedContinuousMap ℂ ℝ) :
    Measurable ((DyadicConvSet γ α).indicator (fun u => dyadicLimit γ α (⇑f) u)) := by
  have hfc : Continuous (fun z : ℂ => f z) := f.continuous
  have hmeas : ∀ k : ℕ, Measurable ((DyadicConvSet γ α).indicator (fun u => dyadicTest γ α (⇑f) u k)) :=
    fun k => (measurable_dyadicTest γ α hfc k).indicator (measurableSet_dyadicConvSet γ α)
  refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun u => ?_)
  by_cases hu : u ∈ DyadicConvSet γ α
  · simp only [Set.indicator_of_mem hu]
    exact tendsto_dyadicLimit (dyadicConvergent_of_mem hu f)
  · simp only [Set.indicator_of_notMem hu]
    exact tendsto_const_nhds

/-- The limit of the inner test integrals, zero off the convergence set. -/
theorem measurable_indicator_innerLimit (γ α : ℝ) {K : Set ℂ} {ρ : ℝ} (hK : K ⊆ Metric.closedBall 0 ρ)
    (j : ℕ) :
    Measurable ((DyadicConvSet γ α).indicator (fun u => dyadicLimit γ α (innerTest K j) u)) :=
  measurable_indicator_dyadicLimit γ α (innerCC hK j)

/-- **Value of the decoder on open sets** (monotone convergence for the inner approximations): on the convergence set
`dyadicDecoder u K = sup_j ∫ min(1, j·dist(·,Kᶜ)) d(dyadicLimit u)`, and zero off it. -/
theorem dyadicDecoder_open (γ α : ℝ) {K : Set ℂ} {ρ : ℝ} (hKo : IsOpen K) (hK : K ⊆ Metric.closedBall 0 ρ)
    (u : ContCircle) :
    dyadicDecoder γ α u K = ⨆ j : ℕ,
      ENNReal.ofReal ((DyadicConvSet γ α).indicator (fun u => dyadicLimit γ α (innerTest K j) u) u) := by
  by_cases hu : u ∈ DyadicConvSet γ α
  · rw [dyadicDecoder_of_mem hu, measure_eq_iSup_innerTest hKo hK]
    simp only [Set.indicator_of_mem hu]
    refine iSup_congr fun j => ?_
    have hint : Integrable (innerTest K j) (dyadicLimitMeasure γ α u hu) :=
      (continuous_innerTest K j).integrable_of_hasCompactSupport (hasCompactSupport_innerTest hK j)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (innerTest_nonneg K j))]
    exact congrArg ENNReal.ofReal (integral_dyadicLimitMeasure hu (innerCC hK j))
  · rw [dyadicDecoder_of_notMem hu]
    simp [Set.indicator_of_notMem hu]

theorem measurable_dyadicDecoder_of_isOpen (γ α : ℝ) {K : Set ℂ} {ρ : ℝ} (hKo : IsOpen K)
    (hK : K ⊆ Metric.closedBall 0 ρ) :
    Measurable (fun u : ContCircle => dyadicDecoder γ α u K) := by
  have heq : (fun u : ContCircle => dyadicDecoder γ α u K) = fun u =>
      ⨆ j : ℕ, ENNReal.ofReal ((DyadicConvSet γ α).indicator (fun u => dyadicLimit γ α (innerTest K j) u) u) :=
    funext fun u => dyadicDecoder_open γ α hKo hK u
  rw [heq]
  exact Measurable.iSup fun j => ENNReal.measurable_ofReal.comp (measurable_indicator_innerLimit γ α hK j)

/-- **Borel measurability of the decoder on Borel sets** (Dynkin induction over the open sets, the π-system of
steps3:501-528; the countable union/limit steps are the continuity of the measure from below). -/
theorem measurable_dyadicDecoder_apply (γ α : ℝ) (s : Set ℂ) (hs : MeasurableSet s) :
    Measurable (fun u : ContCircle => dyadicDecoder γ α u s) := by
  have hBorel : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom {t : Set ℂ | IsOpen t} :=
    BorelSpace.measurable_eq
  have key : ∀ t : Set ℂ, MeasurableSet t → ∀ n : ℕ,
      Measurable (fun u : ContCircle => dyadicDecoder γ α u (t ∩ Metric.ball (0 : ℂ) n)) := by
    intro t ht
    induction t, ht using MeasurableSpace.induction_on_inter (m := inferInstance) hBorel isPiSystem_isOpen with
    | empty => intro n; simp only [Set.empty_inter, measure_empty]; exact measurable_const
    | basic t ht =>
      intro n
      have hto : IsOpen t := ht
      exact measurable_dyadicDecoder_of_isOpen γ α (hto.inter Metric.isOpen_ball)
        (fun z hz => Metric.ball_subset_closedBall hz.2)
    | compl t htm ih =>
      intro n
      have hset : tᶜ ∩ Metric.ball (0 : ℂ) n = Metric.ball (0 : ℂ) n \ (t ∩ Metric.ball (0 : ℂ) n) :=
        Set.ext fun z => by simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
      have heq : (fun u : ContCircle => dyadicDecoder γ α u (tᶜ ∩ Metric.ball (0 : ℂ) n)) =
          fun u => dyadicDecoder γ α u (Metric.ball (0 : ℂ) n) - dyadicDecoder γ α u (t ∩ Metric.ball (0 : ℂ) n) := by
        funext u
        rw [hset, measure_sdiff Set.inter_subset_right (htm.inter measurableSet_ball).nullMeasurableSet
          (dyadicDecoder_ball_ne_top γ α u n |> fun h => ne_top_of_le_ne_top h (measure_mono Set.inter_subset_right))]
      rw [heq]
      exact (measurable_dyadicDecoder_of_isOpen γ α Metric.isOpen_ball
        (fun z hz => Metric.ball_subset_closedBall hz)).sub (ih n)
    | iUnion f hdisj hfm ih =>
      intro n
      have hset : (⋃ i, f i) ∩ Metric.ball (0 : ℂ) n = ⋃ i, (f i ∩ Metric.ball (0 : ℂ) n) := Set.iUnion_inter _ _
      have heq : (fun u : ContCircle => dyadicDecoder γ α u ((⋃ i, f i) ∩ Metric.ball (0 : ℂ) n)) =
          fun u => ∑' i, dyadicDecoder γ α u (f i ∩ Metric.ball (0 : ℂ) n) := by
        funext u
        rw [hset, measure_iUnion]
        · intro i j hij
          exact (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
        · exact fun i => (hfm i).inter measurableSet_ball
      rw [heq]
      exact Measurable.tsum fun i => ih i n
  have hunion : ∀ u : ContCircle, dyadicDecoder γ α u s =
      ⨆ n : ℕ, dyadicDecoder γ α u (s ∩ Metric.ball (0 : ℂ) n) := by
    intro u
    have hU : (⋃ n : ℕ, s ∩ Metric.ball (0 : ℂ) n) = s := by
      rw [← Set.inter_iUnion, Metric.iUnion_ball_nat, Set.inter_univ]
    have hmono : Monotone (fun n : ℕ => s ∩ Metric.ball (0 : ℂ) n) := fun m n hmn =>
      Set.inter_subset_inter_right s (Metric.ball_subset_ball (Nat.cast_le.2 hmn))
    conv_lhs => rw [← hU]
    rw [hmono.measure_iUnion]
  have heq : (fun u : ContCircle => dyadicDecoder γ α u s) =
      fun u => ⨆ n : ℕ, dyadicDecoder γ α u (s ∩ Metric.ball (0 : ℂ) n) :=
    funext hunion
  rw [heq]
  exact Measurable.iSup fun n => key s hs n

/-- **The measurable dyadic decoder is Borel** (steps3:501-528). -/
theorem measurable_dyadicDecoder (γ α : ℝ) : Measurable (dyadicDecoder γ α) :=
  Measure.measurable_of_measurable_coe _ fun s hs => measurable_dyadicDecoder_apply γ α s hs

/-- On the convergence set the decoder is the vague limit of the dyadic approximations. -/
theorem isLQGLimit_dyadicDecoder {γ α : ℝ} {u : ContCircle} (hu : u ∈ DyadicConvSet γ α) :
    IsLQGLimit γ (fieldCircleAverage α (procExt u.1)) (dyadicDecoder γ α u) := by
  rw [dyadicDecoder_of_mem hu]
  refine ⟨inferInstance, fun f hf hcs => ?_⟩
  have h := tendsto_dyadicLimit (dyadicConvergent_of_mem hu (ccOfCont f hf hcs))
  rw [show (∫ z, f z ∂(dyadicLimitMeasure γ α u hu)) = dyadicLimit γ α f u from
    integral_dyadicLimitMeasure hu (ccOfCont f hf hcs)]
  exact h

/-- **Measurable dyadic decoder, constructed** (steps3:501-528): for all `γ, α`, a Borel map `dec` on the continuous
positive-radius processes whose value is the dyadic insertion limit at every continuous process that has one. This is
the constructor of the premise `MeasurableDyadicDecoder`, here with domain `ContCircle`. -/
theorem exists_measurableDyadicDecoder_contCircle (γ α : ℝ) :
    ∃ dec : ContCircle → Measure ℂ, Measurable dec ∧
      ∀ u : ContCircle, (∃ m : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (procExt u.1)) m) →
        IsLQGLimit γ (fieldCircleAverage α (procExt u.1)) (dec u) := by
  refine ⟨dyadicDecoder γ α, measurable_dyadicDecoder γ α, fun u hm => ?_⟩
  obtain ⟨m, hm⟩ := hm
  have hu : u ∈ DyadicConvSet γ α := by
    refine ⟨fun f _ => ?_, dyadicMassBounded_of_tendsto (fun f hf hcs => hm.tendsto_integral f hf hcs)⟩
    have hfc : Continuous (fun z : ℂ => f z) := f.continuous
    have hfs : HasCompactSupport (fun z : ℂ => f z) := f.hasCompactSupport
    exact ⟨∫ z, f z ∂m, hm.tendsto_integral (fun z => f z) hfc hfs⟩
  exact isLQGLimit_dyadicDecoder hu

/-! ## Identification of the supplied measure with the decoded measure (steps3:501-528) -/

/-- The continuous modification of an a.s. continuous measurable process: a measurable `ContCircle`-valued map equal
to it almost surely (steps3:501-528, "give it any fixed continuous value outside that subset"). -/
theorem exists_contModification {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (F : Ω → Set.Ioi (0 : ℝ) × ℂ → ℝ) (hF : Measurable F) (hcont : ∀ᵐ ω ∂P, Continuous (F ω)) :
    ∃ G : Ω → ContCircle, Measurable G ∧ ∀ᵐ ω ∂P, (G ω).1 = F ω := by
  obtain ⟨t, hsub, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  have hS : MeasurableSet tᶜ := htm.compl
  have hcontS : ∀ ω, ω ∈ tᶜ → Continuous (F ω) := fun ω hω =>
    by_contra fun hnc => hω (hsub hnc)
  let Fc : Ω → Set.Ioi (0 : ℝ) × ℂ → ℝ := tᶜ.indicator F
  have hFc_cont : ∀ ω, Continuous (Fc ω) := by
    intro ω
    by_cases hω : ω ∈ tᶜ
    · simp only [Fc, Set.indicator_of_mem hω]
      exact hcontS ω hω
    · simp only [Fc, Set.indicator_of_notMem hω]
      exact continuous_const
  have hFc_meas : Measurable Fc := hF.indicator hS
  refine ⟨fun ω => ⟨Fc ω, hFc_cont ω⟩, hFc_meas.subtype_mk, ?_⟩
  filter_upwards [compl_mem_ae_iff.2 ht0] with ω hω
  show Fc ω = F ω
  simp only [Fc, Set.indicator_of_mem hω]

open scoped Classical in
/-- The decoder on the full function space: the constructed decoder on continuous processes and `0` otherwise. It is
used only through its values on continuous processes; no measurability on the full function space is claimed. -/
noncomputable def dyadicDecoderFull (γ α : ℝ) (v : Set.Ioi (0 : ℝ) × ℂ → ℝ) : Measure ℂ :=
  if h : Continuous v then dyadicDecoder γ α ⟨v, h⟩ else 0

theorem dyadicDecoderFull_of_continuous {γ α : ℝ} {v : Set.Ioi (0 : ℝ) × ℂ → ℝ} (h : Continuous v) :
    dyadicDecoderFull γ α v = dyadicDecoder γ α ⟨v, h⟩ := by
  simp [dyadicDecoderFull, h]

theorem mem_dyadicConvSet_of_isLQGLimit {γ α : ℝ} {u : ContCircle} {m : Measure ℂ}
    (hm : IsLQGLimit γ (fieldCircleAverage α (procExt u.1)) m) : u ∈ DyadicConvSet γ α := by
  refine ⟨fun f _ => ?_, dyadicMassBounded_of_tendsto (fun f hf hcs => hm.tendsto_integral f hf hcs)⟩
  have hfc : Continuous (fun z : ℂ => f z) := f.continuous
  have hfs : HasCompactSupport (fun z : ℂ => f z) := f.hasCompactSupport
  exact ⟨∫ z, f z ∂m, hm.tendsto_integral (fun z => f z) hfc hfs⟩

theorem dyadicDecoderFull_spec (γ α : ℝ) (v : Set.Ioi (0 : ℝ) × ℂ → ℝ) (h : Continuous v)
    (hm : ∃ m : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (procExt v)) m) :
    IsLQGLimit γ (fieldCircleAverage α (procExt v)) (dyadicDecoderFull γ α v) := by
  rw [dyadicDecoderFull_of_continuous h]
  obtain ⟨m, hm⟩ := hm
  exact isLQGLimit_dyadicDecoder (mem_dyadicConvSet_of_isLQGLimit (u := ⟨v, h⟩) hm)

/-- **Identification (steps3:501-528).** For a whole-plane GFF whose insertion-`α` LQG measure is the supplied `μ`
(not assumed measurable), there is a measurable continuous modification `G` of the circle array with `μ = dec(G)` almost
surely, where `dec` is the constructed decoder. The supplied `μ` is never used as a measurable map. -/
theorem insertion_identification_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∃ G : Ω → ContCircle, Measurable G ∧ (∀ᵐ ω ∂P, (G ω).1 = circleProc (hcirc ω)) ∧
      ∀ᵐ ω ∂P, μ ω = dyadicDecoder γ α (G ω) := by
  obtain ⟨G, hG, hGω⟩ := exists_contModification (fun ω => circleProc (hcirc ω))
    (measurable_circleProc hGFF) (ae_continuous_circleProc hGFF)
  refine ⟨G, hG, hGω, ?_⟩
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  filter_upwards [hμ', hGω] with ω h1 h2
  have hprocess : IsLQGLimit γ (fieldCircleAverage α (procExt (G ω).1)) (μ ω) := by
    rw [h2]
    exact isLQGLimit_circleProc_iff.2 h1
  exact isLQGLimit_unique hprocess (isLQGLimit_dyadicDecoder (mem_dyadicConvSet_of_isLQGLimit hprocess))

/-- Equality in law of two continuous modifications, from equality in law of the underlying processes. -/
theorem map_contModification_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F F' : Ω → Set.Ioi (0 : ℝ) × ℂ → ℝ} {G G' : Ω → ContCircle}
    (hF : Measurable F) (hF' : Measurable F') (hG : Measurable G) (hG' : Measurable G')
    (hGF : ∀ᵐ ω ∂P, (G ω).1 = F ω) (hG'F' : ∀ᵐ ω ∂P, (G' ω).1 = F' ω)
    (hFF' : P.map F = P.map F') : P.map G = P.map G' := by
  refine Measure.ext fun A hA => ?_
  obtain ⟨B, hB, hBA⟩ := MeasurableSpace.measurableSet_comap.1 hA
  rw [Measure.map_apply hG hA, Measure.map_apply hG' hA, ← hBA]
  have e1 : P (G ⁻¹' (Subtype.val ⁻¹' B)) = P (F ⁻¹' B) :=
    measure_congr (by filter_upwards [hGF] with ω hω; simp [hω])
  have e2 : P (G' ⁻¹' (Subtype.val ⁻¹' B)) = P (F' ⁻¹' B) :=
    measure_congr (by filter_upwards [hG'F'] with ω hω; simp [hω])
  rw [e1, e2, ← Measure.map_apply hF hB, ← Measure.map_apply hF' hB, hFF']

/-- **No insertion atom at the origin, unconditional** (steps3:538-585, Lemma `lem:insertion-no-atom`). Under `0 < γ`,
`α < Q`, a whole-plane GFF `(hC, hcirc)` whose insertion-`α` LQG measure is `μ`, `μ{0} = 0` almost surely. This is
`insertion_no_atom_zero_ae` with the measurable-decoder premise replaced by the constructed decoder. -/
theorem insertion_no_atom_zero_ae_unconditional {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, μ ω {0} = 0 := by
  have hdecMeas : Measurable (dyadicDecoder γ α) := measurable_dyadicDecoder γ α
  have heval : Measurable fun ν : Measure ℂ => ν {0} := Measure.measurable_coe (measurableSet_singleton 0)
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  obtain ⟨Gc, hGc, hGc_ae, hid⟩ := insertion_identification_ae hGFF hμ
  have hGn_exists : ∀ n : ℕ, ∃ G : Ω → ContCircle, Measurable G ∧
      ∀ᵐ ω ∂P, (G ω).1 = circleProc (Field.affHcirc (dyadicScale n) 0 hcirc ω) := fun n =>
    exists_contModification _
      (measurable_circleProc (Field.isWholePlaneGFF_affine hGFF (dyadicScale_pos n) 0))
      (ae_continuous_circleProc (Field.isWholePlaneGFF_affine hGFF (dyadicScale_pos n) 0))
  choose Gn hGn hGn_ae using hGn_exists
  have hlawG : ∀ n : ℕ, P.map (Gn n) = P.map Gc := fun n =>
    map_contModification_eq
      (measurable_circleProc (Field.isWholePlaneGFF_affine hGFF (dyadicScale_pos n) 0))
      (measurable_circleProc hGFF) (hGn n) hGc (hGn_ae n) hGc_ae
      (circleProc_affine_law hGFF (dyadicScale_pos n))
  have hdec_map : ∀ X Y : Ω → ContCircle, Measurable X → Measurable Y → P.map X = P.map Y →
      P.map (fun ω => dyadicDecoder γ α (X ω) {0}) = P.map (fun ω => dyadicDecoder γ α (Y ω) {0}) := by
    intro X Y hX hY hXY
    calc P.map (fun ω => dyadicDecoder γ α (X ω) {0})
        = (P.map (dyadicDecoder γ α ∘ X)).map (fun ν : Measure ℂ => ν {0}) :=
          (Measure.map_map heval (hdecMeas.comp hX)).symm
      _ = ((P.map X).map (dyadicDecoder γ α)).map (fun ν : Measure ℂ => ν {0}) := by
          rw [Measure.map_map hdecMeas hX]
      _ = ((P.map Y).map (dyadicDecoder γ α)).map (fun ν : Measure ℂ => ν {0}) := by rw [hXY]
      _ = (P.map (dyadicDecoder γ α ∘ Y)).map (fun ν : Measure ℂ => ν {0}) := by
          rw [Measure.map_map hdecMeas hY]
      _ = P.map (fun ω => dyadicDecoder γ α (Y ω) {0}) := Measure.map_map heval (hdecMeas.comp hY)
  let a : Ω → ℝ≥0∞ := fun ω => dyadicDecoder γ α (Gc ω) {0}
  let b : ℕ → Ω → ℝ≥0∞ := fun n ω => dyadicDecoder γ α (Gn n ω) {0}
  let c : ℕ → Ω → ℝ := fun n ω => Field.coordConst γ (dyadicScale n) (fieldCircleAverage α (hcirc ω)) 0
  have ha : Measurable a := heval.comp (hdecMeas.comp hGc)
  have hb : ∀ n, Measurable (b n) := fun n => heval.comp (hdecMeas.comp (hGn n))
  have hlaw : ∀ (n : ℕ) (L : ℝ≥0∞), P (b n ⁻¹' Set.Ioi L) = P (a ⁻¹' Set.Ioi L) := by
    intro n L
    have hmap : P.map (b n) = P.map a := hdec_map _ _ (hGn n) hGc (hlawG n)
    rw [← Measure.map_apply (hb n) measurableSet_Ioi, ← Measure.map_apply ha measurableSet_Ioi, hmap]
  have hscale : ∀ᵐ ω ∂P, ∀ n, b n ω = ENNReal.ofReal (c n ω)⁻¹ * a ω := by
    refine ae_all_iff.2 fun n => ?_
    have hdecAff := dec_affine_ae hGFF hμ (dyadicDecoderFull γ α)
      (fun v hv hm => dyadicDecoderFull_spec γ α v hv hm) n
    filter_upwards [hdecAff, hid, hGn_ae n, hGc_ae] with ω h1 h2 h3 h4
    have hb' : dyadicDecoder γ α (Gn n ω) =
        dyadicDecoderFull γ α (circleProc (Field.affHcirc (dyadicScale n) 0 hcirc ω)) := by
      rw [← h3, dyadicDecoderFull_of_continuous (Gn n ω).2]
    show dyadicDecoder γ α (Gn n ω) {0} = ENNReal.ofReal (c n ω)⁻¹ * dyadicDecoder γ α (Gc ω) {0}
    rw [hb', h1, smul_map_div_singleton _ _ (dyadicScale_pos n).ne', h2]
  have hfin : ∀ᵐ ω ∂P, a ω ≠ ⊤ := by
    filter_upwards [hμ', hid] with ω h1 h2
    have := h1.isLocallyFiniteMeasure
    show dyadicDecoder γ α (Gc ω) {0} ≠ ⊤
    rw [← h2]
    exact (isCompact_singleton.measure_lt_top).ne
  have hc0 : ∀ᵐ ω ∂P, Tendsto (fun n => c n ω) atTop (𝓝 0) :=
    ae_tendsto_coordConst_zero hGFF hγ hαQ
  have hcpos : ∀ (n : ℕ) (ω : Ω), 0 < c n ω := fun n ω =>
    Field.coordConst_pos γ (dyadicScale_pos n) (fieldCircleAverage α (hcirc ω)) 0
  have hmain := atom_vanishing_of_scaling a b c ha hlaw hfin hscale hc0 hcpos
  filter_upwards [hmain, hid] with ω h1 h2
  rw [h2]
  exact h1

/-! ## The Borel carrier: approximations and decoder values are Radon measures -/

/-- The approximating map `u ↦ ν_k(u)` is Borel into the measures on `ℂ` (steps3:501-528, "the map sending `u` to the
dyadic density is Borel into the positive Radon measures"). -/
theorem measurable_dyadicApprox (γ α : ℝ) (k : ℕ) :
    Measurable (fun u : ContCircle => dyadicApprox γ α u k) :=
  Measure.measurable_of_measurable_coe _ fun _ hB => measurable_dyadicApprox_ball γ α k hB

/-- The decoder takes values in the locally finite (Radon) measures, for every continuous process. -/
theorem isLocallyFiniteMeasure_dyadicDecoder (γ α : ℝ) (u : ContCircle) :
    IsLocallyFiniteMeasure (dyadicDecoder γ α u) := by
  by_cases hu : u ∈ DyadicConvSet γ α
  · rw [dyadicDecoder_of_mem hu]
    infer_instance
  · rw [dyadicDecoder_of_notMem hu]
    infer_instance

end MatedCRT
