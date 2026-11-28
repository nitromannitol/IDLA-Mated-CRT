import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Tail
import MatedCRT.FirstPass.Derived.ZeroConeLemmaA1Root
import MatedCRT.FirstPass.Derived.ConeAnnulusAreaLawEquivalenceLocalMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaMeasurable

/-!
# Exterior versions of the area and of the local observation

For the proof of Lemma A.1 of Gwynne–Miller–Sheffield (arXiv:1705.11161, Appendix A; written answer 58, section 3,
third paragraph): at distance more than `k + 2` from the origin, the area measure on `{|w| > k + 1}` and the local
observation at a point `z` are measurable functions of the restriction of the field to `{|w| > k}`.

## Main statements

* `exists_extArea_decoder`: the area measure of a field of the good set, restricted to `{|w| > k + 1}`, is a measurable
  function of the restriction of the field to `{|w| > k}`.
* `exists_rootObs_extVersion`: the local observation `J(h, z)` at a point `z` with mass radius `r_{b₀}(z)` below
  `|z| - (k + 2)` is a jointly measurable function of the restriction of the field to `{|w| > k}` and of `z`.

The decoder reads the dyadic circle averages at scales below `1` on `{|w| > k + 1}` from the restriction (through the
jointly measurable dyadic version of the local circle process), cuts them off by a partition of unity of
`{|w| > k + 1}` into continuous functions supported in balls, and decodes the vague limits of the cut-off
approximations by the measurable decoder `vagueLimitOrZero` of Lattice-Probability.

For the local observation, the restriction `T` to `{|w| > k}` is extended to a whole-plane distribution by a smooth
cut-off (`extExtend`, a measurable function of `T`); the change of coordinates `lqgSimilarityAction` of the extension
restricted to the disc `B_a(0)` is then a jointly measurable function of `(C, z, T)`, and it agrees with the one of
the field itself as long as `B_{aC}(z)` lies in `{|w| > k + 2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRT

open MatedCRTHarmonic MatedCRTHarmonic.MatedCRT

/-! ### The partition of unity of the exterior -/

/-- The cut-off `min 1 (max 0 (n + 1 - |z|))`, equal to `1` on `|z| ≤ n` and to `0` on `|z| ≥ n + 1`. -/
def extScale (n : ℕ) (z : ℂ) : ℝ := min 1 (max 0 ((n : ℝ) + 1 - ‖z‖))

theorem continuous_extScale (n : ℕ) : Continuous (extScale n) := by
  unfold extScale
  fun_prop

theorem extScale_nonneg (n : ℕ) (z : ℂ) : 0 ≤ extScale n z :=
  le_min zero_le_one (le_max_left _ _)

theorem extScale_le_one (n : ℕ) (z : ℂ) : extScale n z ≤ 1 :=
  min_le_left _ _

theorem extScale_mono (z : ℂ) : Monotone fun n : ℕ => extScale n z := by
  refine monotone_nat_of_le_succ fun n => ?_
  unfold extScale
  refine min_le_min_left _ (max_le_max_left _ ?_)
  push_cast
  linarith

theorem extScale_of_le_norm {n : ℕ} {z : ℂ} (hz : (n : ℝ) + 1 ≤ ‖z‖) : extScale n z = 0 := by
  unfold extScale
  rw [max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

theorem extScale_of_norm_le {n : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (n : ℝ)) : extScale n z = 1 := by
  unfold extScale
  rw [max_eq_right (by linarith)]
  exact min_eq_left (by linarith)

/-- The continuous exhaustion `c_n` of the open exterior `{|z| > k + 1}` by functions supported in `{|z| ≤ n + 1}`. -/
def extCut (k n : ℕ) (z : ℂ) : ℝ :=
  annulusCutoff ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ) n z * extScale n z

/-- The partition of unity `ψₙ = c_{n+1} - c_n` of `{|z| > k + 1}`. -/
def extPOU (k n : ℕ) (z : ℂ) : ℝ := extCut k (n + 1) z - extCut k n z

theorem continuous_extCut (k n : ℕ) : Continuous (extCut k n) :=
  (continuous_annulusCutoff _ n).mul (continuous_extScale n)

theorem extCut_nonneg (k n : ℕ) (z : ℂ) : 0 ≤ extCut k n z :=
  mul_nonneg (annulusCutoff_nonneg _ n z) (extScale_nonneg n z)

theorem extCut_le_one (k n : ℕ) (z : ℂ) : extCut k n z ≤ 1 :=
  (mul_le_mul (annulusCutoff_le_one _ n z) (extScale_le_one n z) (extScale_nonneg n z)
    zero_le_one).trans_eq (one_mul 1)

theorem extCut_mono (k : ℕ) (z : ℂ) : Monotone fun n : ℕ => extCut k n z := by
  refine monotone_nat_of_le_succ fun n => ?_
  exact mul_le_mul (annulusCutoff_mono _ z (Nat.le_succ n)) (extScale_mono z (Nat.le_succ n))
    (extScale_nonneg n z) (annulusCutoff_nonneg _ _ z)

theorem extCut_zero (k : ℕ) (z : ℂ) : extCut k 0 z = 0 := by
  simp [extCut, annulusCutoff_zero]

theorem extCut_of_notMem {k : ℕ} {z : ℂ}
    (hz : z ∉ ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ)) (n : ℕ) :
    extCut k n z = 0 := by
  simp [extCut, annulusCutoff_of_notMem hz]

theorem extPOU_nonneg (k n : ℕ) (z : ℂ) : 0 ≤ extPOU k n z :=
  sub_nonneg.2 (extCut_mono k z (Nat.le_succ n))

theorem extPOU_le_one (k n : ℕ) (z : ℂ) : extPOU k n z ≤ 1 := by
  unfold extPOU
  linarith [extCut_le_one k (n + 1) z, extCut_nonneg k n z]

theorem continuous_extPOU (k n : ℕ) : Continuous (extPOU k n) :=
  (continuous_extCut k (n + 1)).sub (continuous_extCut k n)

theorem extPOU_of_notMem {k : ℕ} {z : ℂ}
    (hz : z ∉ ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ)) (n : ℕ) :
    extPOU k n z = 0 := by
  simp [extPOU, extCut_of_notMem hz]

theorem extPOU_of_far {k n : ℕ} {z : ℂ} (hz : (n : ℝ) + 2 ≤ ‖z‖) : extPOU k n z = 0 := by
  have h1 : extScale (n + 1) z = 0 := extScale_of_le_norm (by push_cast; linarith)
  have h2 : extScale n z = 0 := extScale_of_le_norm (by linarith)
  simp [extPOU, extCut, h1, h2]

theorem tsum_ofReal_extPOU (k : ℕ) (z : ℂ) :
    ∑' n, ENNReal.ofReal (extPOU k n z) =
      ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ).indicator 1 z := by
  set W : Set ℂ := ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ) with hW
  have hWo : IsOpen W := (extOpen ((k : ℝ) + 1)).isOpen
  by_cases hz : z ∈ W
  · rw [Set.indicator_of_mem hz, Pi.one_apply]
    have hne : (Wᶜ).Nonempty := ⟨0, fun h => by
      have h' : (k : ℝ) + 1 < ‖(0 : ℂ)‖ := h
      rw [norm_zero] at h'
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]⟩
    have hd : 0 < infDist z Wᶜ :=
      ((isClosed_compl_iff.2 hWo).notMem_iff_infDist_pos hne).1 (by simpa using hz)
    obtain ⟨N, hN⟩ := exists_nat_ge (max (2 / infDist z Wᶜ) ‖z‖)
    rw [ENNReal.tsum_eq_iSup_nat]
    have hsum : ∀ m, ∑ n ∈ Finset.range m, ENNReal.ofReal (extPOU k n z) =
        ENNReal.ofReal (extCut k m z) := by
      intro m
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => extPOU_nonneg k n z)]
      congr 1
      simp only [extPOU]
      rw [Finset.sum_range_sub (fun n => extCut k n z), extCut_zero, sub_zero]
    simp_rw [hsum]
    refine le_antisymm (iSup_le fun m => ENNReal.ofReal_le_one.2 (extCut_le_one k m z)) ?_
    refine le_iSup_of_le N ?_
    have h1 : extCut k N z = 1 := by
      have h2 : 2 ≤ (N : ℝ) * infDist z Wᶜ := by
        have := (div_le_iff₀ hd).1 ((le_max_left _ _).trans hN)
        linarith
      have h3 : annulusCutoff W N z = 1 := by
        simp only [annulusCutoff]
        rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      rw [extCut, h3, extScale_of_norm_le ((le_max_right _ _).trans hN), one_mul]
    rw [h1, ENNReal.ofReal_one]
  · rw [Set.indicator_of_notMem hz]
    simp [extPOU_of_notMem hz]

/-! ### The decoded area approximations -/

/-- The dyadic version of the local circle process of a restriction to `{|w| > k}`, jointly measurable in the
restriction and the centre. -/
def extLocalCircle (k : ℕ) (T : LQGMetric.DistOn (extOpen (k : ℝ))) (ρ : ℝ) (z : ℂ) : ℝ :=
  LQGMetric.GMCIdent.dyVer
    (fun w S => GMS4c.localCircleProcess (extOpen (k : ℝ)) S ρ w) z T

theorem measurable_extLocalCircle (k : ℕ) (ρ : ℝ) :
    Measurable fun p : LQGMetric.DistOn (extOpen (k : ℝ)) × ℂ => extLocalCircle k p.1 ρ p.2 := by
  have hcoord : ∀ w, Measurable fun S : LQGMetric.DistOn (extOpen (k : ℝ)) =>
      GMS4c.localCircleProcess (extOpen (k : ℝ)) S ρ w := fun w =>
    (measurable_pi_apply w).comp
      ((measurable_pi_apply ρ).comp (GMS4c.measurable_localCircleProcess (extOpen (k : ℝ))))
  change Measurable ((fun p : ℂ × LQGMetric.DistOn (extOpen (k : ℝ)) =>
    LQGMetric.GMCIdent.dyVer
      (fun w S => GMS4c.localCircleProcess (extOpen (k : ℝ)) S ρ w) p.1 p.2) ∘ Prod.swap)
  exact (LQGMetric.GMCIdent.measurable_dyVer (m := inferInstance) hcoord).comp measurable_swap

/-- The dyadic version of the circle average of a restriction is the circle average of the field, at points of
`{|z| > k + 1}` and radii below `1`, for a field with continuous circle averages. -/
theorem extLocalCircle_restrictTo {k : ℕ} {h : LQGMetric.DistC} (hh : ConeAreaCovariance.ScaleRegular h) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {z : ℂ}
    (hz : z ∈ ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ)) :
    extLocalCircle k (LQGMetric.restrictTo (extOpen (k : ℝ)) h) ρ z = LQGMetric.circleAvg h ρ z := by
  have hz' : (k : ℝ) + 1 < ‖z‖ := hz
  have hopen : IsOpen {w : ℂ | (k : ℝ) + ρ < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hcongr : ∀ w ∈ {w : ℂ | (k : ℝ) + ρ < ‖w‖},
      GMS4c.localCircleProcess (extOpen (k : ℝ)) (LQGMetric.restrictTo (extOpen (k : ℝ)) h) ρ w =
        LQGMetric.circleAvg h ρ w := by
    intro w hw
    have hball : closedBall w ρ ⊆ ((extOpen (k : ℝ) : TopologicalSpace.Opens ℂ) : Set ℂ) := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm] at hx
      have h1 := norm_sub_norm_le w x
      rw [norm_sub_rev] at h1
      change (k : ℝ) < ‖x‖
      have hw' : (k : ℝ) + ρ < ‖w‖ := hw
      linarith
    have := congrFun (congrFun (GMS4c.localCircleProcess_restrictTo (extOpen (k : ℝ)) h) ρ) w
    simpa [restrictCircles, hρ0, hball] using this
  have hcont : ContinuousAt (fun w => GMS4c.localCircleProcess (extOpen (k : ℝ))
      (LQGMetric.restrictTo (extOpen (k : ℝ)) h) ρ w) z := by
    have hc : ContinuousAt (fun w => LQGMetric.circleAvg h ρ w) z :=
      ((ConeAreaCovariance.continuousOn_circleAvg_of_scaleRegular hh).comp_continuous
        (f := fun w : ℂ => (ρ, w)) (continuous_const.prodMk continuous_id)
        (fun w => ⟨hρ0, mem_univ _⟩)).continuousAt
    refine hc.congr ?_
    filter_upwards [hopen.mem_nhds (show z ∈ {w : ℂ | (k : ℝ) + ρ < ‖w‖} by
      change (k : ℝ) + ρ < ‖z‖
      linarith)] with w hw
    exact (hcongr w hw).symm
  have ht : Tendsto (fun j : ℕ => GMS4c.localCircleProcess (extOpen (k : ℝ))
      (LQGMetric.restrictTo (extOpen (k : ℝ)) h) ρ (QuantumZipper.dyadicRoundC j z)) atTop
      (𝓝 (GMS4c.localCircleProcess (extOpen (k : ℝ))
        (LQGMetric.restrictTo (extOpen (k : ℝ)) h) ρ z)) :=
    hcont.tendsto.comp (QuantumZipper.RegClosure.tendsto_dyadicRoundC z)
  unfold extLocalCircle LQGMetric.GMCIdent.dyVer
  rw [ht.limUnder_eq]
  exact hcongr z (by
    change (k : ℝ) + ρ < ‖z‖
    linarith)

/-- The density of the `n`-th cut-off decoded area approximation at the dyadic scale `2^{-j}`. -/
def extDensity (γ : ℝ) (k n j : ℕ) (T : LQGMetric.DistOn (extOpen (k : ℝ))) (z : ℂ) : ℝ :=
  extPOU k n z *
    (MatedCRTHarmonic.CellScaling.dyadicScale j ^ (γ ^ 2 / 2) *
      Real.exp (γ * extLocalCircle k T (MatedCRTHarmonic.CellScaling.dyadicScale j) z))

theorem extDensity_nonneg (γ : ℝ) (k n j : ℕ) (T : LQGMetric.DistOn (extOpen (k : ℝ))) (z : ℂ) :
    0 ≤ extDensity γ k n j T z :=
  mul_nonneg (extPOU_nonneg k n z) (mul_nonneg (Real.rpow_nonneg (by
    unfold MatedCRTHarmonic.CellScaling.dyadicScale; positivity) _) (Real.exp_pos _).le)

theorem measurable_extDensity (γ : ℝ) (k n j : ℕ) :
    Measurable fun q : LQGMetric.DistOn (extOpen (k : ℝ)) × ℂ => extDensity γ k n j q.1 q.2 :=
  ((continuous_extPOU k n).measurable.comp measurable_snd).mul
    (measurable_const.mul (Real.measurable_exp.comp
      ((measurable_extLocalCircle k (MatedCRTHarmonic.CellScaling.dyadicScale j)).const_mul γ)))

/-- The `n`-th cut-off decoded area approximation at the dyadic scale `2^{-j}`. -/
def extApprox (γ : ℝ) (k n j : ℕ) (T : LQGMetric.DistOn (extOpen (k : ℝ))) : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (extDensity γ k n j T z)

open Classical in
/-- `extApprox` when it has finite total mass, and zero otherwise. -/
def extApproxFin (γ : ℝ) (k n j : ℕ) (T : LQGMetric.DistOn (extOpen (k : ℝ))) : Measure ℂ :=
  if extApprox γ k n j T univ < ⊤ then extApprox γ k n j T else 0

/-- The decoder: the sum over `n` of the decoded vague limits of the cut-off approximations. -/
def extAreaDecode (γ : ℝ) (k : ℕ) (T : LQGMetric.DistOn (extOpen (k : ℝ))) : Measure ℂ :=
  Measure.sum fun n => LatticeProb.VagueLimit.vagueLimitOrZero fun j => extApproxFin γ k n j T

instance isFiniteMeasureOnCompacts_extApproxFin (γ : ℝ) (k n j : ℕ)
    (T : LQGMetric.DistOn (extOpen (k : ℝ))) : IsFiniteMeasureOnCompacts (extApproxFin γ k n j T) := by
  unfold extApproxFin
  split_ifs with h
  · have : IsFiniteMeasure (extApprox γ k n j T) := ⟨h⟩
    infer_instance
  · infer_instance

theorem measurable_mass_extApprox (γ : ℝ) (k n j : ℕ) :
    Measurable fun T : LQGMetric.DistOn (extOpen (k : ℝ)) => extApprox γ k n j T univ := by
  simp_rw [extApprox, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact Measurable.lintegral_prod_right'
    (f := fun q : LQGMetric.DistOn (extOpen (k : ℝ)) × ℂ => ENNReal.ofReal (extDensity γ k n j q.1 q.2))
    (ENNReal.measurable_ofReal.comp (measurable_extDensity γ k n j))

theorem measurable_integral_extApproxFin (γ : ℝ) (k n j : ℕ) {f : ℂ → ℝ} (hf : Continuous f) :
    Measurable fun T : LQGMetric.DistOn (extOpen (k : ℝ)) => ∫ z, f z ∂(extApproxFin γ k n j T) := by
  classical
  have e : (fun T : LQGMetric.DistOn (extOpen (k : ℝ)) => ∫ z, f z ∂(extApproxFin γ k n j T)) =
      fun T => if extApprox γ k n j T univ < ⊤ then ∫ z, f z ∂(extApprox γ k n j T) else 0 := by
    funext T
    unfold extApproxFin
    split_ifs <;> simp
  rw [e]
  refine Measurable.ite (measurableSet_lt (measurable_mass_extApprox γ k n j) measurable_const) ?_
    measurable_const
  exact LatticeProb.LQG.measurable_integral_withDensity_ofReal_uncurry_param
    (d := fun T z => extDensity γ k n j T z) (measurable_extDensity γ k n j)
    (extDensity_nonneg γ k n j) (f := fun _ z => f z) (hf.measurable.comp measurable_snd)

/-- **Measurability of the decoder.** -/
theorem measurable_extAreaDecode (γ : ℝ) (k : ℕ) : Measurable (extAreaDecode γ k) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [extAreaDecode, Measure.sum_apply _ hs]
  refine Measurable.tsum fun n => ?_
  have hm := LatticeProb.VagueLimit.measurable_vagueLimitOrZero
    (m := fun j T => extApproxFin γ k n j T) (fun j T => inferInstance)
    (fun j f hf _ => measurable_integral_extApproxFin γ k n j hf)
  exact (Measure.measurable_coe hs).comp hm

/-! ### Identification of the decoded measure -/

/-- For a field with continuous circle averages, the area approximations are finite on compact sets. -/
theorem lqgAreaApprox_closedBall_lt_top {γ : ℝ} {h : LQGMetric.DistC}
    (hh : ConeAreaCovariance.ScaleRegular h) (j : ℕ) (R : ℝ) :
    MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h j (closedBall (0 : ℂ) R) < ⊤ := by
  have hpos : 0 < MatedCRTHarmonic.CellScaling.dyadicScale j := by
    unfold MatedCRTHarmonic.CellScaling.dyadicScale
    positivity
  have hc : Continuous fun z : ℂ => MatedCRTHarmonic.CellScaling.dyadicScale j ^ (γ ^ 2 / 2) *
      Real.exp (γ * LQGMetric.circleAvg h (MatedCRTHarmonic.CellScaling.dyadicScale j) z) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((ConeAreaCovariance.continuousOn_circleAvg_of_scaleRegular hh).comp_continuous
        (f := fun w : ℂ => (MatedCRTHarmonic.CellScaling.dyadicScale j, w))
        (continuous_const.prodMk continuous_id) (fun w => ⟨hpos, mem_univ _⟩))))
  have : IsLocallyFiniteMeasure (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h j) := by
    unfold MatedCRTHarmonic.CellScaling.lqgAreaApprox
    exact IsLocallyFiniteMeasure.withDensity_ofReal hc
  exact measure_closedBall_lt_top

theorem withDensity_extApprox {γ : ℝ} (k n j : ℕ) {h : LQGMetric.DistC}
    (hcirc : ∀ z ∈ ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ),
      extLocalCircle k (LQGMetric.restrictTo (extOpen (k : ℝ)) h) (MatedCRTHarmonic.CellScaling.dyadicScale j) z =
        LQGMetric.circleAvg h (MatedCRTHarmonic.CellScaling.dyadicScale j) z) :
    extApprox γ k n j (LQGMetric.restrictTo (extOpen (k : ℝ)) h) =
      (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h j).withDensity
        fun z => ENNReal.ofReal (extPOU k n z) := by
  have hm : Measurable fun z : ℂ => ENNReal.ofReal (MatedCRTHarmonic.CellScaling.dyadicScale j ^ (γ ^ 2 / 2) *
      Real.exp (γ * LQGMetric.circleAvg h (MatedCRTHarmonic.CellScaling.dyadicScale j) z)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      ((LQGMetric.measurable_circleAvg.comp (f := fun z : ℂ =>
        (h, MatedCRTHarmonic.CellScaling.dyadicScale j, z))
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).const_mul γ)))
  have hψ : Measurable fun z : ℂ => ENNReal.ofReal (extPOU k n z) :=
    ENNReal.measurable_ofReal.comp (continuous_extPOU k n).measurable
  unfold MatedCRTHarmonic.CellScaling.lqgAreaApprox
  rw [← withDensity_mul _ hm hψ]
  unfold extApprox
  congr 1
  funext z
  simp only [Pi.mul_apply, extDensity]
  by_cases hz : z ∈ ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ)
  · rw [hcirc z hz, ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by
      unfold MatedCRTHarmonic.CellScaling.dyadicScale; positivity) _) (Real.exp_pos _).le), mul_comm]
  · simp [extPOU_of_notMem hz]

/-- **The decoded measure.** For a field with continuous circle averages whose dyadic area approximations
converge vaguely to `μ`, the decoder applied to the restriction to `{|w| > k}` is `μ` restricted to
`{|w| > k + 1}`. -/
theorem extAreaDecode_eq {γ : ℝ} {k : ℕ} {h : LQGMetric.DistC} (hh : ConeAreaCovariance.ScaleRegular h)
    {μ : Measure ℂ}
    (hμ : MatedCRTHarmonic.CellScaling.IsVagueLimitC (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h) μ) :
    extAreaDecode γ k (LQGMetric.restrictTo (extOpen (k : ℝ)) h) =
      μ.restrict ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ) := by
  classical
  set W : Set ℂ := ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ) with hW
  have hWo : IsOpen W := (extOpen ((k : ℝ) + 1)).isOpen
  have hsmall : ∀ᶠ j : ℕ in atTop, MatedCRTHarmonic.CellScaling.dyadicScale j < 1 :=
    ((tendsto_nhdsWithin_iff.1 MatedCRTHarmonic.LQGCoord.tendsto_dyadicScale).1).eventually
      (gt_mem_nhds one_pos)
  have hcirc : ∀ᶠ j : ℕ in atTop, ∀ z ∈ W,
      extLocalCircle k (LQGMetric.restrictTo (extOpen (k : ℝ)) h) (MatedCRTHarmonic.CellScaling.dyadicScale j) z =
        LQGMetric.circleAvg h (MatedCRTHarmonic.CellScaling.dyadicScale j) z := by
    filter_upwards [hsmall] with j hj z hz
    have hpos : 0 < MatedCRTHarmonic.CellScaling.dyadicScale j := by
      unfold MatedCRTHarmonic.CellScaling.dyadicScale
      positivity
    exact extLocalCircle_restrictTo hh hpos hj hz
  have step : ∀ n, LatticeProb.VagueLimit.vagueLimitOrZero
      (fun j => extApproxFin γ k n j (LQGMetric.restrictTo (extOpen (k : ℝ)) h)) =
        μ.withDensity fun z => ENNReal.ofReal (extPOU k n z) := by
    intro n
    have hlim := isVagueLimitC_withDensity hμ (continuous_extPOU k n) (extPOU_nonneg k n)
      (extPOU_le_one k n)
    have hev : ∀ᶠ j : ℕ in atTop,
        extApproxFin γ k n j (LQGMetric.restrictTo (extOpen (k : ℝ)) h) =
          (MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h j).withDensity
            fun z => ENNReal.ofReal (extPOU k n z) := by
      filter_upwards [hcirc] with j hc
      have hE := withDensity_extApprox (γ := γ) k n j hc
      have hlt : extApprox γ k n j (LQGMetric.restrictTo (extOpen (k : ℝ)) h) univ < ⊤ := by
        rw [hE, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        calc ∫⁻ z, ENNReal.ofReal (extPOU k n z) ∂MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h j
            ≤ ∫⁻ z, (closedBall (0 : ℂ) ((n : ℝ) + 2)).indicator (1 : ℂ → ℝ≥0∞) z
                ∂MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h j := by
              refine lintegral_mono fun z => ?_
              by_cases hz : z ∈ closedBall (0 : ℂ) ((n : ℝ) + 2)
              · simp only [Set.indicator_of_mem hz, Pi.one_apply]
                exact ENNReal.ofReal_le_one.2 (extPOU_le_one k n z)
              · have hz' : (n : ℝ) + 2 ≤ ‖z‖ := by
                  rw [mem_closedBall, dist_zero_right, not_le] at hz
                  exact hz.le
                simp [Set.indicator_of_notMem hz, extPOU_of_far hz']
          _ = MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h j (closedBall (0 : ℂ) ((n : ℝ) + 2)) :=
              lintegral_indicator_one measurableSet_closedBall
          _ < ⊤ := lqgAreaApprox_closedBall_lt_top hh j _
      simp only [extApproxFin, hlt, ↓reduceIte]
      exact hE
    have hlim' : MatedCRTHarmonic.MatedCRT.IsVagueLimitC
        (fun j => extApproxFin γ k n j (LQGMetric.restrictTo (extOpen (k : ℝ)) h))
        (μ.withDensity fun z => ENNReal.ofReal (extPOU k n z)) := by
      refine ⟨hlim.1, fun g hg hgc => (hlim.2 g hg hgc).congr' ?_⟩
      filter_upwards [hev] with j hj
      rw [hj]
    have hex : ∃ ν, LatticeProb.VagueLimit.IsVagueLimit
        (fun j => extApproxFin γ k n j (LQGMetric.restrictTo (extOpen (k : ℝ)) h)) ν :=
      ⟨_, hlim'⟩
    have h2 := LatticeProb.VagueLimit.isVagueLimit_vagueLimitOrZero hex
    have : IsFiniteMeasureOnCompacts (LatticeProb.VagueLimit.vagueLimitOrZero
        (fun j => extApproxFin γ k n j (LQGMetric.restrictTo (extOpen (k : ℝ)) h))) := inferInstance
    have : IsFiniteMeasureOnCompacts (μ.withDensity fun z => ENNReal.ofReal (extPOU k n z)) :=
      ⟨hlim'.1⟩
    refine Measure.ext_of_integral_eq_on_compactlySupported fun g => ?_
    exact tendsto_nhds_unique (h2.2 g g.continuous g.hasCompactSupport)
      (hlim'.2 g g.continuous g.hasCompactSupport)
  unfold extAreaDecode
  simp_rw [step]
  rw [← withDensity_tsum (μ := μ) (f := fun n z => ENNReal.ofReal (extPOU k n z))
    (fun n => ENNReal.measurable_ofReal.comp (continuous_extPOU k n).measurable)]
  have : (∑' n, fun z => ENNReal.ofReal (extPOU k n z)) = W.indicator 1 := by
    funext z
    rw [ENNReal.tsum_apply]
    exact tsum_ofReal_extPOU k z
  rw [this, withDensity_indicator_one hWo.measurableSet]

/-- **Locality of the area on the exterior** (area locality). The area measure of a field of the good set,
restricted to `{|w| > k + 1}`, is a measurable function of the restriction of the field to `{|w| > k}`: the
decoder reads the dyadic circle averages at scales below `1` on `{|w| > k + 1}` from the restriction. -/
theorem exists_extArea_decoder (γ : ℝ) (hγ : γ ≠ 0) (k : ℕ) :
    ∃ D : LQGMetric.DistOn (extOpen (k : ℝ)) → Measure ℂ, Measurable D ∧
      ∀ h ∈ ConeAreaCovariance.goodSet γ,
        D (LQGMetric.restrictTo (extOpen (k : ℝ)) h) =
          (ConeAreaCovariance.areaMap γ h).restrict (extOpen ((k : ℝ) + 1)) :=
  ⟨extAreaDecode γ k, measurable_extAreaDecode γ k, fun _ hh =>
    extAreaDecode_eq hh.1 (ConeAreaCovariance.areaMap_spec hγ hh).1⟩

/-! ### Mass radii of a restricted measure -/

/-- **The mass radius only depends on the masses of the balls it looks at**: if the ball `B_R(z)` lies in `W` and the
mass radius of `ν` at `z` is below `R`, then `ν` and its restriction to `W` have the same mass radius at `z`. -/
theorem massRadius_restrict_eq {ν : Measure ℂ} {W : Set ℂ} {s : ℝ} {z : ℂ} {R : ℝ}
    (hball : ball z R ⊆ W) (hlt : ZeroConeRoot.massRadius ν s z < R) :
    ZeroConeRoot.massRadius (ν.restrict W) s z = ZeroConeRoot.massRadius ν s z := by
  set S : Set ℝ := {r : ℝ | 0 < r ∧ ENNReal.ofReal s < ν (ball z r)} with hS
  set S' : Set ℝ := {r : ℝ | 0 < r ∧ ENNReal.ofReal s < (ν.restrict W) (ball z r)} with hS'
  have hsub : S' ⊆ S := fun r hr =>
    ⟨hr.1, hr.2.trans_le (Measure.le_iff'.1 Measure.restrict_le_self _)⟩
  have hbdd : BddBelow S := ⟨0, fun _ hr => hr.1.le⟩
  have hbdd' : BddBelow S' := ⟨0, fun _ hr => hr.1.le⟩
  have hin : ∀ r ∈ S, r < R → r ∈ S' := fun r hr hrR => ⟨hr.1, by
    rw [Measure.restrict_apply measurableSet_ball,
      Set.inter_eq_left.2 ((ball_subset_ball hrR.le).trans hball)]
    exact hr.2⟩
  show sInf S' = sInf S
  by_cases hne : S.Nonempty
  · obtain ⟨r0, hr0, hr0R⟩ := exists_lt_of_csInf_lt hne (show sInf S < R from hlt)
    have hr0' : r0 ∈ S' := hin r0 hr0 hr0R
    refine le_antisymm (le_csInf hne fun r hr => ?_) (csInf_le_csInf hbdd ⟨r0, hr0'⟩ hsub)
    by_cases hrR : r < R
    · exact csInf_le hbdd' (hin r hr hrR)
    · exact (csInf_le hbdd' hr0').trans (hr0R.le.trans (not_lt.1 hrR))
  · have h1 : S = ∅ := not_nonempty_iff_eq_empty.1 hne
    have h2 : S' = ∅ := eq_empty_of_subset_empty (h1 ▸ hsub)
    rw [h1, h2]

/-- The mass radius is monotone in the level, where it is positive. -/
theorem massRadius_le_of_pos {ν : Measure ℂ} {s s' : ℝ} {z : ℂ} (hs : s ≤ s')
    (hpos : 0 < ZeroConeRoot.massRadius ν s' z) :
    ZeroConeRoot.massRadius ν s z ≤ ZeroConeRoot.massRadius ν s' z := by
  have hne : {r : ℝ | 0 < r ∧ ENNReal.ofReal s' < ν (ball z r)}.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have h0 : ZeroConeRoot.massRadius ν s' z = 0 := by
      unfold ZeroConeRoot.massRadius
      rw [hne, Real.sInf_empty]
    linarith
  exact csInf_le_csInf ⟨0, fun _ hr => hr.1.le⟩ hne fun r hr =>
    ⟨hr.1, (ENNReal.ofReal_le_ofReal hs).trans_lt hr.2⟩

/-- The ball `B_{|z| - (k + 1)}(z)` lies in `{|w| > k + 1}`. -/
theorem ball_subset_extOpen {k : ℕ} (z : ℂ) :
    ball z (‖z‖ - ((k : ℝ) + 1)) ⊆ ((extOpen ((k : ℝ) + 1) : TopologicalSpace.Opens ℂ) : Set ℂ) := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  have h1 := norm_sub_norm_le z w
  rw [norm_sub_rev] at h1
  change (k : ℝ) + 1 < ‖w‖
  linarith

/-! ### The extension of a local distribution by a cut-off -/

section Cutoff

open scoped Distributions

/-- The smooth bump equal to `1` on `|w| ≤ k + 1` and to `0` on `|w| ≥ k + 2`. -/
def extBump (k : ℕ) : ContDiffBump (0 : ℂ) :=
  ⟨(k : ℝ) + 1, (k : ℝ) + 2, by positivity, by linarith⟩

/-- The smooth cut-off `1 - extBump k`: `0` on `|w| ≤ k + 1` and `1` on `|w| ≥ k + 2`. -/
def extChi (k : ℕ) (w : ℂ) : ℝ := 1 - extBump k w

theorem contDiff_extChi (k : ℕ) {n : ℕ∞} : ContDiff ℝ n (extChi k) :=
  contDiff_const.sub (extBump k).contDiff

theorem extChi_of_le {k : ℕ} {w : ℂ} (hw : ‖w‖ ≤ (k : ℝ) + 1) : extChi k w = 0 := by
  unfold extChi
  rw [(extBump k).one_of_mem_closedBall (by rw [mem_closedBall, dist_zero_right]; exact hw), sub_self]

theorem extChi_of_ge {k : ℕ} {w : ℂ} (hw : (k : ℝ) + 2 ≤ ‖w‖) : extChi k w = 1 := by
  unfold extChi
  rw [(extBump k).zero_of_le_dist (by rw [dist_zero_right]; exact hw), sub_zero]

theorem tsupport_extChi_subset (k : ℕ) : tsupport (extChi k) ⊆ {w : ℂ | (k : ℝ) + 1 ≤ ‖w‖} := by
  refine closure_minimal (fun w hw => ?_) (isClosed_le continuous_const continuous_norm)
  by_contra hlt
  exact hw (extChi_of_le (not_le.1 hlt).le)

/-- The product of a test function with the cut-off `extChi k`, a test function on `{|w| > k}`. -/
def extCutFun (k : ℕ) (φ : LQGMetric.TestC) : LQGMetric.TestOn (extOpen (k : ℝ)) :=
  ⟨fun w => φ w * extChi k w, φ.contDiff.mul (contDiff_extChi k), φ.hasCompactSupport.mul_right,
    (tsupport_mul_subset_right.trans (tsupport_extChi_subset k)).trans fun w hw =>
      show (k : ℝ) < ‖w‖ from lt_of_lt_of_le (lt_add_one _) hw⟩

/-- The compact set `K ∩ tsupport (extChi k)`. -/
def extK (k : ℕ) (K : TopologicalSpace.Compacts ℂ) : TopologicalSpace.Compacts ℂ :=
  ⟨(K : Set ℂ) ∩ tsupport (extChi k), K.isCompact.inter_right (isClosed_tsupport _)⟩

theorem extK_subset (k : ℕ) (K : TopologicalSpace.Compacts ℂ) :
    ((extK k K : TopologicalSpace.Compacts ℂ) : Set ℂ) ⊆
      ((extOpen (k : ℝ) : TopologicalSpace.Opens ℂ) : Set ℂ) :=
  fun w hw => show (k : ℝ) < ‖w‖ from lt_of_lt_of_le (lt_add_one _) (tsupport_extChi_subset k hw.2)

/-- Multiplication by the cut-off, from test functions supported in `K` to test functions supported in
`K ∩ tsupport (extChi k)` (the Leibniz estimate of `ContDiffMapSupportedIn.bilinLeftCLM`). -/
noncomputable def extCutLM (k : ℕ) (K : TopologicalSpace.Compacts ℂ) :
    𝓓_{K}(ℂ, ℝ) →L[ℝ] 𝓓_{extK k K}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.mkCLM ℝ (fun f w => f w * extChi k w)
    (fun f g x => by simp [add_mul]) (fun c f x => by simp [mul_assoc])
    (fun f => f.contDiff.mul (contDiff_extChi k))
    (fun f w hw => by
      by_cases hwK : w ∈ (K : Set ℂ)
      · have hw' : w ∉ tsupport (extChi k) := fun h => hw ⟨hwK, h⟩
        simp [image_eq_zero_of_notMem_tsupport hw']
      · simp [f.zero_on_compl hwK])
    (fun i _ => by
      have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extChi k) := contDiff_extChi k
      have hcont : Continuous fun x ↦ (Finset.range (i + 1)).sup' Finset.nonempty_range_add_one
          (fun j ↦ ‖iteratedFDeriv ℝ j (extChi k) x‖) :=
        Continuous.finset_sup'_apply Finset.nonempty_range_add_one fun j _ =>
          (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
      obtain ⟨C₀, hC₀⟩ := K.isCompact.exists_bound_of_continuousOn hcont.continuousOn
      have hgC₀ : ∀ j ≤ i, ∀ x ∈ (K : Set ℂ), ‖iteratedFDeriv ℝ j (extChi k) x‖ ≤ ‖C₀‖ :=
        fun j hj x hx ↦ (Finset.le_sup' _ (Finset.mem_range_succ_iff.2 hj)).trans
          ((Real.le_norm_self _).trans ((hC₀ x hx).trans (Real.le_norm_self C₀)))
      refine ⟨Finset.Iic i, ‖ContinuousLinearMap.mul ℝ ℝ‖ * 2 ^ i * ‖C₀‖, by positivity,
        fun φ x hx ↦ ?_⟩
      calc ‖iteratedFDeriv ℝ i (fun y ↦ ContinuousLinearMap.mul ℝ ℝ (φ y) (extChi k y)) x‖
          ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
              ‖iteratedFDeriv ℝ j φ x‖ * ‖iteratedFDeriv ℝ (i - j) (extChi k) x‖ := by
            simpa using (ContinuousLinearMap.mul ℝ ℝ).norm_iteratedFDeriv_le_of_bilinear
              φ.contDiff hg x (by exact_mod_cast le_top)
        _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
              ((Finset.Iic i).sup fun m ↦ N[ℝ]_{K, ⊤, m}) φ * ‖C₀‖ := by
            gcongr with j hj
            · exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
                (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 (Finset.mem_range_succ_iff.mp hj)))
            · exact hgC₀ (i - j) (Nat.sub_le i j) x hx.1
        _ = ‖ContinuousLinearMap.mul ℝ ℝ‖ * 2 ^ i * ‖C₀‖ *
              ((Finset.Iic i).sup fun m ↦ N[ℝ]_{K, ⊤, m}) φ := by
            simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
            push_cast
            ring)

/-- **The cut-off**: `φ ↦ φ · extChi k`, a continuous linear map from test functions on the plane to test functions
on `{|w| > k}`. -/
noncomputable def extCutCLM (k : ℕ) : LQGMetric.TestC →L[ℝ] LQGMetric.TestOn (extOpen (k : ℝ)) :=
  TestFunction.limitCLM ℝ (extCutFun k)
    (fun K _ => TestFunction.ofSupportedInCLM ℝ (extK_subset k K) ∘L extCutLM k K)
    (fun _ _ _ => TestFunction.ext fun _ => rfl)

theorem extCutCLM_apply (k : ℕ) (φ : LQGMetric.TestC) (w : ℂ) : extCutCLM k φ w = φ w * extChi k w := by
  simp [extCutCLM, extCutFun]

/-- The extension of a distribution on `{|w| > k}` to the plane: `φ ↦ T(φ · extChi k)`. -/
def extExtend (k : ℕ) (T : LQGMetric.DistOn (extOpen (k : ℝ))) : LQGMetric.DistC :=
  T.comp (extCutCLM k)

theorem extExtend_apply (k : ℕ) (T : LQGMetric.DistOn (extOpen (k : ℝ))) (φ : LQGMetric.TestC) :
    extExtend k T φ = T (extCutCLM k φ) := rfl

theorem measurable_extExtend (k : ℕ) : Measurable (extExtend k) :=
  LQGMetric.measurable_distOn_iff.2 fun φ => LQGMetric.measurable_distOn_apply (extCutCLM k φ)

/-- The extension of the restriction of a field agrees with the field on test functions supported in
`{|w| ≥ k + 2}`. -/
theorem extExtend_restrictTo (k : ℕ) (h : LQGMetric.DistC) {ψ : LQGMetric.TestC}
    (hψ : ∀ w, ψ w ≠ 0 → (k : ℝ) + 2 ≤ ‖w‖) :
    extExtend k (LQGMetric.restrictTo (extOpen (k : ℝ)) h) ψ = h ψ := by
  have hmono : (TestFunction.monoCLM ℝ (extCutCLM k ψ) : LQGMetric.TestC) = ψ := by
    refine TestFunction.ext fun w => ?_
    have h1 : ((TestFunction.monoCLM ℝ (extCutCLM k ψ) : LQGMetric.TestC) : ℂ → ℝ) w =
        extCutCLM k ψ w := by simp
    rw [h1, extCutCLM_apply]
    by_cases hw : ψ w = 0
    · rw [hw, zero_mul]
    · rw [extChi_of_ge (hψ w hw), mul_one]
  change h (TestFunction.monoCLM ℝ (extCutCLM k ψ)) = h ψ
  rw [hmono]

end Cutoff

/-- **The change of coordinates of the extension of a restriction, restricted to a disc**: for `B_{aC}(z)` in
`{|w| > k + 2}` it is the restriction to the disc `B_a(0)` of the change of coordinates of the field. -/
theorem restrictTo_similarity_extExtend (γ : ℝ) (k a : ℕ) (h : LQGMetric.DistC) {C : ℝ} (hC : 0 < C)
    {z : ℂ} (hz : (a : ℝ) * C < ‖z‖ - ((k : ℝ) + 2)) :
    LQGMetric.restrictTo (a1Ball a)
        (lqgSimilarityField γ C z (extExtend k (LQGMetric.restrictTo (extOpen (k : ℝ)) h))) =
      LQGMetric.restrictTo (a1Ball a) (lqgSimilarityField γ C z h) := by
  refine DFunLike.ext _ _ fun φ => ?_
  have hψ : ∀ w, LQGMetric.testAffinePull C z (TestFunction.monoCLM ℝ φ) w ≠ 0 →
      (k : ℝ) + 2 ≤ ‖w‖ := by
    intro w hw
    rw [LQGMetric.testAffinePull_apply C z hC.ne'] at hw
    have hmem : (w - z) / (C : ℂ) ∈ tsupport (φ : ℂ → ℝ) := subset_tsupport _ (by simpa using hw)
    have hlt : ‖(w - z) / (C : ℂ)‖ < a := by
      have := φ.tsupport_subset hmem
      simpa [a1Ball] using this
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC, div_lt_iff₀ hC] at hlt
    have h1 := norm_sub_norm_le z w
    rw [norm_sub_rev] at h1
    linarith
  change LQGMetric.addConst (LQGMetric.affineComp C z
      (extExtend k (LQGMetric.restrictTo (extOpen (k : ℝ)) h))) (MatedCRTHarmonic.MatedCRT.lqgQ γ * Real.log C)
      (TestFunction.monoCLM ℝ φ) =
    LQGMetric.addConst (LQGMetric.affineComp C z h) (MatedCRTHarmonic.MatedCRT.lqgQ γ * Real.log C)
      (TestFunction.monoCLM ℝ φ)
  rw [LQGMetric.GFFInv.addConst_apply, LQGMetric.GFFInv.addConst_apply,
    LQGMetric.GFFInv.affineComp_apply, LQGMetric.GFFInv.affineComp_apply, extExtend_restrictTo k h hψ]

/-- The change of coordinates of the extension of a local distribution, restricted to the disc `B_a(0)`, is jointly
measurable in the parameters and the distribution. -/
theorem measurable_extFieldRestrict (γ : ℝ) (k a : ℕ) :
    Measurable fun p : (ℝ × ℂ) × LQGMetric.DistOn (extOpen (k : ℝ)) =>
      LQGMetric.restrictTo (a1Ball a) (lqgSimilarityAction γ p.1 (extExtend k p.2)) :=
  (LQGMetric.measurable_restrictTo _).comp ((measurable_lqgSimilarityAction γ).comp
    (measurable_fst.prodMk ((measurable_extExtend k).comp measurable_snd)))

/-- **The exterior version of the local observation.** At a point `z` whose mass radius `r_{b₀}(z)` is below
`|z| - (k + 2)`, the local observation `J(h, z)` of a field of the good set is a jointly measurable function of the
restriction of the field to `{|w| > k}` and of `z`: the mass radii are computed from the decoded exterior area, and
the normalized field on `B_a(0)` only involves the field on `B_{a r_1(z)}(z) ⊆ {|w| > k + 2}`. -/
theorem exists_rootObs_extVersion (γ : ℝ) (hγ : γ ≠ 0) {a : ℕ} {f : LQGMetric.DistOn (a1Ball a) → ℝ}
    (hfm : Measurable f) {b₀ : ℝ} (hb₀ : 1 ≤ b₀) (k : ℕ) :
    ∃ G : LQGMetric.DistOn (extOpen (k : ℝ)) × ℂ → ℝ, Measurable G ∧
      ∀ h ∈ ConeAreaCovariance.goodSet γ, ∀ z : ℂ,
        ZeroConeRoot.massRadius (ConeAreaCovariance.areaMap γ h) b₀ z < ‖z‖ - ((k : ℝ) + 2) →
          G (LQGMetric.restrictTo (extOpen (k : ℝ)) h, z) = rootObs γ f b₀ h z := by
  classical
  obtain ⟨D, hDm, hD⟩ := exists_extArea_decoder γ hγ k
  have hr : ∀ s : ℝ, Measurable fun p : LQGMetric.DistOn (extOpen (k : ℝ)) × ℂ =>
      ZeroConeRoot.massRadius (D p.1) s p.2 := fun s => by
    have h3 := (ZeroConeRoot.measurable_massRadius s).comp
      ((hDm.comp measurable_fst).prodMk measurable_snd)
    simp only [Function.comp_def] at h3
    exact h3
  refine ⟨fun p => if 0 < ZeroConeRoot.massRadius (D p.1) 1 p.2 ∧
      (a : ℝ) * ZeroConeRoot.massRadius (D p.1) 1 p.2 < ZeroConeRoot.massRadius (D p.1) b₀ p.2 then
      f (LQGMetric.restrictTo (a1Ball a)
        (lqgSimilarityAction γ (ZeroConeRoot.massRadius (D p.1) 1 p.2, p.2) (extExtend k p.1)))
    else 0, ?_, ?_⟩
  · refine Measurable.ite ((measurableSet_lt measurable_const (hr 1)).inter
      (measurableSet_lt ((hr 1).const_mul _) (hr b₀))) ?_ measurable_const
    exact hfm.comp ((measurable_extFieldRestrict γ k a).comp (((hr 1).prodMk measurable_snd).prodMk
      measurable_fst))
  · intro h hh z hz
    have hν := hD h hh
    set ν := ConeAreaCovariance.areaMap γ h with hνdef
    have hR : ‖z‖ - ((k : ℝ) + 2) < ‖z‖ - ((k : ℝ) + 1) := by linarith
    have hball := ball_subset_extOpen (k := k) z
    have hb : ZeroConeRoot.massRadius (ν.restrict (extOpen ((k : ℝ) + 1))) b₀ z =
        ZeroConeRoot.massRadius ν b₀ z := massRadius_restrict_eq hball (hz.trans hR)
    simp only [hν]
    by_cases hpos : 0 < ZeroConeRoot.massRadius ν b₀ z
    · have h1 : ZeroConeRoot.massRadius ν 1 z ≤ ZeroConeRoot.massRadius ν b₀ z :=
        massRadius_le_of_pos hb₀ hpos
      have ha : ZeroConeRoot.massRadius (ν.restrict (extOpen ((k : ℝ) + 1))) 1 z =
          ZeroConeRoot.massRadius ν 1 z :=
        massRadius_restrict_eq hball ((h1.trans_lt hz).trans hR)
      rw [ha, hb]
      by_cases ht : RootTest γ a b₀ h z
      · have hC := ht.1
        have hrf : rootField γ h z = lqgSimilarityField γ (ZeroConeRoot.massRadius ν 1 z) z h := rfl
        have hz' : (a : ℝ) * ZeroConeRoot.massRadius ν 1 z < ‖z‖ - ((k : ℝ) + 2) :=
          ht.2.trans hz
        have htt : 0 < ZeroConeRoot.massRadius ν 1 z ∧
            (a : ℝ) * ZeroConeRoot.massRadius ν 1 z < ZeroConeRoot.massRadius ν b₀ z := ht
        simp only [rootObs, ht, htt, and_self, ↓reduceIte, hrf]
        congr 1
        rw [lqgSimilarityAction_of_pos γ (t := (ZeroConeRoot.massRadius ν 1 z, z)) hC]
        exact restrictTo_similarity_extExtend γ k a h hC hz'
      · have hnt : ¬ (0 < ZeroConeRoot.massRadius ν 1 z ∧
            (a : ℝ) * ZeroConeRoot.massRadius ν 1 z < ZeroConeRoot.massRadius ν b₀ z) := ht
        simp only [rootObs, ht, hnt, ↓reduceIte]
    · have h0 : ZeroConeRoot.massRadius ν b₀ z = 0 :=
        le_antisymm (not_lt.1 hpos) (ZeroConeRoot.massRadius_nonneg _ _ _)
      have hnt : ¬ (0 < ZeroConeRoot.massRadius ν 1 z ∧
          (a : ℝ) * ZeroConeRoot.massRadius ν 1 z < ZeroConeRoot.massRadius ν b₀ z) := by
        rintro ⟨h2, h3⟩
        rw [h0] at h3
        nlinarith [Nat.cast_nonneg (α := ℝ) a]
      have hnt' : ¬ (0 < ZeroConeRoot.massRadius (ν.restrict (extOpen ((k : ℝ) + 1))) 1 z ∧
          (a : ℝ) * ZeroConeRoot.massRadius (ν.restrict (extOpen ((k : ℝ) + 1))) 1 z <
            ZeroConeRoot.massRadius (ν.restrict (extOpen ((k : ℝ) + 1))) b₀ z) := by
        rintro ⟨h2, h3⟩
        rw [hb, h0] at h3
        nlinarith [Nat.cast_nonneg (α := ℝ) a]
      have hnt'' : ¬ RootTest γ a b₀ h z := hnt
      simp only [rootObs, hnt', hnt'', ↓reduceIte]

end MatedCRT
