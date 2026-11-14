import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity

/-!
# Harmonic measure of a disc from an off-centre point

For planar Brownian motion started at a point `y` of the open disc `B_r(c)`, the exit point of the
disc has the **harmonic measure** of the disc seen from `y`: the normalized angular measure on the
circle `∂B_r(c)` with density the Poisson kernel `P(c, y, ·)`. In integral form,
`E_y[f(B_{τ})] = P_{B_r(c)}[f](y)` (the Poisson integral) for bounded continuous `f`.

This extends the centred case of the harmonic-ball development (exit at the centre is uniform on
the circle) and is the second step towards the continuity of Euclidean harmonic measure in the
base point (Gwynne-Miller-Sheffield, invariance principle, proof of Lemma 3.14).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric InnerProductSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open HarmonicBalls HarmonicBalls.Section6

namespace MatedCRT

/-- Brownian motion started inside a disc almost surely leaves it in finite time, at a point of
the bounding circle. -/
theorem ae_planarBrownian_disc_exitPoint_mem_sphere {c y : ℂ} {r : ℝ} (hy : y ∈ ball c r) :
    ∀ᵐ ω ∂(planarBrownianMotion y),
      ContinuousPath.exitTime (ball c r) ω ≠ ⊤ ∧
      ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal) ∈ sphere c r := by
  have hr : 0 < r := pos_of_mem_ball hy
  have hsub : ball c r ⊆ ball y (2 * r) := by
    intro z hz
    rw [mem_ball] at hz hy ⊢
    calc dist z y ≤ dist z c + dist y c := dist_triangle_right z y c
      _ < 2 * r := by linarith
  filter_upwards [ae_planarBrownianMotion_exitTime_ball_lt_top y (2 * r),
    ae_planarBrownianMotion_eval_zero y] with ω hfin h0
  have hfin' : ContinuousPath.exitTime (ball c r) ω ≠ ⊤ :=
    ((ContinuousPath.exitTime_mono hsub ω).trans_lt hfin).ne
  refine ⟨hfin', ?_⟩
  have hfr := ContinuousPath.coordinate_exitTime_mem_frontier (ball c r) isOpen_ball ω
    (by rw [h0]; exact hy) hfin'
  rwa [frontier_ball c hr.ne'] at hfr

/-- **Exit expectation from an off-centre start.** For `y` in the disc `B_r(c)` and a bounded
continuous `f`, the expected value of `f` at the Brownian exit point of the disc is the Poisson
integral of `f` at `y`. -/
theorem planarBrownian_integral_disc_exit_eq_discPoissonIntegral
    {c y : ℂ} {r : ℝ} (hy : y ∈ ball c r) {f : ℂ → ℝ}
    (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) :
    (∫ ω : ContinuousPath ℂ, f (ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal))
      ∂(planarBrownianMotion y)) = discPoissonIntegral f c r y := by
  have hr : 0 < r := pos_of_mem_ball hy
  let q := discSweep Set.univ c r f
  have hD : IsSweepDisc Set.univ c r := ⟨hr, subset_univ _⟩
  have hq : Continuous q := by
    apply continuousOn_univ.mp
    exact continuousOn_discSweep isOpen_univ hf.continuousOn
  have hci : CircleIntegrable f c r := hD.circleIntegrable hf.continuousOn
  have hh : HarmonicOnNhd q (ball c r) := by
    intro z hz
    have heq : q =ᶠ[𝓝 z] discPoissonIntegral f c r := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact discSweep_of_mem hD hw
    exact (harmonicAt_congr_nhds heq).2 (harmonicOnNhd_discPoissonIntegral hci z hz)
  have hbound : ∀ z, ‖q z‖ ≤ M := by
    intro z
    by_cases hz : z ∈ ball c r
    · rw [show q z = discPoissonIntegral f c r z from discSweep_of_mem hD hz]
      have hb (w : ℂ) : -M ≤ f w ∧ f w ≤ M := by
        have := hM w
        rw [Real.norm_eq_abs, abs_le] at this
        exact this
      have hlo := le_discPoissonIntegral hci hz (fun ζ _ => (hb ζ).1)
      have hhi : discPoissonIntegral f c r z ≤ M := by
        rw [← discPoissonIntegral_const M hz]
        exact discPoissonIntegral_mono hci continuousOn_const.circleIntegrable' hz
          (fun ζ _ => (hb ζ).2)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hlo, hhi⟩
    · rw [show q z = f z from discSweep_of_not (fun h => hz h.2)]
      exact hM z
  have he := harmonic_eq_integral_planarBrownian_exitTime isOpen_ball isBounded_ball
    hq hh hbound hy
  have hEq : ∀ᵐ ω ∂(planarBrownianMotion y),
      q (ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal)) =
      f (ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal)) := by
    filter_upwards [ae_planarBrownian_disc_exitPoint_mem_sphere hy] with ω ⟨_, hsphere⟩
    exact discSweep_of_not (fun h => (sphere_disjoint_ball.ne_of_mem hsphere h.2) rfl)
  rw [integral_congr_ae hEq] at he
  rw [show q y = discPoissonIntegral f c r y from discSweep_of_mem hD hy] at he
  exact he.symm

/-- The **harmonic measure** of the disc `B_r(c)` seen from `y`: the normalized angular measure
on the circle `∂B_r(c)` with density the Poisson kernel `P(c, y, ·)`. -/
noncomputable def discHarmonicMeasure (c : ℂ) (r : ℝ) (y : ℂ) : Measure ℂ :=
  (normalizedCircleMeasure c r).withDensity (fun ζ => ENNReal.ofReal (poissonKernel c y ζ))

/-- The harmonic measure of a disc seen from an interior point is a finite measure. -/
theorem isFiniteMeasure_discHarmonicMeasure {c y : ℂ} {r : ℝ} (hy : y ∈ ball c r) :
    IsFiniteMeasure (discHarmonicMeasure c r y) := by
  have hr : 0 < r := pos_of_mem_ball hy
  obtain ⟨K, hK⟩ := (isCompact_sphere c |r|).exists_bound_of_continuousOn
    (continuousOn_poissonKernel hy)
  have hθ : ∀ θ : ℝ, ENNReal.ofReal (poissonKernel c y (circleMap c r θ)) ≤ ENNReal.ofReal K :=
    fun θ => ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans
      (hK _ (by rw [abs_of_pos hr]; exact circleMap_mem_sphere c hr.le θ)))
  refine ⟨?_⟩
  rw [discHarmonicMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    normalizedCircleMeasure, lintegral_map (measurable_poissonKernel_comp' c y).ennreal_ofReal
      (continuous_circleMap c r).measurable]
  refine lt_of_le_of_lt (lintegral_mono hθ) ?_
  rw [lintegral_const, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ioc, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- Integration against the harmonic measure of a disc is the Poisson integral. -/
theorem integral_discHarmonicMeasure {c y : ℂ} {r : ℝ} (hy : y ∈ ball c r) {g : ℂ → ℝ}
    (hg : Measurable g) :
    (∫ z, g z ∂(discHarmonicMeasure c r y)) = discPoissonIntegral g c r y := by
  have hr : 0 < r := pos_of_mem_ball hy
  have hP := (measurable_poissonKernel_comp' c y).ennreal_ofReal
  rw [discHarmonicMeasure, integral_withDensity_eq_integral_toReal_smul hP
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    HarmonicBalls.integral_normalizedCircleMeasure_of_measurable c r
      (f := fun z => (ENNReal.ofReal (poissonKernel c y z)).toReal • g z) (hP.ennreal_toReal.smul hg)]
  unfold discPoissonIntegral
  apply Real.circleAverage_congr_sphere
  intro ζ hζ
  rw [abs_of_pos hr] at hζ
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (poissonKernel_pos hy hζ).le]
  rfl

/-- **Exit distribution from an off-centre start.** Brownian motion started at `y ∈ B_r(c)`
leaves the disc with the harmonic measure of the disc seen from `y`. -/
theorem planarBrownian_disc_exit_distribution_of_mem {c y : ℂ} {r : ℝ} (hy : y ∈ ball c r) :
    (planarBrownianMotion y).map
      (fun ω => ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal)) =
      discHarmonicMeasure c r y := by
  have ht := ContinuousPath.isStoppingTime_exitTime (ball c r) isOpen_ball
  have hm : Measurable (fun ω : ContinuousPath ℂ =>
      ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime (ball c r)) ht
  have := isFiniteMeasure_discHarmonicMeasure hy
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hm.aemeasurable f.continuous.aestronglyMeasurable,
    integral_discHarmonicMeasure hy f.continuous.measurable]
  exact planarBrownian_integral_disc_exit_eq_discPoissonIntegral hy f.continuous
    f.norm_coe_le_norm

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.ae_planarBrownian_disc_exitPoint_mem_sphere
#print axioms MatedCRT.planarBrownian_integral_disc_exit_eq_discPoissonIntegral
#print axioms MatedCRT.isFiniteMeasure_discHarmonicMeasure
#print axioms MatedCRT.integral_discHarmonicMeasure
#print axioms MatedCRT.planarBrownian_disc_exit_distribution_of_mem
