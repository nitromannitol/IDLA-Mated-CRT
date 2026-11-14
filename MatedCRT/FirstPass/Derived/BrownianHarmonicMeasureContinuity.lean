import MatedCRT.FirstPass.Derived.BrownianExitPointRestart
import MatedCRT.FirstPass.Derived.BrownianDiscPoissonExit

/-!
# Continuity of Euclidean harmonic measure in the base point

Let `U` be a bounded open set containing the closed disc `closedBall c ρ`. For base points `y`,
`y'` in the open disc `B_ρ(c)`, the harmonic measures of `U` seen from `y` and from `y'` (the
exit distributions of planar Brownian motion) differ in total variation by at most the circle
average of `|P(c, y, ·) - P(c, y', ·)|`, where `P` is the Poisson kernel of the disc:
for every Borel set `A`,
`|P_y(B_{τ_U} ∈ A) - P_{y'}(B_{τ_U} ∈ A)| ≤ M(|P(c, y, ·) - P(c, y', ·)|; c, ρ)`.

The proof restarts Brownian motion at its exit from the disc (strong Markov property) and uses
that the exit point of the disc from `y` has the Poisson-kernel harmonic measure of the disc.
This is the continuity of harmonic measure in the base point used in the proof of Lemma 3.14 of
the Gwynne-Miller-Sheffield invariance principle.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology
open HarmonicBalls HarmonicBalls.Section6

namespace MatedCRT

/-- A path started in the disc `B_ρ(c)`, whose exit point from the disc lies on the circle
`∂B_ρ(c)`, leaves the disc strictly before it leaves any open set `U ⊇ closedBall c ρ`. -/
theorem exitTime_ball_lt_exitTime {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {ρ : ℝ}
    (hsub : closedBall c ρ ⊆ U) (ω : ContinuousPath ℂ) (h0 : ω 0 ∈ ball c ρ)
    (hfin : ContinuousPath.exitTime (ball c ρ) ω ≠ ⊤)
    (hsph : ω ((ContinuousPath.exitTime (ball c ρ) ω).toNNReal) ∈ sphere c ρ) :
    ContinuousPath.exitTime (ball c ρ) ω < ContinuousPath.exitTime U ω := by
  refine lt_of_not_ge fun hle => ?_
  have hUfin : ContinuousPath.exitTime U ω ≠ ⊤ := ne_top_of_le_ne_top hfin hle
  have hfr := ContinuousPath.coordinate_exitTime_mem_frontier U hU ω
    (hsub (ball_subset_closedBall h0)) hUfin
  rw [hU.frontier_eq] at hfr
  apply hfr.2
  rcases hle.lt_or_eq with hlt | heq
  · apply hsub
    apply ball_subset_closedBall
    apply ContinuousPath.mem_of_lt_exitTime
    rwa [ENNReal.coe_toNNReal hUfin]
  · rw [heq]
    exact hsub (sphere_subset_closedBall hsph)

/-- **Harmonic measure of `U` through the disc.** For a bounded open `U ⊇ closedBall c ρ` and
`y ∈ B_ρ(c)`, the probability that Brownian motion from `y` leaves `U` in `A` is the average,
against the harmonic measure of the disc seen from `y`, of the same probability from the start
point `z ∈ ∂B_ρ(c)`. -/
theorem planarBrownian_exitPoint_eq_lintegral_discHarmonicMeasure {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {c y : ℂ} {ρ : ℝ} (hsub : closedBall c ρ ⊆ U)
    (hy : y ∈ ball c ρ) {A : Set ℂ} (hA : MeasurableSet A) :
    planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A} =
      ∫⁻ z, planarBrownianMotion z {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}
        ∂(discHarmonicMeasure c ρ y) := by
  have hmU : Measurable (fun p : ContinuousPath ℂ =>
      p ((ContinuousPath.exitTime U p).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  have hmV : Measurable (fun p : ContinuousPath ℂ =>
      p ((ContinuousPath.exitTime (ball c ρ) p).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime (ball c ρ))
      (ContinuousPath.isStoppingTime_exitTime (ball c ρ) isOpen_ball)
  have hE : MeasurableSet {p : ContinuousPath ℂ |
      p ((ContinuousPath.exitTime U p).toNNReal) ∈ A} := hmU hA
  obtain ⟨R, hR⟩ := hUb.subset_ball y
  have hae := ae_planarBrownian_disc_exitPoint_mem_sphere hy
  rw [planarBrownian_exitPoint_restart hU isOpen_ball
    (by filter_upwards [hae] with ω hω; exact lt_top_iff_ne_top.2 hω.1)
    (by
      filter_upwards [hae, ae_planarBrownianMotion_eval_zero y] with ω hω h0
      exact exitTime_ball_lt_exitTime hU hsub ω (by rw [h0]; exact hy) hω.1 hω.2)
    (by
      filter_upwards [ae_planarBrownianMotion_exitTime_ball_lt_top y R] with ω hω
      exact ((ContinuousPath.exitTime_mono hR ω).trans_lt hω).ne)
    hA,
    ← planarBrownian_disc_exit_distribution_of_mem hy,
    lintegral_map (Kernel.measurable_coe _ hE) hmV]

/-- The probability of leaving `U` in `A`, as a function of the base point in the disc, is the
Poisson integral of its values on the circle. -/
theorem planarBrownian_exitPoint_toReal_eq_discPoissonIntegral {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {c x : ℂ} {ρ : ℝ} (hsub : closedBall c ρ ⊆ U)
    (hx : x ∈ ball c ρ) {A : Set ℂ} (hA : MeasurableSet A) :
    (planarBrownianMotion x {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal =
      discPoissonIntegral (fun z => (planarBrownianMotion z
        {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}).toReal) c ρ x := by
  have hmU : Measurable (fun p : ContinuousPath ℂ =>
      p ((ContinuousPath.exitTime U p).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  have hE : MeasurableSet {p : ContinuousPath ℂ |
      p ((ContinuousPath.exitTime U p).toNNReal) ∈ A} := hmU hA
  have hk := Kernel.measurable_coe planarBrownianMotion hE
  rw [planarBrownian_exitPoint_eq_lintegral_discHarmonicMeasure hU hUb hsub hx hA,
    ← integral_discHarmonicMeasure hx hk.ennreal_toReal]
  have := isFiniteMeasure_discHarmonicMeasure hx
  exact (integral_toReal hk.aemeasurable
    (Eventually.of_forall fun z => measure_lt_top _ _)).symm

/-- **Total-variation continuity of harmonic measure in the base point.** For a bounded open
`U ⊇ closedBall c ρ`, base points `y, y' ∈ B_ρ(c)` and every Borel set `A`, the exit
probabilities of `U` through `A` differ by at most the circle average of the difference of
Poisson kernels `|P(c, y, ·) - P(c, y', ·)|` (a bound uniform in `A`). -/
theorem abs_planarBrownian_exitPoint_sub_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {c y y' : ℂ} {ρ : ℝ} (hsub : closedBall c ρ ⊆ U)
    (hy : y ∈ ball c ρ) (hy' : y' ∈ ball c ρ) {A : Set ℂ} (hA : MeasurableSet A) :
    |(planarBrownianMotion y {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal -
      (planarBrownianMotion y' {ω | ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ A}).toReal| ≤
      Real.circleAverage (fun ζ => |poissonKernel c y ζ - poissonKernel c y' ζ|) c ρ := by
  have hmU : Measurable (fun p : ContinuousPath ℂ =>
      p ((ContinuousPath.exitTime U p).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime U) (ContinuousPath.isStoppingTime_exitTime U hU)
  have hE : MeasurableSet {p : ContinuousPath ℂ |
      p ((ContinuousPath.exitTime U p).toNNReal) ∈ A} := hmU hA
  have hgm := (Kernel.measurable_coe planarBrownianMotion hE).ennreal_toReal
  rw [planarBrownian_exitPoint_toReal_eq_discPoissonIntegral hU hUb hsub hy hA,
    planarBrownian_exitPoint_toReal_eq_discPoissonIntegral hU hUb hsub hy' hA]
  have hg0 : ∀ z, 0 ≤ (planarBrownianMotion z
      {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}).toReal :=
    fun z => ENNReal.toReal_nonneg
  have hg1 : ∀ z, (planarBrownianMotion z
      {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}).toReal ≤ 1 := by
    intro z
    calc _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      _ = 1 := ENNReal.toReal_one
  have hgci : CircleIntegrable (fun z => (planarBrownianMotion z
      {p | p ((ContinuousPath.exitTime U p).toNNReal) ∈ A}).toReal) c ρ := by
    refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const
      (hgm.comp (continuous_circleMap c ρ).measurable).aestronglyMeasurable
      (Eventually.of_forall fun θ => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
    exact hg1 _
  have h1 := HarmonicBalls.CircleIntegrable.poissonKernel_smul hgci hy
  have h2 := HarmonicBalls.CircleIntegrable.poissonKernel_smul hgci hy'
  unfold discPoissonIntegral
  rw [← Real.circleAverage_sub h1 h2]
  refine Real.abs_circleAverage_le_circleAverage_abs.trans ?_
  apply Real.circleAverage_mono (h1.sub h2).abs
    ((continuousOn_poissonKernel hy).sub (continuousOn_poissonKernel hy')).abs.circleIntegrable'
  intro ζ _
  simp only [Pi.abs_apply, Pi.sub_apply, smul_eq_mul, Pi.mul_apply]
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_of_nonneg (hg0 ζ)]; exact hg1 ζ)

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.exitTime_ball_lt_exitTime
#print axioms MatedCRT.planarBrownian_exitPoint_eq_lintegral_discHarmonicMeasure
#print axioms MatedCRT.planarBrownian_exitPoint_toReal_eq_discPoissonIntegral
#print axioms MatedCRT.abs_planarBrownian_exitPoint_sub_le
