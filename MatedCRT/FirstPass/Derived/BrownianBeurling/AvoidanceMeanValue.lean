import MatedCRT.FirstPass.Derived.BrownianBeurling.AvoidanceProbability
import HarmonicBalls.Proofs.Sec6.AvoidanceDiscRestart
import HarmonicBalls.Proofs.Sec6.AvoidanceBallSubmean

/-!
# The mean value property of the avoidance probability on circles

Let `U` be open, `K` compact, and `E` the event that planar Brownian motion leaves `U` no later than
it hits `K`. For a disc `closedBall x r` disjoint from `K` and an outer disc `ball x R ⊆ U`, the
Brownian path started at `x` reaches the circle `sphere x r` strictly before leaving `ball x R`,
and strictly before hitting `K`. Consequently `E` coincides almost surely with its preimage under
the shift by the exit time `τ` of `ball x r`: after the shift, leaving `U` before hitting `K` is
the same as it was before. The strong Markov property then gives the identity
`P^x (E) = ∫ P^{ω τ} (E) dP^x`, and the exit law of `ball x r` is the normalized circle measure.
Thus the avoidance probability has the mean value property over circles, stated both as an
equality of integrals against `normalizedCircleMeasure x r` and as an equality with
`Real.circleAverage`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.BrownianBeurling

/-- A Brownian path from the centre of `ball x r` exits the disc strictly before it hits a compact
set disjoint from `closedBall x r`. -/
private theorem ae_exitTime_ball_lt_exitTime_compl {K : Set ℂ} (hK : IsCompact K) {x : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hrK : Disjoint (closedBall x r) K) :
    ∀ᵐ ω ∂(planarBrownianMotion x),
      ContinuousPath.exitTime (ball x r) ω < ContinuousPath.exitTime Kᶜ ω := by
  have hfin := Section6.ae_planarBrownianMotion_exitTime_ball_lt_top x r
  have hcross := Section6.ae_planarBrownian_ball_crossing_unconditional (x := x) hr hrR
  filter_upwards [hfin, hcross] with ω hf ⟨_, hs⟩
  by_contra hle
  rw [not_lt] at hle
  set t : ℝ≥0 := (ContinuousPath.exitTime (ball x r) ω).toNNReal with ht
  have htcoe : (t : ℝ≥0∞) = ContinuousPath.exitTime (ball x r) ω :=
    ENNReal.coe_toNNReal hf.ne
  rw [← htcoe] at hle
  obtain ⟨⟨s, hst⟩, hsK⟩ :=
    (ContinuousPath.exitTime_le_iff_mem_hitsSetBy Kᶜ hK.isClosed.isOpen_compl t ω).mp hle
  have hsK' : ω s ∈ K := by simpa using hsK
  have hball : ω s ∈ closedBall x r := by
    rcases lt_or_eq_of_le (show s ≤ t from hst) with hlt | heq
    · apply ball_subset_closedBall
      apply ContinuousPath.mem_of_lt_exitTime
      rw [← htcoe]
      exact_mod_cast hlt
    · rw [heq]
      exact sphere_subset_closedBall hs
  exact Set.disjoint_left.mp hrK hball hsK'

/-- Strong Markov restart at the exit of `ball x r`: the avoidance event is almost surely invariant
under the shift by the exit time, so its probability is the mean of the avoidance probabilities
over the exit point. -/
private theorem planarBrownian_avoidEvent_eq_restart {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) {x : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hRU : ball x R ⊆ U)
    (hrK : Disjoint (closedBall x r) K) :
    planarBrownianMotion x (avoidEvent U K) =
      ∫⁻ ω, planarBrownianMotion
        (ω ((ContinuousPath.exitTime (ball x r) ω).toNNReal)) (avoidEvent U K)
        ∂(planarBrownianMotion x) := by
  let E : Set (ContinuousPath ℂ) := avoidEvent U K
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime (ball x r)
  have hτ := ContinuousPath.isStoppingTime_exitTime (ball x r) isOpen_ball
  have hE : MeasurableSet E := measurableSet_avoidEvent hU hK
  have hshift := ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ
  have hfin : ∀ᵐ ω ∂(planarBrownianMotion x), τ ω < ⊤ :=
    Section6.ae_planarBrownianMotion_exitTime_ball_lt_top x r
  have hcross := Section6.ae_planarBrownian_ball_crossing_unconditional (x := x) hr hrR
  have hKτ := ae_exitTime_ball_lt_exitTime_compl hK hr hrR hrK
  have hrestart :=
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
      x τ hτ univ (by simp)
  rw [← planarBrownianMotion_eq_continuousProcess] at hrestart
  simp only [univ_inter] at hrestart
  have hre : (planarBrownianMotion x).restrict {ω | (τ ω : WithTop ℝ≥0) < ⊤} =
      planarBrownianMotion x :=
    Measure.restrict_eq_self_of_ae_mem hfin
  change ((planarBrownianMotion x).restrict {ω | τ ω < ⊤}).map
      (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) =
    Kernel.comap planarBrownianMotion (fun ω => ω ((τ ω).untopD 0))
      (ContinuousPath.measurable_eval_untopD_stoppingTime τ hτ) ∘ₘ
        ((planarBrownianMotion x).restrict {ω | τ ω < ⊤}) at hrestart
  rw [hre] at hrestart
  have happ := congrArg (fun m : Measure (ContinuousPath ℂ) => m E) hrestart
  rw [Measure.map_apply hshift hE, Measure.bind_apply hE (Kernel.aemeasurable _)] at happ
  simp only [Kernel.comap_apply] at happ
  calc
    planarBrownianMotion x E = planarBrownianMotion x
        ((fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' E) := by
      apply measure_congr
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hfin, hcross, hKτ] with ω hf ⟨hc, _⟩ hKω
      have ht : (τ ω).untopD 0 < ContinuousPath.exitTime U ω := by
        simpa [τ, ENNReal.coe_toNNReal (ne_of_lt hf)] using
          hc.trans_le (ContinuousPath.exitTime_mono hRU ω)
      have htK : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime Kᶜ ω := by
        simpa [τ, ENNReal.coe_toNNReal (ne_of_lt hf)] using hKω
      constructor
      · exact fun hω => Section6.avoidance_after_shift ω _ ht hω
      · exact fun hω => Section6.exitTime_le_of_shift_exitTime_le (U := Kᶜ) (E := U) ω _ htK hω
    _ = ∫⁻ ω, planarBrownianMotion (ω ((τ ω).untopD 0)) E ∂(planarBrownianMotion x) := happ
    _ = _ := by rfl

/-- **Mean value identity for the avoidance event.** If `ball x R ⊆ U` and the closed disc
`closedBall x r` with `0 < r < R` misses the compact set `K`, the probability that Brownian motion
from `x` leaves `U` no later than it hits `K` is the average of the same probability over the
normalized circle measure on `sphere x r`. -/
theorem planarBrownian_avoidEvent_eq_disc_exit_mean {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) {x : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hRU : ball x R ⊆ U)
    (hrK : Disjoint (closedBall x r) K) :
    planarBrownianMotion x (avoidEvent U K) =
      ∫⁻ z, planarBrownianMotion z (avoidEvent U K) ∂(Section6.normalizedCircleMeasure x r) := by
  have hm : Measurable (fun z : ℂ => planarBrownianMotion z (avoidEvent U K)) :=
    Section6.measurable_avoidance_probability hU hK
  have ht := ContinuousPath.isStoppingTime_exitTime (ball x r) isOpen_ball
  have hstop : Measurable (fun ω : ContinuousPath ℂ =>
      ω ((ContinuousPath.exitTime (ball x r) ω).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime (ball x r)) ht
  have h := planarBrownian_avoidEvent_eq_restart hU hK hr hrR hRU hrK
  rw [← lintegral_map hm hstop, Section6.planarBrownian_disc_exit_distribution hr] at h
  exact h

/-- **Mean value property of the avoidance probability.** On a circle whose closed disc lies in
`O \ K`, the circle average of `avoidanceProb O K` equals its value at the centre. -/
theorem circleAverage_avoidanceProb {O K : Set ℂ} (hO : IsOpen O) (hK : IsCompact K) {x : ℂ}
    {r : ℝ} (hr : 0 < r) (hxr : closedBall x r ⊆ O \ K) :
    Real.circleAverage (avoidanceProb O K) x r = avoidanceProb O K x := by
  have hrK : Disjoint (closedBall x r) K :=
    Set.disjoint_left.2 fun z hz hzK => (hxr hz).2 hzK
  obtain ⟨R, hrR, hRO⟩ : ∃ R, r < R ∧ ball x R ⊆ O := by
    obtain ⟨ε, hε, hεO⟩ := (isCompact_closedBall x r).exists_thickening_subset_open hO
      (fun z hz => (hxr hz).1)
    rw [thickening_closedBall hε hr.le] at hεO
    exact ⟨ε + r, by linarith, hεO⟩
  have hf : Measurable (fun z : ℂ => planarBrownianMotion z (avoidEvent O K)) :=
    Section6.measurable_avoidance_probability hO hK
  have h1 := planarBrownian_avoidEvent_eq_disc_exit_mean hO hK hr hrR hRO hrK
  rw [Section6.lintegral_normalizedCircleMeasure x r hf] at h1
  set gθ : ℝ → ℝ := fun θ => avoidanceProb O K (circleMap x r θ)
  have hmeas : Measurable gθ :=
    (measurable_avoidanceProb hO hK).comp (continuous_circleMap x r).measurable
  have hint : IntegrableOn gθ (Ioo (-Real.pi) Real.pi) := by
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioo_lt_top.ne
      hmeas.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (avoidanceProb_nonneg O K _)]
    exact avoidanceProb_le_one O K _
  have hI : 0 ≤ ∫ θ in Ioo (-Real.pi) Real.pi, gθ θ :=
    setIntegral_nonneg measurableSet_Ioo fun θ _ => avoidanceProb_nonneg O K _
  have hl : ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      planarBrownianMotion (circleMap x r θ) (avoidEvent O K) =
      ENNReal.ofReal (∫ θ in Ioo (-Real.pi) Real.pi, gθ θ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun θ => avoidanceProb_nonneg O K _)]
    exact lintegral_congr fun θ => (ofReal_avoidanceProb O K _).symm
  rw [hl, ← ofReal_avoidanceProb O K x, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_eq_ofReal_iff (avoidanceProb_nonneg O K x) (by positivity)] at h1
  rw [Real.circleAverage_eq_integral_add (-Real.pi), h1]
  have heq := intervalIntegral.integral_comp_add_right gθ (a := 0) (b := 2 * Real.pi) (-Real.pi)
  have hp : 0 + -Real.pi = -Real.pi := by ring
  have hp' : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [hp, hp'] at heq
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo] at heq
  simp only [smul_eq_mul]
  rw [show (∫ θ in (0 : ℝ)..2 * Real.pi, avoidanceProb O K (circleMap x r (θ + -Real.pi))) =
    ∫ θ in Ioo (-Real.pi) Real.pi, gθ θ from heq]

end MatedCRT.BrownianBeurling
