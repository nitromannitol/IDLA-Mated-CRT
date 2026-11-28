import MatedCRT.FirstPass.Derived.BrownianBeurling.AvoidanceProbability
import HarmonicBalls.Proofs.Sec6.LogAnnulusExit
import HarmonicBalls.Proofs.Sec6.CompactHittingStopping

/-!
# Avoidance probabilities near a point of an exterior disc

Let `O` be open, `K` compact and `x₀ ∈ O`, and suppose that `x₀` lies on the boundary of a closed
disc `closedBall z δ ⊆ K`. Two facts about `avoidanceProb O K` follow.

* At a point of `O ∩ K` the avoidance probability vanishes, since Brownian motion started in `K`
  hits `K` at time zero but leaves `O` at a positive time.
* The avoidance probability tends to `0` at `x₀`. Near `x₀` one passes to a small closed disc
  `closedBall a r ⊆ K` with `closedBall a (2 * r) ⊆ O` and `x₀` on its boundary. The logarithmic
  function `log ‖· - a‖`, clipped to `[r, 2 * r]`, is harmonic on the annulus between the two
  circles, so its value at `x` is the expectation of its value at the exit point from the annulus.
  A path that leaves `O` no later than it hits `K` cannot exit the annulus through the inner
  circle, hence exits through the outer one, where the clipped logarithm is `log (2 * r)`. This
  gives `avoidanceProb O K x * log 2 ≤ log (‖x - a‖ / r)`, which tends to `0` as `x → x₀`.
-/

set_option autoImplicit false

open MeasureTheory Set MarkovProcess Metric
open _root_.HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.BrownianBeurling

/-- Brownian motion started at a point of `O ∩ K` avoids `K` before leaving `O` with probability
zero. -/
theorem avoidanceProb_eq_zero_of_mem {O K : Set ℂ} (hO : IsOpen O) {x : ℂ}
    (hxO : x ∈ O) (hxK : x ∈ K) : avoidanceProb O K x = 0 := by
  have hE : ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Kᶜ ω = 0 := by
    filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω hω
    refine le_antisymm ?_ bot_le
    simpa using ContinuousPath.exitTime_le_of_notMem Kᶜ ω 0 (by simp [hω, hxK])
  have h := Section6.avoidance_probability_eq_zero_of_instant_hit x hE
    (Section6.ae_planarBrownianMotion_exitTime_pos hO hxO)
  unfold avoidanceProb avoidEvent
  rw [h]
  rfl

/-- The logarithmic barrier estimate: if `closedBall a r ⊆ K`, `ball a (2 * r) ⊆ O` and
`r < ‖x - a‖ < 2 * r`, then `avoidanceProb O K x * log 2 ≤ log (‖x - a‖ / r)`. -/
theorem avoidanceProb_mul_log_two_le {O K : Set ℂ} (hO : IsOpen O) (hK : IsCompact K) {a : ℂ}
    {r : ℝ} (hr : 0 < r) (hKa : closedBall a r ⊆ K) (hOa : ball a (2 * r) ⊆ O) {x : ℂ}
    (hx1 : r < ‖x - a‖) (hx2 : ‖x - a‖ < 2 * r) :
    avoidanceProb O K x * Real.log 2 ≤ Real.log (‖x - a‖ / r) := by
  set A : Set ℂ := annulus a r (2 * r) with hAdef
  have hA : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAb : Bornology.IsBounded A := isBounded_ball.subset sdiff_subset
  have hxA : x ∈ A := by
    simp only [hAdef, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le,
      dist_eq_norm]
    exact ⟨hx2, hx1⟩
  have hrR : r ≤ 2 * r := by linarith
  have hEq := Section6.clippedAnnulusLog_eq_integral_exitTime a hr hrR hxA
  have hval : Section6.clippedAnnulusLog a r (2 * r) x = Real.log ‖x - a‖ := by
    simp only [Section6.clippedAnnulusLog, min_eq_right hx2.le, max_eq_right hx1.le]
  set μ := planarBrownianMotion x with hμ
  set f : ContinuousPath ℂ → ℝ := fun ω =>
    Section6.clippedAnnulusLog a r (2 * r) (ω ((ContinuousPath.exitTime A ω).toNNReal)) with hf
  have hTmeas : Measurable (fun ω : ContinuousPath ℂ => (ContinuousPath.exitTime A ω).toNNReal) :=
    ENNReal.measurable_toNNReal.comp (ContinuousPath.measurable_exitTime A hA)
  have hfmeas : Measurable f :=
    (Section6.continuous_clippedAnnulusLog a hr).measurable.comp
      (ContinuousPath.measurable_eval_of_measurable _ hTmeas)
  have hfint : Integrable f μ := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable
      (max |Real.log r| |Real.log (2 * r)|) (Filter.Eventually.of_forall fun ω => ?_)
    exact Section6.norm_clippedAnnulusLog_le a hr hrR _
  set E := avoidEvent O K with hE
  have hEmeas : MeasurableSet E := measurableSet_avoidEvent hO hK
  have hAO : A ⊆ O := sdiff_subset.trans hOa
  have hle : ∀ᵐ ω ∂μ, Real.log r + Real.log 2 * E.indicator (fun _ => (1 : ℝ)) ω ≤ f ω := by
    filter_upwards [Section6.ae_planarBrownian_exitTime_bounded_lt_top x hAb] with ω hfin
    by_cases hω : ω ∈ E
    · have hfin' : ContinuousPath.exitTime A ω ≠ ∞ := hfin.ne
      have hnot := Section6.coordinate_exitTime_notMem hA ω hfin'
      have hout : 2 * r ≤ ‖ω ((ContinuousPath.exitTime A ω).toNNReal) - a‖ := by
        by_contra hlt
        rw [not_le] at hlt
        have htc : (((ContinuousPath.exitTime A ω).toNNReal : ℝ≥0) : ℝ≥0∞) =
            ContinuousPath.exitTime A ω := ENNReal.coe_toNNReal hfin'
        have hinball : ω ((ContinuousPath.exitTime A ω).toNNReal) ∈ ball a (2 * r) := by
          rw [mem_ball, dist_eq_norm]; exact hlt
        have hcl : ω ((ContinuousPath.exitTime A ω).toNNReal) ∈ closedBall a r := by
          by_contra h
          exact hnot ⟨hinball, h⟩
        have hKle := ContinuousPath.exitTime_le_of_notMem Kᶜ ω
          ((ContinuousPath.exitTime A ω).toNNReal) (by simpa using hKa hcl)
        rw [htc] at hKle
        have hω' : ContinuousPath.exitTime O ω ≤ ContinuousPath.exitTime Kᶜ ω := hω
        have heq : ContinuousPath.exitTime O ω = ContinuousPath.exitTime A ω :=
          le_antisymm (hω'.trans hKle) (ContinuousPath.exitTime_mono hAO ω)
        have hOfin : ContinuousPath.exitTime O ω ≠ ∞ := heq ▸ hfin'
        have hnotO := Section6.coordinate_exitTime_notMem hO ω hOfin
        rw [heq] at hnotO
        exact hnotO (hOa hinball)
      have hfω : f ω = Real.log 2 + Real.log r := by
        simp only [hf, Section6.clippedAnnulusLog, min_eq_left hout, max_eq_right hrR]
        rw [Real.log_mul two_ne_zero hr.ne']
      rw [Set.indicator_of_mem hω, hfω]
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact Real.log_le_log hr (le_max_left _ _)
  have hgint : Integrable
      (fun ω => Real.log r + Real.log 2 * E.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).indicator hEmeas).const_mul _)
  have hint := integral_mono_ae hgint hfint hle
  rw [integral_add (integrable_const _) (((integrable_const (1 : ℝ)).indicator hEmeas).const_mul _),
    integral_const, integral_const_mul, integral_indicator_const _ hEmeas, ← hEq, hval] at hint
  have hprob : avoidanceProb O K x = μ.real E := rfl
  rw [hprob]
  have hlog : Real.log (‖x - a‖ / r) = Real.log ‖x - a‖ - Real.log r :=
    Real.log_div (by linarith) hr.ne'
  simp only [smul_eq_mul, mul_one, probReal_univ] at hint
  rw [hlog]
  linarith

/-- If `x₀ ∈ O` lies on the boundary of a closed disc `closedBall z δ ⊆ K`, then the avoidance
probability of `K` before leaving `O` is arbitrarily small near `x₀`. -/
theorem exists_avoidanceProb_le_of_exterior_disc {O K : Set ℂ} (hO : IsOpen O) (hK : IsCompact K)
    {x₀ z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hx₀ : x₀ ∈ O) (hz : dist x₀ z = δ)
    (hdisc : closedBall z δ ⊆ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℂ, dist x x₀ < η → avoidanceProb O K x ≤ ε := by
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hO x₀ hx₀
  set r : ℝ := min δ (ρ₀ / 4) with hr
  have hr0 : 0 < r := lt_min hδ (by linarith)
  have hrδ : r ≤ δ := min_le_left _ _
  have hrρ : r ≤ ρ₀ / 4 := min_le_right _ _
  set s : ℝ := r / δ with hs
  have hs0 : 0 < s := div_pos hr0 hδ
  have hs1 : s ≤ 1 := (div_le_one hδ).mpr hrδ
  set a : ℂ := x₀ + s • (z - x₀) with ha
  have hzx : ‖z - x₀‖ = δ := by rw [← dist_eq_norm, dist_comm]; exact hz
  have hax : ‖a - x₀‖ = r := by
    have : a - x₀ = s • (z - x₀) := by rw [ha]; abel
    rw [this, norm_smul, hzx, Real.norm_of_nonneg hs0.le, hs]
    field_simp
  have haz : ‖a - z‖ = δ - r := by
    have : a - z = (s - 1) • (z - x₀) := by rw [ha]; module
    rw [this, norm_smul, hzx, Real.norm_eq_abs, abs_of_nonpos (by linarith), hs]
    field_simp
    ring
  have hKa : closedBall a r ⊆ K := by
    refine Subset.trans (fun y hy => ?_) hdisc
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    calc ‖y - z‖ = ‖(y - a) + (a - z)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - a‖ + ‖a - z‖ := norm_add_le _ _
      _ ≤ δ := by rw [haz]; linarith
  have hOa : ball a (2 * r) ⊆ O := by
    refine Subset.trans (fun y hy => ?_) hball
    rw [mem_ball, dist_eq_norm] at hy ⊢
    calc ‖y - x₀‖ = ‖(y - a) + (a - x₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - a‖ + ‖a - x₀‖ := norm_add_le _ _
      _ < ρ₀ := by rw [hax]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨min r (ε * Real.log 2 * r), lt_min hr0 (by positivity), fun x hx => ?_⟩
  have hxr : dist x x₀ < r := hx.trans_le (min_le_left _ _)
  have hxη : dist x x₀ < ε * Real.log 2 * r := hx.trans_le (min_le_right _ _)
  rw [dist_eq_norm] at hxr hxη
  by_cases hin : ‖x - a‖ ≤ r
  · have hxK : x ∈ K := hKa (by rw [mem_closedBall, dist_eq_norm]; exact hin)
    have hxO : x ∈ O := hOa (by rw [mem_ball, dist_eq_norm]; linarith)
    rw [avoidanceProb_eq_zero_of_mem hO hxO hxK]
    exact hε.le
  · rw [not_le] at hin
    have hupper : ‖x - a‖ < r + ε * Real.log 2 * r := by
      calc ‖x - a‖ = ‖(x - x₀) + (x₀ - a)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖x - x₀‖ + ‖x₀ - a‖ := norm_add_le _ _
        _ < r + ε * Real.log 2 * r := by rw [norm_sub_rev x₀ a, hax]; linarith
    have hx2 : ‖x - a‖ < 2 * r := by
      have : ‖x - a‖ < r + r := by
        calc ‖x - a‖ = ‖(x - x₀) + (x₀ - a)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖x - x₀‖ + ‖x₀ - a‖ := norm_add_le _ _
          _ < r + r := by rw [norm_sub_rev x₀ a, hax]; linarith
      linarith
    have hkey := avoidanceProb_mul_log_two_le hO hK hr0 hKa hOa hin hx2
    have hlog := Real.log_le_sub_one_of_pos (div_pos (hr0.trans hin) hr0)
    have hdiv : ‖x - a‖ / r - 1 < ε * Real.log 2 := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hr0]
      linarith
    exact le_of_mul_le_mul_right (by linarith) hlog2

end MatedCRT.BrownianBeurling
