import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole
import HarmonicBalls.Proofs.Potential.GreenBall
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable
import MarkovProcess.Path.ExitTimeShift
import MarkovProcess.Examples.BrownianMotion
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockProof

/-!
# Textbook binders of the base occupation identity (Appendix B)

`baseOccupationIdentity_of_GMC` (BaseClockProof.lean) takes five measurability and integrability binders about the
exit time `pathExitTime (ball z r)` of planar Brownian motion and the Green function `greenFunction (ball z r) y` of the
ball. This file discharges them, so that `baseOccupationIdentity_of_GMC'` no longer has them:

* the exit time is Borel on the path space (MarkovProcess `ContinuousPath.measurable_exitTime`);
* the exit time has finite expectation from every starting point: the event that the path stays in the ball up to time
  `n` lies in `n` independent unit-time increment events of the real part (Brownian increments are independent Gaussians,
  `brownianMotion_map_increments`), so `P^y(τ > n) ≤ q^n` with `q = P(N(0,1) < 2r) < 1`, and `E^y τ ≤ ∑ q^n` (the
  expected exit time of a bounded domain is finite; Armitage–Gardiner, Dynkin's formula);
* the Green function `G_{B(z,r)}(y,·)` is Borel and integrable on the ball (Armitage–Gardiner §4.1; the disc
  Green function is `(2π)⁻¹ log(|R² - x̄y| / (R|x - y|))` up to translation, Harmonic-Balls `integrable_greenFunction_ball_left`).
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls ProbabilityTheory
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The exit time of an open set is Borel on the continuous-path space (`MarkovProcess.ContinuousPath.measurable_exitTime`). -/
theorem measurable_pathExitTime_ball (z : ℂ) (r : ℝ) :
    Measurable fun b : ContinuousPath ℂ => pathExitTime (ball z r) b :=
  ContinuousPath.measurable_exitTime (ball z r) isOpen_ball

/-- The Green function of a ball, as a function of its second variable, is Borel (`measurable_greenFunction`). -/
theorem measurable_greenFunction_ball_left (z y : ℂ) (r : ℝ) :
    Measurable fun x => greenFunction (ball z r) y x :=
  measurable_greenFunction isOpen_ball y

/-- The Green function of a ball with a pole `y` in the ball is integrable over the ball. The centred disc case is
`integrable_greenFunction_ball_left` (Harmonic-Balls, Proofs/Sec3/Basic.lean); the translation `ball z r` ↦ `ball 0 r` is
`greenFunction_ball_translate`, the symmetry is `greenFunction_ball_comm`, and the Lebesgue volume growth is
`volumeGrowth_volume`. -/
theorem integrableOn_greenFunction_ball (z y : ℂ) (r : ℝ) (hy : y ∈ ball z r) :
    IntegrableOn (fun x => greenFunction (ball z r) y x) (ball z r) := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (mem_ball.1 hy)
  have hc : y - z ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall_zero_iff, ← dist_eq_norm]
    exact (mem_ball.1 hy).le
  have h1 : IntegrableOn (fun w => greenFunction (ball 0 r) w (y - z)) (ball 0 r) :=
    integrable_greenFunction_ball_left hr (volumeGrowth_volume r) hc
  have hpre : (fun x : ℂ => x - z) ⁻¹' ball (0 : ℂ) r = ball z r := by
    ext x
    simp [mem_ball, dist_eq_norm]
  have heq : (fun x => greenFunction (ball z r) y x)
      = (fun w => greenFunction (ball 0 r) w (y - z)) ∘ (fun x : ℂ => x - z) := by
    funext x
    simp only [Function.comp]
    rw [greenFunction_ball_translate, greenFunction_ball_comm r (y - z) (x - z)]
  have hmp : MeasurePreserving (fun x : ℂ => x - z) volume volume := measurePreserving_sub_right volume z
  have hme : MeasurableEmbedding (fun x : ℂ => x - z) := (Homeomorph.subRight z).measurableEmbedding
  have key : IntegrableOn ((fun w => greenFunction (ball 0 r) w (y - z)) ∘ (fun x : ℂ => x - z)) (ball z r) := by
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage hme).2 h1
  rw [heq]
  exact key

/-- A point of the path before its exit time lies in the open set. -/
theorem mem_ball_of_lt_pathExitTime (z : ℂ) (r : ℝ) (b : ContinuousPath ℂ) (s : ℝ≥0) {n : ℕ}
    (hs : s ≤ (n : ℝ≥0)) (hb : (n : ℝ≥0∞) < pathExitTime (ball z r) b) : b s ∈ ball z r := by
  refine ContinuousPath.mem_of_lt_exitTime (ball z r) b s ?_
  exact lt_of_le_of_lt (by exact_mod_cast hs) hb

/-- The unit-time grid `0, 1, …, n` in `ℝ≥0`. -/
noncomputable def unitTimes (n : ℕ) : Fin (n + 1) → ℝ≥0 := fun i => ((i : ℕ) : ℝ≥0)

theorem unitTimes_monotone (n : ℕ) : Monotone (unitTimes n) := fun _ _ hij =>
  Nat.cast_le.2 (Fin.val_fin_le.2 hij)

theorem unitTimes_succ_sub (n : ℕ) (i : Fin n) : unitTimes n i.succ - unitTimes n i.castSucc = 1 := by
  simp [unitTimes]

/-- The `n` unit-time increments of a real path. -/
noncomputable def unitIncrements (n : ℕ) (ω : ContinuousPath ℝ) : Fin n → ℝ :=
  fun i => ω (unitTimes n i.succ) - ω (unitTimes n i.castSucc)

theorem measurable_unitIncrements (n : ℕ) : Measurable (unitIncrements n) := by
  refine Measurable.of_eval fun i => ?_
  exact (ContinuousPath.measurable_coordinateProcess _).sub (ContinuousPath.measurable_coordinateProcess _)

/-- The `n` unit-time increments of standard real Brownian motion are i.i.d. `N(0,1)`, so the probability that all
of them lie below `c` is `P(N(0,1) < c)^n`. -/
theorem brownianMotion_unitIncrements_pi (x : ℝ) (n : ℕ) (c : ℝ) :
    brownianMotion x (unitIncrements n ⁻¹' (Set.univ.pi fun _ : Fin n => Iio c))
      = (gaussianReal 0 1 (Iio c)) ^ n := by
  rw [← Measure.map_apply (measurable_unitIncrements n) (MeasurableSet.univ_pi fun _ => measurableSet_Iio)]
  have hmap : (brownianMotion x).map (unitIncrements n) = Measure.pi fun _ : Fin n => gaussianReal 0 1 := by
    have h := brownianMotion_map_increments (unitTimes_monotone n) x
    have hfam : (fun i : Fin n => gaussianReal 0 (unitTimes n i.succ - unitTimes n i.castSucc))
        = fun _ : Fin n => gaussianReal 0 1 := funext fun i => by rw [unitTimes_succ_sub]
    rw [hfam] at h
    exact h
  rw [hmap, Measure.pi_pi]
  simp [Finset.prod_const]

/-- `P(N(0,1) < c) < 1`, since `N(0,1)` charges every half-line. -/
theorem gaussianReal_Iio_lt_one (c : ℝ) : gaussianReal 0 1 (Iio c) < 1 := by
  have hpos : 0 < gaussianReal 0 1 (Ioi c) := by
    rw [gaussianReal_apply 0 one_ne_zero, setLIntegral_pos_iff (measurable_gaussianPDF 0 1)]
    have hsupp : Function.support (gaussianPDF 0 1) = univ :=
      Set.eq_univ_of_forall fun x => (gaussianPDF_pos 0 one_ne_zero x).ne'
    rw [hsupp, univ_inter, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  have hcompl : gaussianReal 0 1 (Ici c) = 1 - gaussianReal 0 1 (Iio c) := by
    rw [← Set.compl_Iio, prob_compl_eq_one_sub measurableSet_Iio]
  have hIci : 0 < gaussianReal 0 1 (Ici c) := lt_of_lt_of_le hpos (measure_mono Ioi_subset_Ici_self)
  rw [hcompl] at hIci
  exact tsub_pos_iff_lt.1 hIci

/-- The planar stay estimate: the probability that the path started at `y` has not left the ball before time `n` is at
most `P(N(0,1) < 2r)^n`. Proof: on `{τ > n}` the real parts of consecutive unit-time points differ by less than `2r`
(both points lie in the ball of radius `r`), and the real part of planar Brownian motion is a real Brownian motion. -/
theorem planarBrownianMotion_exit_gt_le (y z : ℂ) (r : ℝ) (n : ℕ) :
    planarBrownianMotion y {b : ContinuousPath ℂ | (n : ℝ≥0∞) < pathExitTime (ball z r) b}
      ≤ (gaussianReal 0 1 (Iio (2 * r))) ^ n := by
  have hmeasF : Measurable (fun b : ContinuousPath ℂ => (reImPath b).1) :=
    measurable_fst.comp measurable_reImPath
  have hEmeas : MeasurableSet (unitIncrements n ⁻¹' (Set.univ.pi fun _ : Fin n => Iio (2 * r))) :=
    measurable_unitIncrements n (MeasurableSet.univ_pi fun _ => measurableSet_Iio)
  have hsub : {b : ContinuousPath ℂ | (n : ℝ≥0∞) < pathExitTime (ball z r) b}
      ⊆ (fun b : ContinuousPath ℂ => (reImPath b).1) ⁻¹'
          (unitIncrements n ⁻¹' (Set.univ.pi fun _ : Fin n => Iio (2 * r))) := by
    intro b hb
    simp only [Set.mem_preimage, Set.mem_univ_pi, unitIncrements, Set.mem_Iio]
    intro i
    have hs1 : unitTimes n i.succ ≤ (n : ℝ≥0) := by
      simp only [unitTimes, Fin.val_succ]
      exact_mod_cast Nat.lt_iff_add_one_le.1 i.isLt
    have hs0 : unitTimes n i.castSucc ≤ (n : ℝ≥0) := by
      simp only [unitTimes, Fin.val_castSucc]
      exact_mod_cast i.isLt.le
    have hm1 := mem_ball.1 (mem_ball_of_lt_pathExitTime z r b _ hs1 hb)
    have hm0 := mem_ball.1 (mem_ball_of_lt_pathExitTime z r b _ hs0 hb)
    rw [reImPath_fst_apply, reImPath_fst_apply, ← Complex.sub_re]
    have hre : (b (unitTimes n i.succ) - b (unitTimes n i.castSucc)).re
        ≤ dist (b (unitTimes n i.succ)) (b (unitTimes n i.castSucc)) := by
      rw [dist_eq_norm]
      exact Complex.re_le_norm _
    have htri := dist_triangle (b (unitTimes n i.succ)) z (b (unitTimes n i.castSucc))
    rw [dist_comm z] at htri
    linarith
  calc planarBrownianMotion y {b : ContinuousPath ℂ | (n : ℝ≥0∞) < pathExitTime (ball z r) b}
      ≤ planarBrownianMotion y ((fun b : ContinuousPath ℂ => (reImPath b).1) ⁻¹'
          (unitIncrements n ⁻¹' (Set.univ.pi fun _ : Fin n => Iio (2 * r)))) := measure_mono hsub
    _ = (planarBrownianMotion y).map (fun b : ContinuousPath ℂ => (reImPath b).1)
          (unitIncrements n ⁻¹' (Set.univ.pi fun _ : Fin n => Iio (2 * r))) :=
        (Measure.map_apply hmeasF hEmeas).symm
    _ = brownianMotion y.re (unitIncrements n ⁻¹' (Set.univ.pi fun _ : Fin n => Iio (2 * r))) := by
        rw [planarBrownianMotion_map_re]
    _ = (gaussianReal 0 1 (Iio (2 * r))) ^ n := brownianMotion_unitIncrements_pi y.re n (2 * r)

/-- Pointwise: a value `x : ℝ≥0∞` is at most the number of naturals `n` with `n < x`, i.e. `x ≤ ∑ₙ 1_{n < x}`. -/
theorem le_tsum_indicator_natCast_lt (x : ℝ≥0∞) :
    x ≤ ∑' n : ℕ, (if (n : ℝ≥0∞) < x then (1 : ℝ≥0∞) else 0) := by
  induction x using ENNReal.recTopCoe with
  | top =>
    have h : ∀ n : ℕ, (if (n : ℝ≥0∞) < ⊤ then (1 : ℝ≥0∞) else 0) = 1 := fun n => by
      simp [ENNReal.natCast_lt_top n]
    simp only [h]
    exact le_of_eq (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe a =>
    calc (a : ℝ≥0∞) ≤ ((⌈a⌉₊ : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.le_ceil a
      _ = ∑ _n ∈ Finset.range ⌈a⌉₊, (1 : ℝ≥0∞) := by simp
      _ = ∑ n ∈ Finset.range ⌈a⌉₊, (if (n : ℝ≥0∞) < (a : ℝ≥0∞) then (1 : ℝ≥0∞) else 0) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have hlt : (n : ℝ≥0) < a := Nat.lt_ceil.1 (Finset.mem_range.1 hn)
          have h' : (n : ℝ≥0∞) < (a : ℝ≥0∞) := by exact_mod_cast hlt
          simp [h']
      _ ≤ ∑' n : ℕ, (if (n : ℝ≥0∞) < (a : ℝ≥0∞) then (1 : ℝ≥0∞) else 0) :=
          ENNReal.sum_le_tsum _

/-- The expected exit time of the ball under planar Brownian motion is finite:
`∫⁻ τ dP^y = ∑ₙ P^y(τ > n) ≤ ∑ₙ P(N(0,1) < 2r)^n < ∞`. -/
theorem lintegral_pathExitTime_planar_ne_top (y z : ℂ) (r : ℝ) :
    ∫⁻ b, pathExitTime (ball z r) b ∂planarBrownianMotion y ≠ ⊤ := by
  have hτ := measurable_pathExitTime_ball z r
  have hmeas : ∀ n : ℕ, Measurable fun b : ContinuousPath ℂ =>
      (if (n : ℝ≥0∞) < pathExitTime (ball z r) b then (1 : ℝ≥0∞) else 0) := fun n =>
    Measurable.ite (measurableSet_lt measurable_const hτ) measurable_const measurable_const
  have hle : ∫⁻ b, pathExitTime (ball z r) b ∂planarBrownianMotion y
      ≤ ∑' n : ℕ, ∫⁻ b, (if (n : ℝ≥0∞) < pathExitTime (ball z r) b then (1 : ℝ≥0∞) else 0)
          ∂planarBrownianMotion y := by
    rw [← lintegral_tsum fun n => (hmeas n).aemeasurable]
    exact lintegral_mono fun b => le_tsum_indicator_natCast_lt _
  have hval : ∀ n : ℕ, ∫⁻ b, (if (n : ℝ≥0∞) < pathExitTime (ball z r) b then (1 : ℝ≥0∞) else 0)
      ∂planarBrownianMotion y
      = planarBrownianMotion y {b : ContinuousPath ℂ | (n : ℝ≥0∞) < pathExitTime (ball z r) b} := fun n => by
    have hs : MeasurableSet {b : ContinuousPath ℂ | (n : ℝ≥0∞) < pathExitTime (ball z r) b} :=
      measurableSet_lt measurable_const hτ
    rw [← lintegral_indicator_one hs]
    simp [Set.indicator_apply]
  have hsum : ∑' n : ℕ, ∫⁻ b, (if (n : ℝ≥0∞) < pathExitTime (ball z r) b then (1 : ℝ≥0∞) else 0)
      ∂planarBrownianMotion y ≤ ∑' n : ℕ, (gaussianReal 0 1 (Iio (2 * r))) ^ n :=
    ENNReal.tsum_le_tsum fun n => (hval n).le.trans (planarBrownianMotion_exit_gt_le y z r n)
  have hg : gaussianReal 0 1 (Iio (2 * r)) < 1 := gaussianReal_Iio_lt_one _
  have hfin : ∑' n : ℕ, (gaussianReal 0 1 (Iio (2 * r))) ^ n < ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_lt_top.2 (tsub_pos_iff_lt.2 hg)
  exact ne_of_lt (lt_of_le_of_lt hle (lt_of_le_of_lt hsum hfin))

/-- **(b) Integrability of the exit time** under planar Brownian motion from `y`: `τ_{B(z,r)}` has finite mean. -/
theorem integrable_pathExitTime_toReal_planar (y z : ℂ) (r : ℝ) :
    Integrable (fun b : ContinuousPath ℂ => (pathExitTime (ball z r) b).toReal) (planarBrownianMotion y) :=
  integrable_toReal_of_lintegral_ne_top (measurable_pathExitTime_ball z r).aemeasurable
    (lintegral_pathExitTime_planar_ne_top y z r)

/-- **(b) Finiteness of the truncated-real exit time integral** `∫⁻ σ dP^y ≠ ⊤` with `σ = (τ).toNNReal`. -/
theorem lintegral_toNNReal_pathExitTime_planar_ne_top (y z : ℂ) (r : ℝ) :
    ∫⁻ b, ((pathExitTime (ball z r) b).toNNReal : ℝ≥0∞) ∂planarBrownianMotion y ≠ ⊤ :=
  ne_top_of_le_ne_top (lintegral_pathExitTime_planar_ne_top y z r)
    (lintegral_mono fun _ => ENNReal.coe_toNNReal_le_self)

/-- **Base occupation identity with its textbook binders discharged.** `baseOccupationIdentity_of_GMC`
(BaseClockProof.lean) with the exit-time binders `hτ`, `hτmeas`, `hσint` and the Green-function binders `hGmeas`,
`hGint` proved in this file; the remaining binders are those of `baseOccupationIdentity_of_GMC`. -/
theorem baseOccupationIdentity_of_GMC' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (r : ℝ) {y : ℂ} (hy : y ∈ ball z r)
    (hDB : ball z r ⊆ ball 0 1)
    (hS0 : KilledBrownianOccupationOnBall z r)
    (hw : ∀ k, Measurable fun p : Ω × ℂ => circleWeight γ hcirc p.1 k p.2)
    (hVar : ∀ᶠ k in atTop, ∀ x ∈ ball z r, ∫⁻ ω, ENNReal.ofReal (circleWeight γ hcirc ω k x) ∂P = 1)
    (ν : Ω → Measure ℂ) (dA : Ω → ContinuousPath ℂ → Measure ℝ≥0)
    (hνmeas : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → Measurable fun ω => ∫⁻ x, ρ x ∂(ν ω))
    (hconvB1 : ∀ ρ : ℂ → ℝ≥0∞, Measurable ρ → (∃ N : ℝ≥0∞, N ≠ ⊤ ∧ ∀ x, ρ x ≤ N) →
      (∀ x ∉ ball 0 1, ρ x = 0) →
      Tendsto (fun k => ∫⁻ ω, ediffE (∫⁻ x, ρ x ∂(circleMeasure γ hcirc ω k)) (∫⁻ x, ρ x ∂(ν ω)) ∂P)
        atTop (𝓝 0))
    (hLjoint : ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun p : Ω × ContinuousPath ℂ => limitClockFun dA z r p.1 p.2 q)
    (hmeasKernel : ∀ᵐ ω ∂P, ∀ q : ℂ → ℝ≥0∞, Measurable q →
      Measurable fun b : ContinuousPath ℂ => ∫⁻ u in Icc (0 : ℝ≥0) (pathExitTime (ball z r) b).toNNReal,
        q (b u) ∂(dA ω b))
    (hLpath : ∀ q : ℂ → ℝ≥0∞, Measurable q → (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ x, q x ≤ M) →
      ∀ᵐ b ∂planarBrownianMotion y, Tendsto (fun k => clockGapMean P γ hcirc dA z r k q b) atTop (𝓝 0)) :
    BaseOccupationIdentity P (planarBrownianMotion y) (ball z r) (greenFunction (ball z r) y) ν dA
      (fun b => (pathExitTime (ball z r) b).toNNReal) :=
  baseOccupationIdentity_of_GMC P γ hcirc z r hy hDB hS0
    (integrable_pathExitTime_toReal_planar y z r) (measurable_pathExitTime_ball z r)
    (measurable_greenFunction_ball_left z y r) (integrableOn_greenFunction_ball z y r hy)
    hw hVar ν dA hνmeas hconvB1 hLjoint hmeasKernel hLpath
    (lintegral_toNNReal_pathExitTime_planar_ne_top y z r)

end MatedCRT.KilledOccupation
