import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockAgree
import MatedCRT.Proofs.Sec3.KilledOccupation.RegClockFun
import MatedCRT.Proofs.Sec3.KilledOccupation.ConeClockTransfer
import MatedCRT.Proofs.Sec3.KilledOccupation.ClockExitLIntegral
import MatedCRT.Proofs.Sec3.KilledOccupation.BaseClockProofCont

/-!
# Regularized clocks against the approximating LQG clocks (Appendix B of arXiv:2211.04891)

This file collects the pointwise and measure-theoretic facts that compare the regularized clock
`regClockFun` built from circle averages (the clock of the Duplantier-Sheffield circle-average field)
with the approximating LQG clock `HarmonicBalls.lqgClockApprox` of the quantum cone field.

* `clockGapFun` is the quenched gap between the regularized clocks at two scales, taken as a supremum over
  rational times, so that it is measurable in the path variable;
* `measurable_clockGapFun` is its measurability;
* `ennDist_ofReal_le` compares `ENNReal.ofReal` values in the extended distance.

Terminology: Duplantier-Sheffield (circle averages and the LQG measure), Berestycki-Powell (LQG clocks),
Armitage-Gardiner (potential theory, harmonic balls).
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The quenched gap between the regularized clocks at the scales `ε` and `ε'`: the supremum over rational
times of the extended distance of the two clocks. Taking the supremum over `ℚ≥0` makes it a countable
supremum of measurable functions of the path. -/
noncomputable def clockGapFun (γ : ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (ε ε' : ℝ)
    (x : (UnitDiskCircleIndex → ℝ) × ContinuousPath ℂ) : ℝ≥0∞ :=
  ⨆ q : ℚ≥0, ennDist (regClockFun γ ε x.1 σ x.2 (q : ℝ≥0)) (regClockFun γ ε' x.1 σ x.2 (q : ℝ≥0))

/-- The gap `clockGapFun` is measurable whenever the exit time `σ` is measurable. -/
theorem measurable_clockGapFun (γ : ℝ) (σ : ContinuousPath ℂ → ℝ≥0) (hσ : Measurable σ) (ε ε' : ℝ) :
    Measurable (clockGapFun γ σ ε ε') :=
  Measurable.iSup fun q =>
    ((measurable_regClockFun γ ε σ hσ (q : ℝ≥0)).sub (measurable_regClockFun γ ε' σ hσ (q : ℝ≥0))).add
      ((measurable_regClockFun γ ε' σ hσ (q : ℝ≥0)).sub (measurable_regClockFun γ ε σ hσ (q : ℝ≥0)))

/-- The extended distance of two `ENNReal.ofReal` values is at most the `ENNReal.ofReal` of their difference. -/
lemma ennDist_ofReal_le (a b : ℝ) :
    ennDist (ENNReal.ofReal a) (ENNReal.ofReal b) ≤ ENNReal.ofReal |a - b| := by
  have key : ∀ x y : ℝ, x ≤ y → ENNReal.ofReal y - ENNReal.ofReal x ≤ ENNReal.ofReal |x - y| := by
    intro x y hxy
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hxy), tsub_le_iff_right]
    calc ENNReal.ofReal y = ENNReal.ofReal (y - x + x) := congrArg ENNReal.ofReal (sub_add_cancel y x).symm
      _ ≤ ENNReal.ofReal (y - x) + ENNReal.ofReal x := ENNReal.ofReal_add_le
  unfold ennDist
  rcases le_total a b with hab | hab
  · rw [tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal hab), zero_add]
    exact key a b hab
  · rw [tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal hab), add_zero, abs_sub_comm a b]
    exact key b a hab

/-- On the cone, the regularized clock of the field `h` (its circle averages at scale `ε` read on the unit disk),
run up to the exit time of the ball `ball z r`, equals the extended nonnegative real `ENNReal.ofReal` of the
approximating LQG clock `HarmonicBalls.lqgClockApprox γ h ε` at the time `min s (exitNN z r b)`. The circle averages
of `coneShift γ h` are `h` itself (`fieldCircleAverage_coneShift`); the approximation scale `ε` stays inside the unit
disk because the ball `ball z r` lies in `ball 0 ρ` with `ρ + ε < 1`. -/
lemma regClockFun_eq_ofReal_lqgClockApprox {γ ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < 1 - ρ) {h : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) {z y : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ball z r ⊆ ball 0 ρ) (hy : y ∈ ball z r) {b : ContinuousPath ℂ} (hb0 : b 0 = y) (s : ℝ≥0) :
    regClockFun γ ε (fun q : UnitDiskCircleIndex => h q.1.1 q.1.2) (exitNN z r) b s =
      ENNReal.ofReal (HarmonicBalls.lqgClockApprox γ h ε b (min s (exitNN z r b))) := by
  -- (a) the family is the family of circle averages of the cone shift
  have hfam : (fun q : UnitDiskCircleIndex => h q.1.1 q.1.2) =
      fun q : UnitDiskCircleIndex => HarmonicBalls.fieldCircleAverage γ (coneShift γ h) q.1.1 q.1.2 := by
    funext q
    rw [fieldCircleAverage_coneShift]
  -- (b) the index condition: the path stays in the closed ball, which lies in `ball 0 ρ`
  have hρpos : 0 < ρ := lt_of_le_of_lt dist_nonneg (mem_ball.1 (hball hy))
  have hcl : closedBall z r ⊆ closedBall 0 ρ := by
    rw [← closure_ball z hr.ne', ← closure_ball (0 : ℂ) hρpos.ne']
    exact closure_mono hball
  have hb : ∀ u ∈ Set.Icc (0 : ℝ≥0) (min s (exitNN z r b)), (ε, b u) ∈ UnitDiskCircleIndex := by
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ≥0) (HarmonicBalls.pathExitTime (ball z r) b).toNNReal :=
      ⟨hu.1, le_trans hu.2 (min_le_right _ _)⟩
    have hmem : b u ∈ closedBall z r := path_mem_closedBall_of_start hy hb0 hu'
    have hsub : closedBall (b u) ε ⊆ ball (0 : ℂ) 1 := by
      intro w hw
      have h1 : ‖b u‖ ≤ ρ := mem_closedBall_zero_iff.1 (hcl hmem)
      have h2 : dist w (b u) ≤ ε := hw
      have h3 : dist w 0 ≤ dist w (b u) + dist (b u) 0 := dist_triangle _ _ _
      simp only [dist_zero_right] at h3
      rw [mem_ball_zero_iff]
      linarith
    exact ⟨hε, hsub⟩
  -- (c) the regularized clock with the family of circle averages of the cone shift equals `regClock`
  have hψ : Continuous fun q : UnitDiskCircleIndex =>
      HarmonicBalls.fieldCircleAverage γ (coneShift γ h) q.1.1 q.1.2 := by
    have hsub : (UnitDiskCircleIndex : Set (ℝ × ℂ)) ⊆ Ioi 0 ×ˢ univ := fun q hq => ⟨hq.1, mem_univ _⟩
    simp only [fieldCircleAverage_coneShift]
    exact continuousOn_iff_continuous_domRestrict.1 (hc.mono hsub)
  have hreg := regClockFun_eq_regClock γ ε (coneShift γ h) hψ (exitNN z r) b s hb
  -- (d) the clock `regClock` is read up to `min s (σ b)` and equals the ofReal of the LQG clock approximation
  have hx : Continuous fun x : ℂ => h ε x := by
    have h1 : Continuous fun x : ℂ => ((ε, x) : ℝ × ℂ) := continuous_const.prodMk continuous_id
    exact hc.comp_continuous h1 fun x => ⟨hε, mem_univ _⟩
  have hcs : Continuous fun x : ℂ => coneShift γ h ε x := continuous_coneShift hε hx
  have hfinal := regClock_coneShift_eq_ofReal hε hcs b (exitNN z r b) (min s (exitNN z r b)) (min_le_right _ _)
  have hmin : regClock γ ε (coneShift γ h) (exitNN z r b) ⇑b s =
      regClock γ ε (coneShift γ h) (exitNN z r b) ⇑b (min s (exitNN z r b)) := by
    unfold regClock
    rw [min_eq_left (min_le_right _ _)]
  rw [hfam, hreg, hmin, hfinal]

end MatedCRT.KilledOccupation
