import MatedCRT.FirstPass.Derived.WalkClassLevyProkhorovOfGood
import MatedCRT.FirstPass.Derived.ReversibilityPairingDiscrete

/-!
# The interpolated quenched walk law at a point, on the uniform-start good event

On the uniform-start good event (`MatedCRT.UniformStartGood.goodG`, with finite exits), for a point `z` and
cell mesh `d` around `z`, every cell of the interpolation with positive weight at `z` has its vertex within
`d + ε` of `z` (`dist_vertexPoint_lt_of_interpWeight_ne_zero`).  Hence the stopped class law of the interpolated
quenched walk at `z` is within Lévy–Prokhorov distance `κ + κ₂` of the stopped class law of planar Brownian
motion from `z` (`levyProkhorovDist_interpWalkLaw_stoppedExitCurve_le`), where `κ` is the tolerance of the good
event and `κ₂` bounds the variation of the Brownian class law over the ball of radius `d + ε` around `z`.
-/

namespace MatedCRT.InterpClassClose

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open _root_.HarmonicBalls
open scoped NNReal ENNReal
open MatedCRT.StopAtExitLevyProkhorov MatedCRT.FirstPass.Derived

/-- A cell with positive interpolation weight at `z` has its vertex within `d + ε` of `z`, when the cells
meeting `B_{ρ+1}` have diameter at most `d` and `‖z‖ + ε ≤ ρ`. -/
theorem dist_vertexPoint_lt_of_interpWeight_ne_zero {η : ℝ → ℂ} (hη : Continuous η) {ε ρ d : ℝ}
    (hε : 0 ≤ ε) (hd0 : 0 ≤ d) (hmesh : maxCellDiam ε η ρ ≤ ENNReal.ofReal d) {z : ℂ}
    (hz : ‖z‖ + ε ≤ ρ) {k : ℤ} (hk : interpWeight (fun k => cell ε η k) ε k z ≠ 0) :
    dist (vertexPoint ε η k) z < d + ε := by
  have hvp : vertexPoint ε η k ∈ cell ε η k :=
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩
  have hbdd : Bornology.IsBounded (cell ε η k) := (isCompact_Icc.image hη).isBounded
  obtain ⟨y, hy, hyz⟩ := (Metric.infDist_lt_iff ⟨_, hvp⟩).1
    ((interpWeight_ne_zero_iff (fun k => cell ε η k) ε k z).1 hk)
  have hyball : y ∈ ball (0 : ℂ) (ρ + 1) := by
    rw [mem_ball]
    have h1 := dist_triangle y z 0
    have h2 : dist z 0 = ‖z‖ := dist_zero_right z
    rw [dist_comm y z] at h1
    linarith
  have hdiam : Metric.diam (cell ε η k) ≤ d :=
    (ENNReal.ofReal_le_ofReal_iff hd0).1
      ((le_iSup₂ (f := fun k (_ : (cell ε η k ∩ ball (0 : ℂ) (ρ + 1)).Nonempty) =>
        ENNReal.ofReal (Metric.diam (cell ε η k))) k ⟨y, hy, hyball⟩).trans hmesh)
  have hvy : dist (vertexPoint ε η k) y ≤ d := (Metric.dist_le_diam_of_mem hbdd hvp hy).trans hdiam
  have h2 := dist_triangle (vertexPoint ε η k) y z
  rw [dist_comm y z] at h2
  linarith

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The stopped class law of the interpolated quenched walk at a point.**  On the uniform-start good event with
tolerance `κ` and finite exits, if the cells meeting `B_{ρ+1}` have diameter at most `d`, `‖z‖ + d + ε ≤ ρ`, and the
Brownian class law varies by at most `κ₂` (Lévy–Prokhorov) over the ball of radius `d + ε` around `z`, then the stopped
class law of the interpolated walk at `z` is within `κ + κ₂` of the stopped class law of planar Brownian motion
from `z`. -/
theorem levyProkhorovDist_interpWalkLaw_stoppedExitCurve_le (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ))
    {ε R ρ κ κ₂ d : ℝ} (hε : 0 ≤ ε) (hκ : 0 ≤ κ) (hd0 : 0 ≤ d) (hmε : 0 < S.mε ε) {ω : Ω}
    (hη : ⇑(η' ω) = S.η ω)
    (hloc : ∀ z, ∃ U ∈ 𝓝 z,
      {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0)
    (hfin : ω ∈ UniformStartGood.finExit S ε R ρ) (hG : ω ∈ UniformStartGood.goodG S ε R ρ κ)
    (hmesh : maxCellDiam ε (⇑(η' ω)) ρ ≤ ENNReal.ofReal d) {z : ℂ} (hz : ‖z‖ + d + ε ≤ ρ)
    (hBM : ∀ w : ℂ, dist w z < d + ε →
      levyProkhorovDist ((planarBrownianMotion w).map (stoppedExitCurve (ball (0 : ℂ) R)))
        ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤ κ₂) :
    levyProkhorovDist
      (((interpWalkLaw S η' ε ω z : ProbabilityMeasure (ContinuousPath ℂ)) :
        Measure (ContinuousPath ℂ)).map (stoppedExitCurve (ball (0 : ℂ) R)))
      ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤ κ + κ₂ := by
  refine MatedCRT.FirstPass.Derived.levyProkhorovDist_map_interpWalkLaw_le S η' hloc hpos
    (measurable_stoppedExitCurve _ isOpen_ball)
    ((planarBrownianMotion z).map (stoppedExitCurve (ball (0 : ℂ) R))).toProbabilityMeasure z ?_
  intro k hk
  have hdist := dist_vertexPoint_lt_of_interpWeight_ne_zero (η' ω).continuous hε hd0 hmesh
    (by linarith) hk
  have hvρ : vertexPoint ε (⇑(η' ω)) k ∈ closedBall (0 : ℂ) ρ := by
    rw [mem_closedBall, dist_zero_right]
    have h1 := norm_le_norm_add_norm_sub' (vertexPoint ε (⇑(η' ω)) k) z
    rw [← dist_eq_norm] at h1
    linarith
  have hA := WalkClassLevyProkhorov.levyProkhorovEDist_walkPathLaw_stoppedExitCurve_le S η' hmε hη hfin hG hvρ
  have hA' : levyProkhorovDist
      (((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω :
        ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)).map
          (stoppedExitCurve (ball (0 : ℂ) R)))
      ((planarBrownianMotion (vertexPoint ε (⇑(η' ω)) k)).map (stoppedExitCurve (ball (0 : ℂ) R))) ≤ κ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hA
    rwa [ENNReal.toReal_ofReal hκ] at this
  have hB := hBM _ hdist
  exact (levyProkhorovDist_triangle _ _ _).trans (add_le_add hA' hB)

end MatedCRT.InterpClassClose
