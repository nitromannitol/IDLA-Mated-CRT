import MatedCRT.FirstPass.Derived.InterpKernelModulus
import MatedCRT.FirstPass.Derived.ExitCouplingEvents

/-!
# Vertices, starting points and cell diameters for the interpolated walk laws

Deterministic and almost-sure facts used to bound the interpolated quenched walk law `P̃^ε_z(ω)` by
its vertex laws `Q^ε(k)(ω)`:

* `vertex_near_of_infDist_lt`: a cell within distance `ε` of `z`, with `‖z‖ ≤ R`, `ε ≤ 1`, and all
  cells meeting `B_{R+1}` of diameter at most `d`, has its vertex within `ε + d` of `z`, hence in
  the ball of radius `R + ε + d`;
* `walkPathLaw_start_null`: the walk path law from vertex `k` charges only paths starting at `v k`;
* `maxCellDiam_lt_top_of_proper`: for a proper onto curve the largest cell diameter in a ball is
  finite.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- The start event `{f | r < dist (f 0) z}` of continuous paths is open, hence measurable. -/
theorem measurableSet_pathStart_gt (z : ℂ) (r : ℝ) :
    MeasurableSet {f : ContinuousPath ℂ | r < dist (f 0) z} :=
  (isOpen_lt continuous_const ((continuous_eval_const (0 : ℝ≥0)).dist continuous_const)).measurableSet

/-- A cell within distance `ε` of `z` has its vertex near `z`, when the cells meeting `B_{R+1}` have
diameter at most `d`. -/
theorem vertex_near_of_infDist_lt {η : C(ℝ, ℂ)} {ε R d : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hd0 : 0 ≤ d)
    (hD : maxCellDiam ε (⇑η) R ≤ ENNReal.ofReal d) {z : ℂ} (hz : ‖z‖ ≤ R) {k : ℤ}
    (hk : Metric.infDist z (cell ε (⇑η) k) < ε) :
    dist z (vertexPoint ε (⇑η) k) < ε + d ∧ ‖vertexPoint ε (⇑η) k‖ < R + ε + d := by
  have hvk : vertexPoint ε (⇑η) k ∈ cell ε (⇑η) k :=
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩
  obtain ⟨y, hy, hyz⟩ := (Metric.infDist_lt_iff ⟨_, hvk⟩).1 hk
  have hbdd : Bornology.IsBounded (cell ε (⇑η) k) :=
    (isCompact_Icc.image η.continuous).isBounded
  have hyk := Metric.dist_le_diam_of_mem hbdd hy hvk
  have hz0 := dist_zero_right z
  have hyball : y ∈ ball (0 : ℂ) (R + 1) := by
    rw [mem_ball]
    have h2 := dist_triangle y z 0
    have h3 := dist_comm y z
    linarith
  have hdiam : Metric.diam (cell ε (⇑η) k) ≤ d := by
    have h := (le_iSup₂ (f := fun k (_ : (cell ε (⇑η) k ∩ ball (0 : ℂ) (R + 1)).Nonempty) =>
      ENNReal.ofReal (Metric.diam (cell ε (⇑η) k))) k ⟨y, hy, hyball⟩).trans hD
    exact (ENNReal.ofReal_le_ofReal_iff hd0).1 h
  have hzk : dist z (vertexPoint ε (⇑η) k) < ε + d := by
    have := dist_triangle z y (vertexPoint ε (⇑η) k)
    linarith
  refine ⟨hzk, ?_⟩
  have h2 := dist_triangle (vertexPoint ε (⇑η) k) z 0
  have h3 := dist_comm (vertexPoint ε (⇑η) k) z
  have h4 := dist_zero_right (vertexPoint ε (⇑η) k)
  linarith

/-- The walk path law from vertex `k` charges only paths starting at `v ω k`: if `v ω k` is within
`r` of `z`, the paths starting farther than `r` from `z` form a null set. -/
theorem walkPathLaw_start_null (S : MatedCRTEnv Ω) (v : Ω → ℤ → ℂ) {m : ℝ} (hm : 0 ≤ m) (ε : ℝ)
    (k : ℤ) (ω : Ω) {z : ℂ} {r : ℝ} (h : dist (v ω k) z ≤ r) :
    (walkPathLaw S v hm ε k ω : Measure (ContinuousPath ℂ)) {f | r < dist (f 0) z} = 0 := by
  have hcoe : ((walkPathLaw S v hm ε k ω : ProbabilityMeasure (ContinuousPath ℂ)) :
      Measure (ContinuousPath ℂ)) =
      Measure.map (interpPathCM (v ω) hm) (srwLaw (S.mult ε ω) k) := rfl
  rw [hcoe, Measure.map_apply (measurable_interpPathCM (v ω) hm) (measurableSet_pathStart_gt z r)]
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [srwLaw_ae_start (S.mult ε ω) k] with x hx hx'
  have h0 : interpPathCM (v ω) hm x 0 = v ω k := by
    rw [interpPathCM_apply, MatedCRT.ExitCouplingEvents.interpPathFn_zero, hx]
  change r < dist (interpPathCM (v ω) hm x 0) z at hx'
  rw [h0] at hx'
  exact absurd h (not_le.2 hx')

/-- For a proper onto curve, the largest diameter of the cells meeting `B_{R+1}` is finite. -/
theorem maxCellDiam_lt_top_of_proper {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ}
    (hη : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hsurj : Function.Surjective η) (R : ℝ) :
    maxCellDiam ε η R < ⊤ := by
  obtain ⟨-, -, hfin⟩ := cell_cover_finite_of_proper_surjective hε hη hsurj
  have hF := hfin 0 (R + 1)
  refine lt_of_le_of_lt (b := hF.toFinset.sup fun k => ENNReal.ofReal (Metric.diam (cell ε η k)))
    ?_ ?_
  · refine iSup₂_le fun k hk => ?_
    obtain ⟨y, hy, hyb⟩ := hk
    exact Finset.le_sup (f := fun k => ENNReal.ofReal (Metric.diam (cell ε η k)))
      (hF.mem_toFinset.2 ⟨y, hy, mem_ball.1 hyb⟩)
  · exact (Finset.sup_lt_iff (by simp)).2 fun _ _ => ENNReal.ofReal_lt_top

end MatedCRT.FirstPass.Derived
