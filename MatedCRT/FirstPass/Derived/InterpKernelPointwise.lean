import MatedCRT.FirstPass.Derived.UniformScales
import MatedCRT.FirstPass.Derived.InterpKernelVertex
import MatedCRT.FirstPass.Derived.InterpolatedLawAssembly
import LatticeProb.Prob.PathLawCompactSet
import LatticeProb.Prob.InterpolatedLawMeasureBound

/-!
# The interpolated walk law at a point lies in a compact set of path laws

Deterministic step of the tightness of the interpolated quenched walk laws `z ↦ P̃^ε(ω)(z)`: fix
`z`, a radius `m ≥ ‖z‖`, a mesh bound `B ≥ ε`, a bound `D ≥ 0` for the cell diameters in
`B_{m+B}`, scales `δ_k > 0` and levels `a_k ≤ 1 / (k + 1)`.  For a proper onto curve with cell
diameters in `B_{m+B}` at most `D` and no vertex of `B_{m+B+D+1}` whose walk path law charges the
modulus failure of level `k + 1` at scale `δ_k` with mass above `a_k`, the law `P̃^ε(ω)(z)` is a
mixture of walk path laws from vertices within `ε + D ≤ B + D` of `z`, hence charges only paths
starting within `B + D` of `z` and the modulus failures with mass at most `1 / (k + 1)`: it lies in
the compact set of `LatticeProb.exists_isCompact_pathLaws`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

attribute [local instance] dUnifMetricSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- A cell within distance `ε ≤ B` of `z`, when the cells meeting `B_{R+B+1}` have diameter at most
`d`, has its vertex within `ε + d` of `z`, hence in the ball of radius `R + ε + d`. -/
theorem vertex_near_of_infDist_lt_le {η : C(ℝ, ℂ)} {ε B R d : ℝ} (hε : 0 ≤ ε) (hεB : ε ≤ B)
    (hd0 : 0 ≤ d) (hD : maxCellDiam ε (⇑η) (R + B) ≤ ENNReal.ofReal d) {z : ℂ} (hz : ‖z‖ ≤ R)
    {k : ℤ} (hk : Metric.infDist z (cell ε (⇑η) k) < ε) :
    dist z (vertexPoint ε (⇑η) k) < ε + d ∧ ‖vertexPoint ε (⇑η) k‖ < R + ε + d := by
  have hvk : vertexPoint ε (⇑η) k ∈ cell ε (⇑η) k :=
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩
  obtain ⟨y, hy, hyz⟩ := (Metric.infDist_lt_iff ⟨_, hvk⟩).1 hk
  have hbdd : Bornology.IsBounded (cell ε (⇑η) k) :=
    (isCompact_Icc.image η.continuous).isBounded
  have hyk := Metric.dist_le_diam_of_mem hbdd hy hvk
  have hz0 := dist_zero_right z
  have hyball : y ∈ ball (0 : ℂ) (R + B + 1) := by
    rw [mem_ball]
    have h2 := dist_triangle y z 0
    have h3 := dist_comm y z
    linarith
  have hdiam : Metric.diam (cell ε (⇑η) k) ≤ d := by
    have h := (le_iSup₂ (f := fun k (_ : (cell ε (⇑η) k ∩ ball (0 : ℂ) (R + B + 1)).Nonempty) =>
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

/-- **Compact set of values of the interpolated walk law at a point.** -/
theorem exists_isCompact_interpWalkLaw (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ)) (z : ℂ)
    (m B D : ℝ) (hD : 0 ≤ D) (δ : ℕ → ℝ≥0) (hδ : ∀ k, 0 < δ k) (a : ℕ → ℝ)
    (ha : ∀ k : ℕ, a k ≤ 1 / ((k : ℝ) + 1)) :
    ∃ K : Set (LevyProkhorov (ProbabilityMeasure (ContinuousPath ℂ))), IsCompact K ∧
      ∀ (ω : Ω) (ε : ℝ), ω ∈ properCurveSet η' → 0 < ε → ε ≤ B → ‖z‖ ≤ m →
        maxCellDiam ε (⇑(η' ω)) (m + B) ≤ ENNReal.ofReal D →
        (∀ k : ℕ, ω ∉ vertexPathFailure S η' ε (m + B + D) ((k : ℝ) + 1) (a k) (δ k)) →
        LevyProkhorov.probabilityMeasureHomeomorph (interpWalkLaw S η' ε ω z) ∈ K := by
  obtain ⟨K, hK, hKmem⟩ := exists_isCompact_pathLaws (E := ℂ) z (B + D) δ hδ
  refine ⟨K, hK, fun ω ε hω hε hεB hz hdiam hgood => ?_⟩
  obtain ⟨hloc, hpos⟩ := interpWeight_good_of_proper_surjective hε hω.1 hω.2
  have hQ : ∀ {s : Set (ContinuousPath ℂ)}, MeasurableSet s → ∀ {b : ℝ≥0∞},
      (∀ k : ℤ, Metric.infDist z (cell ε (⇑(η' ω)) k) < ε →
        ((walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω :
          ProbabilityMeasure (ContinuousPath ℂ)) : Measure (ContinuousPath ℂ)) s ≤ b) →
      ((interpWalkLaw S η' ε ω z : ProbabilityMeasure (ContinuousPath ℂ)) :
        Measure (ContinuousPath ℂ)) s ≤ b := by
    intro s hs b h
    rw [interpWalkLaw_eq_of_good S η' hloc hpos z]
    exact interpLaw_apply_le hloc hpos _ z hs h
  refine hKmem _ ?_ ?_
  · refine le_antisymm (hQ (measurableSet_pathStart_gt z (B + D)) fun k hk => ?_) zero_le
    have h1 := (vertex_near_of_infDist_lt_le hε.le hεB hD hdiam hz hk).1
    exact (walkPathLaw_start_null S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω
      (r := B + D) (by
        show dist (vertexPoint ε (⇑(η' ω)) k) z ≤ B + D
        rw [dist_comm]
        linarith)).le
  · intro k
    refine hQ (isOpen_pathModulusFailure _ _).measurableSet fun j hj => ?_
    have hv := (vertex_near_of_infDist_lt_le hε.le hεB hD hdiam hz hj).2
    have hball : vertexPoint ε (⇑(η' ω)) j ∈ ball (0 : ℂ) (m + B + D + 1) := by
      rw [mem_ball, dist_zero_right]
      linarith
    have h := hgood k
    simp only [vertexPathFailure, mem_ofPred_eq, not_exists, not_and, not_lt] at h
    exact (h j hball).trans (ENNReal.ofReal_le_ofReal (ha k))

end MatedCRT.FirstPass.Derived
