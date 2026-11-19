import MatedCRT.FirstPass.Derived.ReversibilityPairingDiscrete

/-!
# The walk law against the interpolated law at a point of the cell

`pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le` compares the quenched walk law `Q^ε(x)` with the
interpolated law `P̃^ε` at the vertex position `η(εx)`.  The embedded walk of Theorem 2.11 starts at the vertex
`x` of a cell `H^ε_x` containing a fixed point `z`, so the comparison is needed at `z ∈ H^ε_x`:
`pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

attribute [local instance] LatticeProb.dUnifMetricSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The walk law against the interpolated law at a point of the cell** (MATH-ANSWERS step 3 at a point
`z ∈ H^ε_x`): on the event where the interpolation is defined, if `z ∈ H^ε_x`, `|z| ≤ R`, the cells meeting
`B_{R+1}` have diameter at most `d`, `ε + 2 d ≤ δ`, `ε + d < 1` and `ω^ε_R(δ) ≤ a`, then
`LP(Q^ε(x), P̃^ε_z) ≤ a`. -/
theorem pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell (S : MatedCRTEnv Ω)
    (η' : Ω → C(ℝ, ℂ)) {ε : ℝ} (hε : 0 ≤ ε) {ω : Ω}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0)
    {R δ d a : ℝ} (hd0 : 0 ≤ d) (hd : ε + 2 * d ≤ δ) (hd1 : ε + d < 1) (ha : 0 ≤ a)
    (hD : maxCellDiam ε (⇑(η' ω)) R ≤ ENNReal.ofReal d)
    (hmod : walkLawModulus S η' ε R δ ω ≤ ENNReal.ofReal a)
    {x : ℤ} {z : ℂ} (hz : z ∈ cell ε (⇑(η' ω)) x) (hzR : ‖z‖ ≤ R) :
    pathLevyProkhorovEDist (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω)
      (interpWalkLaw S η' ε ω z) ≤ ENNReal.ofReal a := by
  let : PseudoMetricSpace (ContinuousPath ℂ) := dUnifPseudoMetric
  have hOMS : @OpensMeasurableSpace (ContinuousPath ℂ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _ ‹_›)) _ :=
    opensMeasurableSpace_dUnif
  have hvp : ∀ k : ℤ, vertexPoint ε (⇑(η' ω)) k ∈ cell ε (⇑(η' ω)) k := fun k =>
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε, le_rfl⟩, rfl⟩
  have hbdd : ∀ k : ℤ, Bornology.IsBounded (cell ε (⇑(η' ω)) k) := fun k =>
    (isCompact_Icc.image (η' ω).continuous).isBounded
  have hzball : z ∈ ball (0 : ℂ) (R + 1) := by
    rw [mem_ball, dist_zero_right]
    linarith
  have hdiam : ∀ k : ℤ, ∀ y ∈ cell ε (⇑(η' ω)) k, y ∈ ball (0 : ℂ) (R + 1) →
      Metric.diam (cell ε (⇑(η' ω)) k) ≤ d := by
    intro k y hy hyball
    have h := (le_iSup₂ (f := fun k (_ : (cell ε (⇑(η' ω)) k ∩ ball (0 : ℂ) (R + 1)).Nonempty) =>
      ENNReal.ofReal (Metric.diam (cell ε (⇑(η' ω)) k))) k ⟨y, hy, hyball⟩).trans hD
    exact (ENNReal.ofReal_le_ofReal_iff hd0).1 h
  have hdx : Metric.diam (cell ε (⇑(η' ω)) x) ≤ d := hdiam x z hz hzball
  have hzx : dist z (vertexPoint ε (⇑(η' ω)) x) ≤ d :=
    (Metric.dist_le_diam_of_mem (hbdd x) hz (hvp x)).trans hdx
  have hk : ∀ k : ℤ, Metric.infDist z (cell ε (⇑(η' ω)) k) < ε →
      levyProkhorovDist
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω : Measure (ContinuousPath ℂ))
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω : Measure (ContinuousPath ℂ))
        ≤ a := by
    intro k hk
    have hvk := hvp k
    obtain ⟨y, hy, hyz⟩ := (Metric.infDist_lt_iff ⟨_, hvk⟩).1 hk
    have hyk := Metric.dist_le_diam_of_mem (hbdd k) hy hvk
    have hyball : y ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball]
      have h1 := dist_triangle y z 0
      have h2 := dist_comm y z
      have h3 := dist_zero_right z
      linarith
    have hdk : Metric.diam (cell ε (⇑(η' ω)) k) ≤ d := hdiam k y hy hyball
    have hxk : dist (vertexPoint ε (⇑(η' ω)) x) (vertexPoint ε (⇑(η' ω)) k) < ε + 2 * d := by
      have h1 := dist_triangle (vertexPoint ε (⇑(η' ω)) x) z (vertexPoint ε (⇑(η' ω)) k)
      have h2 := dist_triangle z y (vertexPoint ε (⇑(η' ω)) k)
      have h3 := dist_comm (vertexPoint ε (⇑(η' ω)) x) z
      linarith
    have hxball : vertexPoint ε (⇑(η' ω)) x ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball]
      have h1 := dist_triangle (vertexPoint ε (⇑(η' ω)) x) z 0
      have h3 := dist_zero_right z
      have h4 := dist_comm (vertexPoint ε (⇑(η' ω)) x) z
      linarith
    have hkball : vertexPoint ε (⇑(η' ω)) k ∈ ball (0 : ℂ) (R + 1) := by
      rw [mem_ball]
      have h1 := dist_triangle (vertexPoint ε (⇑(η' ω)) k) y 0
      have h2 := dist_triangle y z 0
      have h3 := dist_zero_right z
      have h4 := dist_comm y z
      have h5 := dist_comm y (vertexPoint ε (⇑(η' ω)) k)
      linarith
    have hm : pathLevyProkhorovEDist
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω)
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
          ≤ walkLawModulus S η' ε R δ ω :=
      le_iSup₂_of_le x k (le_iSup_of_le ⟨hxball, hkball, by linarith⟩ le_rfl)
    exact ENNReal.toReal_le_of_le_ofReal ha (hm.trans hmod)
  have hL := levyProkhorovDist_interpLaw_le hloc hpos
    (fun k => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
    (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε x ω) z ha hk
  rw [interpWalkLaw_eq_of_good S η' hloc hpos]
  show levyProkhorovEDist _ _ ≤ _
  rw [← ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hL

end MatedCRT.FirstPass.Derived
