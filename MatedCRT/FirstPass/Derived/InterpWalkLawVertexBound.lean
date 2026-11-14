import MatedCRT.FirstPass.Derived.InterpKernelModulus

/-!
# The quenched walk law of the vertex of a point is close to the interpolated law at the point

For the interpolated quenched walk law `interpWalkLaw S η' ε ω : ℂ → Prob(ContinuousPath ℂ)` (the mixture of the
quenched path laws `Q^ε(k)(ω)` with weights `(ε - dist(z, H_k))₊`), the quenched path law `Q^ε(j)(ω)` of the vertex `j`
whose cell contains `z` is within `a` of `interpWalkLaw z` in the Lévy–Prokhorov distance of `dUnif`, as soon as every
cell meeting `B_{R+1}` has diameter at most `d`, the vertex-indexed modulus `ω^ε_R(δ)` of the quenched walk laws is at
most `a`, and `2 d + ε ≤ δ` (Berestycki–Gwynne (2020), proof of Prop. 6.1, comparison of `P̃^ε_z` and `Q^ε(a^ε_z)`).
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory ProbabilityTheory Filter Topology Set Metric LatticeProb
open MarkovProcess (ContinuousPath)
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- **`Q^ε(j)` is close to the interpolated law at a point of the cell `H_j`.** If `z ∈ H^ε_j`, `|z| ≤ R`, every
cell meeting `B_{R+1}` has diameter at most `d`, `ε + d < 1`, `2 d + ε ≤ δ` and `ω^ε_R(δ) ≤ a`, then
`LP(Q^ε(j)(ω), P̃^ε_z(ω)) ≤ a`. -/
theorem pathLevyProkhorovEDist_walkPathLaw_interpWalkLaw_le_of_mem_cell (S : MatedCRTEnv Ω) (η' : Ω → C(ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) {ω : Ω}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k : ℤ | ∃ y ∈ U, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k : ℤ, interpWeight (fun k => cell ε (⇑(η' ω)) k) ε k z ≠ 0)
    {R δ d a : ℝ} (hd0 : 0 ≤ d) (hδ : 2 * d + ε ≤ δ) (h1 : ε + d < 1) (ha : 0 ≤ a)
    (hD : maxCellDiam ε (⇑(η' ω)) R ≤ ENNReal.ofReal d)
    (hmod : walkLawModulus S η' ε R δ ω ≤ ENNReal.ofReal a)
    {z : ℂ} (hz : ‖z‖ ≤ R) {j : ℤ} (hzj : z ∈ cell ε (⇑(η' ω)) j) :
    pathLevyProkhorovEDist (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε j ω)
      (interpWalkLaw S η' ε ω z) ≤ ENNReal.ofReal a := by
  let : PseudoMetricSpace (ContinuousPath ℂ) := dUnifPseudoMetric
  have hOMS : @OpensMeasurableSpace (ContinuousPath ℂ)
      (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _ ‹_›)) _ :=
    opensMeasurableSpace_dUnif
  have hdiam : ∀ (k : ℤ) (y : ℂ), y ∈ cell ε (⇑(η' ω)) k → y ∈ ball (0 : ℂ) (R + 1) →
      Metric.diam (cell ε (⇑(η' ω)) k) ≤ d := by
    intro k y hy hyball
    have h := (le_iSup₂ (f := fun k (_ : (cell ε (⇑(η' ω)) k ∩ ball (0 : ℂ) (R + 1)).Nonempty) =>
      ENNReal.ofReal (Metric.diam (cell ε (⇑(η' ω)) k))) k ⟨y, hy, hyball⟩).trans hD
    exact (ENNReal.ofReal_le_ofReal_iff hd0).1 h
  have hbdd : ∀ k : ℤ, Bornology.IsBounded (cell ε (⇑(η' ω)) k) := fun k =>
    (isCompact_Icc.image (η' ω).continuous).isBounded
  have hv : ∀ k : ℤ, vertexPoint ε (⇑(η' ω)) k ∈ cell ε (⇑(η' ω)) k := fun k =>
    ⟨ε * k, ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_rfl⟩, rfl⟩
  have hnorm : ∀ u w : ℂ, ‖u‖ ≤ ‖w‖ + dist u w := fun u w => by
    have := dist_triangle u w 0
    rw [dist_zero_right, dist_zero_right] at this
    linarith
  have hzball : z ∈ ball (0 : ℂ) (R + 1) := mem_ball_zero_iff.2 (by linarith)
  have hdj : Metric.diam (cell ε (⇑(η' ω)) j) ≤ d := hdiam j z hzj hzball
  have hvjz : dist (vertexPoint ε (⇑(η' ω)) j) z ≤ d :=
    (dist_le_diam_of_mem (hbdd j) (hv j) hzj).trans hdj
  have hvj : vertexPoint ε (⇑(η' ω)) j ∈ ball (0 : ℂ) (R + 1) :=
    mem_ball_zero_iff.2 (by linarith [hnorm (vertexPoint ε (⇑(η' ω)) j) z])
  have hL : ∀ k : ℤ, Metric.infDist z (cell ε (⇑(η' ω)) k) < ε →
      levyProkhorovDist
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε j ω :
          Measure (ContinuousPath ℂ))
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω :
          Measure (ContinuousPath ℂ)) ≤ a := by
    intro k hk
    obtain ⟨y, hy, hzy⟩ := (Metric.infDist_lt_iff ⟨_, hv k⟩).1 hk
    have hyball : y ∈ ball (0 : ℂ) (R + 1) :=
      mem_ball_zero_iff.2 (by linarith [hnorm y z, dist_comm y z])
    have hdk := hdiam k y hy hyball
    have hyv : dist y (vertexPoint ε (⇑(η' ω)) k) ≤ d :=
      (dist_le_diam_of_mem (hbdd k) hy (hv k)).trans hdk
    have hzv : dist z (vertexPoint ε (⇑(η' ω)) k) ≤ ε + d := by
      have := dist_triangle z y (vertexPoint ε (⇑(η' ω)) k)
      linarith
    have hvk : vertexPoint ε (⇑(η' ω)) k ∈ ball (0 : ℂ) (R + 1) :=
      mem_ball_zero_iff.2 (by linarith [hnorm (vertexPoint ε (⇑(η' ω)) k) z, dist_comm (vertexPoint ε (⇑(η' ω)) k) z])
    have hdist : dist (vertexPoint ε (⇑(η' ω)) j) (vertexPoint ε (⇑(η' ω)) k) ≤ δ := by
      have := dist_triangle (vertexPoint ε (⇑(η' ω)) j) z (vertexPoint ε (⇑(η' ω)) k)
      linarith
    have hm : pathLevyProkhorovEDist
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε j ω)
        (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
          ≤ walkLawModulus S η' ε R δ ω :=
      le_iSup₂_of_le j k (le_iSup_of_le ⟨hvj, hvk, hdist⟩ le_rfl)
    exact ENNReal.toReal_le_of_le_ofReal ha (hm.trans hmod)
  have hL1 := levyProkhorovDist_interpLaw_le hloc hpos
    (fun k => walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε k ω)
    (walkPathLaw S (fun ω => vertexPoint ε (⇑(η' ω))) (S.mε_nonneg ε) ε j ω) z ha hL
  rw [interpWalkLaw_eq_of_good S η' hloc hpos z]
  show levyProkhorovEDist _ _ ≤ _
  rw [← ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hL1

end MatedCRT.FirstPass.Derived
