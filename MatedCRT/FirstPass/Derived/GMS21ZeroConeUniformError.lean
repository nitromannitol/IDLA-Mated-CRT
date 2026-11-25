import MatedCRT.FirstPass.Derived.GMS21AnnulusOfCurveLaw
import MatedCRT.FirstPass.Derived.GMS21UniformStartOfAnnulus
import MatedCRT.FirstPass.Derived.UniformStartGoodFinExit
import MatedCRT.FirstPass.Derived.StopAtExitNested

/-!
# The uniform error of the invariance principle and the comparison on an annulus

In the proof of Theorem 3.4, case 1, of Gwynne–Miller–Sheffield (arXiv:1705.11161, lines 1303-1307), the quantity
which tends to `0` in probability is the supremum, over the starts `z` in a compact set, of the Prokhorov distance
between the law of the embedded walk started from the cell containing `z` and the law of Brownian motion started from
`z`, modulo time parametrization, in the local metric (2.2).

* `uniformLPError A c v m`: this supremum for the multigraph `m` on `ℤ` with cells `c x` and embedded vertices `v x`,
  over starts `z ∈ A` and vertices `x` whose cell contains `z`.
* `exists_mem_annulusSelectedLPData_of_uniformLPError_lt`: for `0 < α < b < ρ < R` and `c > 0` there is `δ > 0` such
  that every datum with a proper curve and a locally finite multigraph with the successor edges whose uniform error
  over `closedBall 0 ρ \ B_b(0)` at mesh `ε` is less than `δ` lies in the good set `annulusSelectedLPData ε α b ρ R c`.
-/

set_option autoImplicit false

open MeasureTheory Set Metric Filter HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

noncomputable section

namespace MatedCRT.GMS310Transfer

open LatticeProb LatticeProb.UnboundedRayIntervalIntegrand LatticeProb.UnboundedRayLocalDistance
  LatticeProb.UnboundedRayCurveSpace LatticeProb.ReparamDistanceIsometry
open ReflectedGMS.StatementIngredients

local instance : MeasurableSpace (UnboundedRayCurveSpace 2) := borel _

attribute [local instance] isProbabilityMeasure_map_complexToEuclideanPath

/-- **The uniform error of the invariance principle.** For the multigraph `m` on `ℤ` with cells `c x` and embedded
vertices `v x`: the supremum over starts `z ∈ A` and vertices `x` whose cell contains `z` of the Lévy–Prokhorov
distance between the law modulo time parametrization of the interpolated embedded walk from `x` (restricted to the
unbounded paths) and that of planar Brownian motion from `z`. -/
def uniformLPError (A : Set ℂ) (c : ℤ → Set ℂ) (v : ℤ → ℂ) (m : ℤ → ℤ → ℕ) : ℝ≥0∞ :=
  ⨆ z ∈ A, ⨆ x ∈ {x : ℤ | z ∈ c x},
    levyProkhorovEDist (GMS310.unboundedCurveLaw ((srwLaw m x).map fun ξ =>
        complexToEuclideanPath (interpPathCM v zero_le_one ξ)))
      (curveLaw ((planarBrownianMotion z).map complexToEuclideanPath)
        (ae_unbounded_range_map_planarBrownianMotion z))

theorem levyProkhorovEDist_le_uniformLPError {A : Set ℂ} {c : ℤ → Set ℂ} (v : ℤ → ℂ) (m : ℤ → ℤ → ℕ)
    {z : ℂ} (hz : z ∈ A) {x : ℤ} (hx : z ∈ c x) :
    levyProkhorovEDist (GMS310.unboundedCurveLaw ((srwLaw m x).map fun ξ =>
        complexToEuclideanPath (interpPathCM v zero_le_one ξ)))
      (curveLaw ((planarBrownianMotion z).map complexToEuclideanPath)
        (ae_unbounded_range_map_planarBrownianMotion z)) ≤ uniformLPError A c v m := by
  unfold uniformLPError
  exact le_iSup₂_of_le z hz (le_iSup₂_of_le (f := fun x (_ : x ∈ {x : ℤ | z ∈ c x}) =>
    levyProkhorovEDist (GMS310.unboundedCurveLaw ((srwLaw m x).map fun ξ =>
        complexToEuclideanPath (interpPathCM v zero_le_one ξ)))
      (curveLaw ((planarBrownianMotion z).map complexToEuclideanPath)
        (ae_unbounded_range_map_planarBrownianMotion z))) x hx le_rfl)

/-- **From the uniform error to the good set on an annulus** (proof of Theorem 3.4, case 1, of arXiv:1705.11161). For
`0 < α < b < ρ < R` and `c > 0` there is `δ > 0` such that for every mesh `ε > 0` and every datum `d` whose curve is
proper and whose multigraph is locally finite with the successor edges, if the uniform error over
`closedBall 0 ρ \ B_b(0)` of the walk on `d.2` with the cells and vertices of `d.1` at mesh `ε` is less than `δ`, then
`d` lies in `annulusSelectedLPData ε α b ρ R c`. -/
theorem exists_mem_annulusSelectedLPData_of_uniformLPError_lt {α b ρ R c : ℝ} (hα : 0 < α) (hαb : α < b)
    (hbρ : b < ρ) (hρR : ρ < R) (hc : 0 < c) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ∀ d : C(ℝ, ℂ) × (ℤ → ℤ → ℕ),
      Tendsto d.1 (cocompact ℝ) (cocompact ℂ) → IsLocallyFiniteMult d.2 → (∀ k : ℤ, d.2 k (k + 1) ≠ 0) →
      uniformLPError (closedBall (0 : ℂ) ρ \ ball 0 b) (cell ε d.1) (vertexPoint ε d.1) d.2 <
        ENNReal.ofReal δ →
      d ∈ annulusSelectedLPData ε α b ρ R c := by
  obtain ⟨δ, hδ, hAnn⟩ :=
    exists_levyProkhorovEDist_stoppedExitCurve_annulus_lt (Ω' := ℕ → ℤ) hα hαb hbρ hρR hc
  refine ⟨δ, hδ, fun ε hε d hp hlf hsucc herr => ?_⟩
  intro z hzb hzρ x hzx
  have hzA : z ∈ closedBall (0 : ℂ) ρ \ ball 0 b := ⟨hzρ, hzb⟩
  have hfin : ∀ᵐ ξ ∂(srwLaw d.2 x), pathExitTime (ball (0 : ℂ) R \ closedBall 0 α)
      ⇑(interpPathCM (vertexPoint ε d.1) zero_le_one ξ) ≠ ⊤ := by
    filter_upwards [UniformStartGood.ae_pathExitTime_interpolatedWalk_ne_top hε d.1.continuous hp hlf
      hsucc R x] with ξ hξ
    exact ne_top_of_le_ne_top hξ (StopAtExitCmp.pathExitTime_mono sdiff_subset _)
  exact hAnn z hzA (srwLaw d.2 x) (interpPathCM (vertexPoint ε d.1) zero_le_one)
    (measurable_interpPathCM _ _) hfin
    ((levyProkhorovEDist_le_uniformLPError (vertexPoint ε d.1) d.2 hzA hzx).trans_lt herr)

end MatedCRT.GMS310Transfer
