import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion

/-!
# Polish coordinates of whole-plane distributions and their circle averages

A whole-plane distribution `H : LQGMetric.DistC` is encoded by its pairings
`LQGMetric.pairJ ⊤ H : LQGMetric.CoordJ → ℝ` against the countable family `LQGMetric.CoordJ` of integer
combinations of the generating test functions. The coordinate space `LQGMetric.CoordJ → ℝ` is Polish and
Borel, the coordinate map is a measurable embedding with Borel range, and its Borel left inverse
`LQGMetric.pairJInv ⊤` recovers `H`.

This file records these facts and defines the circle-average process of a coordinate vector,
`coordCircleAverage x r z`, as the distributional circle version of the decoded distribution. It is jointly
Borel in `(x, r, z)`, it equals the distributional circle version on the range of the coordinate map, and for
any measurable version `H` of the field of a valid mated-CRT environment it recovers, almost surely, the
circle average `S.hcirc ω r z` of the field at every positive radius `r` and every center `z`.

## Main statements

* `MatedCRT.polishSpace_coordJ`, `MatedCRT.borelSpace_coordJ`, `MatedCRT.measurable_pairJ_top`;
* `MatedCRT.measurable_coordCircleAverage`, `MatedCRT.coordCircleAverage_pairJ`;
* `MatedCRT.MatedCRTEnv.IsValid.ae_coordCircleAverage_eq`.
-/

noncomputable section

open MeasureTheory

namespace MatedCRT

/-- The coordinate space of whole-plane distributions is Polish: `LQGMetric.CoordJ` is countable. -/
theorem polishSpace_coordJ : PolishSpace (LQGMetric.CoordJ → ℝ) := inferInstance

/-- The coordinate space of whole-plane distributions carries the Borel σ-algebra of its product topology. -/
theorem borelSpace_coordJ : BorelSpace (LQGMetric.CoordJ → ℝ) := inferInstance

/-- The coordinate map of whole-plane distributions is measurable. -/
theorem measurable_pairJ_top :
    Measurable (LQGMetric.pairJ ⊤ : LQGMetric.DistC → LQGMetric.CoordJ → ℝ) :=
  LQGMetric.measurable_pairJ ⊤

/-- The circle-average process of a coordinate vector `x`: the distributional circle version of the
distribution `LQGMetric.pairJInv ⊤ x` decoded by the Borel left inverse of the coordinate map (the zero
distribution off the range of `LQGMetric.pairJ ⊤`). -/
def coordCircleAverage (x : LQGMetric.CoordJ → ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  Sec1.distributionCircleVersion (LQGMetric.pairJInv ⊤ x) r z

/-- The circle-average process of a coordinate vector is jointly Borel in the coordinates, the radius and
the center. -/
theorem measurable_coordCircleAverage :
    Measurable fun p : (LQGMetric.CoordJ → ℝ) × ℝ × ℂ => coordCircleAverage p.1 p.2.1 p.2.2 := by
  have hinv : Measurable (LQGMetric.pairJInv ⊤ : (LQGMetric.CoordJ → ℝ) → LQGMetric.DistC) :=
    LQGMetric.measurable_pairJInv ⊤
  have hdec : Measurable fun p : (LQGMetric.CoordJ → ℝ) × ℝ × ℂ =>
      ((LQGMetric.pairJInv ⊤ p.1 : LQGMetric.DistC), p.2) :=
    (hinv.comp measurable_fst).prodMk measurable_snd
  have h := Sec1.measurable_distributionCircleVersion.comp hdec
  unfold coordCircleAverage
  exact h

/-- On the range of the coordinate map, the circle-average process of the coordinates is the
distributional circle version of the distribution itself. -/
theorem coordCircleAverage_pairJ (H : LQGMetric.DistC) :
    coordCircleAverage (LQGMetric.pairJ ⊤ H) = Sec1.distributionCircleVersion H := by
  funext r z
  simp only [coordCircleAverage, LQGMetric.pairJInv_pairJ]

/-- For any version `H` of the field of a valid mated-CRT environment, the circle-average process of the
coordinates `LQGMetric.pairJ ⊤ (H ω)` almost surely recovers the circle average of the field at every
positive radius and every center. -/
theorem MatedCRTEnv.IsValid.ae_coordCircleAverage_eq
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC}
    (hH : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∀ᵐ ω ∂S.P, ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      coordCircleAverage (LQGMetric.pairJ ⊤ (H ω)) r z = S.hcirc ω r z := by
  filter_upwards [Sec1.ae_distributionCircleVersion_eq hS hH] with ω hω r hr z
  rw [coordCircleAverage_pairJ]
  exact hω r hr z

end MatedCRT
