import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.LQGSingularScaledLimit
import MatedCRT.FirstPass.Frozen.S2k

/-!
# The coordinate change rule of the γ-LQG measure of an insertion field, as a theorem

`FrozenInsertionCoordinateRule` (`FirstPass/Frozen/S2k.lean`): for `0 < γ < 2`, `α < Q_γ`, a whole-plane GFF `h^ℂ`
with γ-LQG measure `μ` of the field `h^ℂ - α log |·|`, and each fixed affine map `z ↦ a z + b` with `a ≠ 0`, almost
surely the push-forward of `μ` under `x ↦ (x - b)/a` is the γ-LQG limit of the regularized field
`ε, z ↦ (h^ℂ - α log |·|)_{|a| ε}(a z + b) + Q_γ log |a|` (Duplantier-Sheffield 2011, Proposition 2.1; the
LQG coordinate change rule for one fixed affine map).

The proof is `LatticeProb.LQG.LQGSingularScaledLimit.ae_isLQGLimit_affine_fieldCircleAverage`: almost surely, the
singular approximations of the field along the scales `|a| 2^{-k}` converge to `μ` (a Cauchy argument along the
scales from the scale-ratio increment bound), and the approximation measures of the affine field are push-forwards
of those approximations. The HB definitions match the library copies through `isWholePlaneGFF_iff`,
`isLQGMeasureOfField_iff` and `isLQGLimit_iff`; `lqgQ` and `fieldCircleAverage` agree by `rfl`.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory

/-- **The coordinate change rule for one affine map** (`FrozenInsertionCoordinateRule`) is a theorem. -/
theorem frozenInsertionCoordinateRule_holds : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule := by
  intro γ α hγ hγ2 hα Ω _ P hC hcirc μ _ hG hμ a ha b
  filter_upwards [LatticeProb.LQG.LQGSingularScaledLimit.ae_isLQGLimit_affine_fieldCircleAverage
    ((HarmonicBalls.LPBridge.isWholePlaneGFF_iff P hC hcirc).1 hG) hγ hγ2 hα
    ((HarmonicBalls.LPBridge.isLQGMeasureOfField_iff P γ α hcirc μ).1 hμ) ha b] with ω hω
  exact (HarmonicBalls.LPBridge.isLQGLimit_iff γ _ _).2 hω

end MatedCRT.FirstPass.Derived
