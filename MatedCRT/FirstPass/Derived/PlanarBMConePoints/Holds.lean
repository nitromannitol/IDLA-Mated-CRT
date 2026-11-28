import MatedCRT.FirstPass.Derived.PlanarBMConePoints.NoConePoints
import MatedCRT.FirstPass.Derived.MatingOfTreesCellSideInputsProof

/-!
# The cone-point input of the cell-side identity is proved

`PlanarBMNoTwoSidedConePoints` (`MatingOfTreesCellSideInputsProof.lean`), the statement of Le Gall,
*Some properties of planar Brownian motion*, Chapter III, Theorem 3(i), that planar Brownian motion
has no two-sided cone points of angle less than `π`, holds
(`planarBMNoTwoSidedConePoints`, from `PlanarBMConePoints.noTwoSidedConePoints`). Hence a
correlated Brownian pair has no common local minimum of its coordinates
(`correlatedBMNoCommonLocalMin_holds`), and the cell-side identity follows from the statement on
the triple points of the space-filling SLE traversal alone
(`matingOfTreesCellSideIdentity_of_triplePoints`).
-/

set_option autoImplicit false

namespace MatedCRT

/-- **Planar Brownian motion has no two-sided cone points of angle less than `π`** (Le Gall,
*Some properties of planar Brownian motion*, Chapter III, Theorem 3(i)). -/
theorem planarBMNoTwoSidedConePoints : PlanarBMNoTwoSidedConePoints :=
  fun _ hμ => PlanarBMConePoints.noTwoSidedConePoints hμ

/-- A `γ`-correlated two-sided Brownian pair, `0 < γ < 2`, almost surely has no time which is a
local minimum of both coordinates. -/
theorem correlatedBMNoCommonLocalMin_holds : CorrelatedBMNoCommonLocalMin :=
  correlatedBMNoCommonLocalMin planarBMNoTwoSidedConePoints

/-- The cell-side identity from the statement on the triple points of the space-filling SLE
traversal alone. -/
theorem matingOfTreesCellSideIdentity_of_triplePoints {𝒮 : SpaceFillingSLEModel}
    (hA : CorrelatedBMTraversalTriplePointsNoContinuum) : MatingOfTreesCellSideIdentity 𝒮 :=
  matingOfTreesCellSideIdentity_of_literature planarBMNoTwoSidedConePoints hA

end MatedCRT
