import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyProof
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraCellBoundsProof
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSummationProof
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraLocalization
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.PeanosphereTriplePointsProof

/-!
# The triple points of Peanosphere curves of the correlated Brownian pair contain no continuum

`correlatedBMPeanosphereTriplePointsNoContinuum_holds : GMS310Transfer.CorrelatedBMPeanosphereTriplePointsNoContinuum`:
for almost every `γ`-correlated Brownian pair, `0 < γ < 2`, the points visited at least three times by any
Peanosphere curve of the pair contain no continuum of positive diameter. It follows from Shimura's theorem for the
pair in both orders (`correlatedBMPeanosphereTriplePointsNoContinuum_of_shimuraSteps`), whose four steps are proved:
the localization (`shimuraLocalization_holds`), the summation (`shimuraSummation_holds`), the bound for a cell
(`shimuraCellBounds_holds`) and the occupation of a later cell (`shimuraOccupancy_holds`).
-/

set_option autoImplicit false

namespace MatedCRT.PeanosphereTriplePoints

/-- **The triple points of the Peanosphere curves of the correlated Brownian pair contain no continuum**
(`GMS310Transfer.CorrelatedBMPeanosphereTriplePointsNoContinuum`), from Shimura's theorem for the pair. -/
theorem correlatedBMPeanosphereTriplePointsNoContinuum_holds :
    GMS310Transfer.CorrelatedBMPeanosphereTriplePointsNoContinuum :=
  correlatedBMPeanosphereTriplePointsNoContinuum_of_shimuraSteps fun γ hγ0 hγ2 =>
    ⟨shimuraLocalization_holds γ, shimuraSummation_holds γ, shimuraCellBounds_holds γ,
      shimuraOccupancy_holds hγ0 hγ2⟩

end MatedCRT.PeanosphereTriplePoints
