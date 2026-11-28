import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyLower
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyTails
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraLemmaTwoProof
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraBarrierProof
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraBarrierTube

/-!
# The occupation of a later cell in Shimura's argument

`shimuraOccupancy_holds`: the occupation bound of a later cell (`ShimuraOccupancy γ`, Shimura (4.2)–(4.7)) for
`0 < γ < 2`, from its upper bound (`occupancyUpper_holds`), its lower bound (`occupancyLower_holds`, with Shimura's
Lemma 2 for every angle, `shimuraLemmaTwo_of_barriers`, from the killed interval kernel near the lower barrier,
`killedBarrierPositive`, and the tube positivity of planar Brownian motion, `planarTubePositive`) and the tails of
the drops (`occupancyTails_holds`).
-/

set_option autoImplicit false

namespace MatedCRT.PeanosphereTriplePoints

/-- **The occupation of a later cell** (Shimura (4.2)–(4.7)) for the `γ`-correlated pair, `0 < γ < 2`. -/
theorem shimuraOccupancy_holds {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : ShimuraOccupancy γ :=
  shimuraOccupancy_of_steps (occupancyUpper_holds γ)
    (occupancyLower_holds hγ0 hγ2
      (shimuraLemmaTwo_of_barriers hγ0 hγ2 killedBarrierPositive planarTubePositive) planarTubePositive)
    (occupancyTails_holds γ)

end MatedCRT.PeanosphereTriplePoints
