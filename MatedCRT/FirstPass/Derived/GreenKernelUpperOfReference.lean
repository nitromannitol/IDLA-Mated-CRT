import MatedCRT.FirstPass.Derived.HarnackPairUnionBound
import MatedCRT.FirstPass.Derived.HarnackPairFromCoupling
import MatedCRT.FirstPass.Derived.HSingleOfReference
import MatedCRT.FirstPass.Derived.CellSizeOfConeCouplingProd

/-!
# The Green kernel upper bound (BG20 Lemma 5.4) in every valid environment, from a reference environment

Berestycki–Gwynne (2020), Lemma 5.4 (`GreenKernelUpperBoundStmt`). Let `ν` be a normalized space-filling SLE law of
the model `𝒮`, which has valid reference environments on the standard Borel space `ℝ` for every `γ ∈ (0, 2)`
(`HasReferenceEnvironments`), and `G` a one-sided mating-rigid set that is full for every `γ`-correlated two-sided
Brownian law. The wrapper `greenKernelUpperBoundStmt_of_pair_single_cellSize` takes

* the cell size estimate (Lemma 2.8, BG20 Lemma 2.4): `cellSizeEstimateStmt_holds`;
* the per-circle failure bounds of the itinerary events (3.21) and of the disconnection event (3.35) of Lemma 3.11:
  `hPair_of_reference`, applied with the model `𝒮` itself as reference model;
* the single-ball cell sum bound of Gwynne–Miller–Sheffield (2019), Proposition 2.9: `hsingle_of_reference`.

The result is `greenKernelUpperBoundStmt_of_reference`.
-/

set_option autoImplicit false

open MeasureTheory

namespace MatedCRT.FirstPass.Derived

/-- **The Green kernel upper bound** (Berestycki–Gwynne 2020, Lemma 5.4) for a space-filling SLE model `𝒮` with a
normalized space-filling SLE law `ν` and valid reference environments on `ℝ`, given a one-sided mating-rigid set `G`
that is full for every `γ`-correlated two-sided Brownian law. -/
theorem greenKernelUpperBoundStmt_of_reference {𝒮 : SpaceFillingSLEModel} {ν : ℝ → Measure SLEPathCode}
    (hν : HasNormalizedSLELaw 𝒮 ν) (href : HasReferenceEnvironments 𝒮)
    {G : Set MatedCRTHarmonic.MatedCRT.Path2}
    (hGnull : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ μ : Measure MatedCRTHarmonic.MatedCRT.Path2,
      MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ μ → μ Gᶜ = 0)
    (hG : MatingRigidLEOn G) :
    GreenKernelUpperBoundStmt 𝒮 :=
  greenKernelUpperBoundStmt_of_pair_single_cellSize (cellSizeEstimateStmt_holds 𝒮)
    (hPair_of_reference hν hν href hGnull hG) (hsingle_of_reference hν href hGnull hG)

end MatedCRT.FirstPass.Derived
