import MatedCRT.FirstPass.Closure.LssDerived
import MatedCRT.FirstPass.Closure.HSCDerived

/-!
# Proposition 5.1 without the cluster strong compatibility binder

The counted form `MatedCRT.FirstPassClosure.closed_5_1_lp_noSup` (`MatedCRT/FirstPass/Closure/LssDerived.lean`) of
Proposition 5.1 (lower bound for internal DLA) binds both `hI2 : LQGVolumeGrowthAllScalesStmt` and
`hSC : ClusterStrongCompatibilityStmt` (Lemma 5.8 of the Harmonic-Balls paper, for every bounded open set). The second
follows from the first: `MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`
(`MatedCRT/FirstPass/Closure/HSCDerived.lean`), by exhaustion with Green-regular domains. The wrapper
`closed_5_1_lp_noSup_noSC` has the binders of `closed_5_1_lp_noSup` without `hSC`, in the same order, and the same
conclusion. Theorems 1.4 and 1.6 are treated in the same way in `MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean`.
-/

namespace MatedCRT.FirstPassClosure

open MeasureTheory Set
open _root_.HarmonicBalls

/-- **Proposition 5.1 (lower bound for internal DLA)** in its counted form `closed_5_1_lp_noSup`, with the cluster
strong compatibility `hSC` (Lemma 5.8 of the Harmonic-Balls paper) derived from the volume growth `hI2`
(`MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth`). -/
theorem closed_5_1_lp_noSup_noSC
    {𝒮 : SpaceFillingSLEModel}
    (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (h27 : VolumeGrowthStmt)
    (hmodel : FPWholePlaneLQGModel)
    (hFL : FPConeWholePlaneFieldLaw)
    (hstd : FrozenConeLogLocalCodeLawStd)
    (hGBC : FrozenGreenBallCentre)
    (hconf : FrozenHBInitialConfinement)
    (hK : MatedCRT.FirstPass.S2k.FrozenInsertionCoordinateRule)
    (hE : MatedCRT.FirstPass.S2m.FrozenLQGMeasureExistenceInsertion)
    (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep)
    (hscale : QuantumConeScalingInput)
    (hND : LQGMeasureNonDyadicDilationPart)
    (hcanon : FrozenBG20GreenCrudeCanonical 𝒮)
    (h32 : ClusterOpenLaplacianStmt.{0})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{0})
    (h82 : TypicalPointManyGoodScalesStmt.{0})
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0})
    (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0})
    (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hEx : ExistenceHarmonicBallsStmt.{0})
    (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0})
    (hBG : FrozenBerestyckiGwynneConeBallMass) :
    IDLALowerBoundStmt 𝒮 :=
  closed_5_1_lp_noSup (𝒮 := 𝒮) (ν := ν)
    (hC := hC) (h27 := h27) (hmodel := hmodel) (hFL := hFL) (hstd := hstd) (hGBC := hGBC) (hconf := hconf)
    (hK := hK) (hE := hE) (hE1 := hE1) (hE2 := hE2) (hscale := hscale) (hND := hND) (hcanon := hcanon) (h32 := h32)
    (h611 := h611) (h82 := h82) (hI2 := hI2) (hSup := hSup) (hCons := hCons) (hMono := hMono) (hCompat := hCompat)
    (hBdry := hBdry) (hEx := hEx) (hThm11 := hThm11) (hProp56 := hProp56) (hloc := hloc) (hBG := hBG)
    (hSC := MatedCRT.frozenClusterStrongCompatibility_of_volumeGrowth hI2)

end MatedCRT.FirstPassClosure
