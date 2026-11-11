import MatedCRT.FirstPass.S2g.HalfBallGate
import MatedCRT.FirstPass.S2g.SourcePathwise
import MatedCRT.FirstPass.S2g.HalfBallFamily
import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime

/-!
# `ConeHarmonicBallLocalityStep` with `S = Set.univ` (fp-S2x-hM-univ-closure)

The locality Step `ConeHarmonicBallLocalityStep` (Steps/Sec2/ConeHarmonicBallsUpToFixedTime.lean) is proved with the
measurable set `S = Set.univ`, as in CHATGPT-223 (PRO), section 5, "Minimal current-repository closure". No analytic coding
input is used: the hypothesis `hA` of `coneHarmonicBallLocalityStep_of_borel` (ConeHarmonicBallLocalityBorel.lean) is
RETIRED, being false as typed (operator, chat 223).

With `S = univ` both clauses of the Step reduce to the almost sure existence of `HasConeHarmonicBallsUpToHalfBall (μ ω)`:
* quantum cone: `coneCanonicalHalfBallStep_of_draft` (FirstPass/S2g/HalfBallGate.lean) gives, almost surely, a family of
  harmonic balls stopped at `∂B_{1/2}` at the canonical time `halfBallTime (μ ω)`;
* whole-plane GFF, `h^ℂ - γ log |·|`: `sourceHalfBallPathwiseStep_of_draft` (FirstPass/S2g/SourcePathwise.lean) gives the
  pathwise inputs almost surely, and `ae_canonical_family_of_pathwise` (FirstPass/S2g/HalfBallFamily.lean) the stopped family.

This is not an independent, locality-based proof of Lemma 2.4 (the locality of HB22 Proposition 1.3 is not used).
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls

/-- A family of harmonic balls for `ν` on `(0, T)` with the properties of Theorem 2.3, stopped at `∂B_{1/2}`, gives the
event `HasConeHarmonicBallsUpToHalfBall ν` of Lemma 2.4 (with the time `T`). -/
theorem hasConeHarmonicBallsUpToHalfBall_of_family {ν : Measure ℂ} {T : ℝ} {Λ : ℝ → Set ℂ} (h0 : 0 < T)
    (hfam : IsConeHarmonicBallFamilyOn ν Λ T) (hstop : IsStoppedAtHalfBall Λ T) :
    HasConeHarmonicBallsUpToHalfBall ν := by
  unfold HasConeHarmonicBallsUpToHalfBall
  exact ⟨T, h0, Λ, hfam, hstop⟩

/-- **`ConeHarmonicBallLocalityStep` with `S = Set.univ` (fp-S2x-hM-univ-closure).** The Step holds without any analytic
coding input. Its hypotheses are those of `coneCanonicalHalfBallStep_of_draft`, which supply the cone clause, and the
whole-plane clause uses the same inputs through `sourceHalfBallPathwiseStep_of_draft`. -/
theorem coneHarmonicBallLocalityStep_of_univ
    (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hmeasT : FrozenLQGTestIntegralMeasurable) (hstd : CandidateConeLogLocalCodeLawStd)
    (hmin : FrozenSuperharmonicMinimumPrinciple) (hC : FrozenGreenBallCentre)
    (hGB : HarmonicBalls.GreenFunctionBallStmt) (hpole : FrozenGreenDiscPole)
    (hOpen : ClusterOpenLaplacianStmt.{0}) (hSup : LeastSupersolutionMemStmt.{0})
    (hCons : ClusterConservationOfMassStmt.{0}) (hMono : ClusterMonotoneStmt.{0})
    (hCompat : ClusterCompatibilityStmt.{0}) (hBdry : ClusterBoundaryMeasureZeroStmt.{0})
    (hExist : ExistenceHarmonicBallsStmt.{0}) (hThm11 : ExistenceUniquenessHarmonicBallsStmt.{0})
    (hProp56 : UniquenessHarmonicBallsStmt.{0})
    (hconf : FrozenHBInitialConfinement) :
    ConeHarmonicBallLocalityStep := by
  intro γ hγ0 hγ2
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · -- clause for the quantum cone: the canonical stopped family holds almost surely
    intro Ω _ P hC' hcirc μ hcone
    have hcan := coneCanonicalHalfBallStep_of_draft hU hmeasT hstd hmin hC hGB hpole hOpen hSup hCons hMono hCompat
      hBdry hExist hThm11 hProp56 hconf γ hγ0 hγ2 Ω P hC' hcirc μ hcone
    filter_upwards [hcan] with ω hω
    obtain ⟨Λ, h0, hfam, hstop⟩ := hω
    exact iff_of_true (hasConeHarmonicBallsUpToHalfBall_of_family h0 hfam hstop) (Set.mem_univ _)
  · -- clause for h^ℂ - γ log |·| (whole-plane GFF with its LQG measure)
    intro Ω _ P hC' hcirc μ hP hW hL
    have hpath := sourceHalfBallPathwiseStep_of_draft hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf
      γ hγ0 hγ2 Ω P hC' hcirc μ hP hW hL
    filter_upwards [ae_canonical_family_of_pathwise P μ hmin hC hGB hpole hpath] with ω hω
    obtain ⟨Λ, h0, hfam, hstop⟩ := hω
    exact iff_of_true (hasConeHarmonicBallsUpToHalfBall_of_family h0 hfam hstop) (Set.mem_univ _)

end MatedCRT
