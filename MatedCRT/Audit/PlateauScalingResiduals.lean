import MatedCRT.Proofs.Sec4.Prop42Closure.PlateauScalingAssembly
import MatedCRT.Proofs.Sec4.Prop42Closure.Assembly
import MatedCRT.Proofs.Sec1.EnvironmentScaling.FieldCircleScaling
import MatedCRT.Proposed.DuplantierSheffieldCoordinate2011

/-! # Residual audit of the plateau-scale assembly and of the Proposition 4.2 consumers

Task `z5-plateau-scaling-residual-audit`. Audit only. Every declaration here is an exact-type check, a conditional
consumer that takes each unresolved Step as an explicit argument, an axiom print, or a source-preparation check.
Nothing here closes a numbered result, proves a named Step, or adds a literature input.

## Named residuals (hypotheses, never proved or assumed in this file)

* Scaling gap K, `MatedCRT.Proposed.DS11CoordinateRuleFixedAffine` (= `InsertionCoordinateExtensionStep`):
  `WPN-42-insertion-coordinate-extension`, `docs/campaign/GAPS-TAKEOVER-20261108.md:288`. An OPEN INTERNAL EXTENSION of
  DS11 Prop. 2.1 (p. 13): the printed rule has no whole-plane field and no non-dyadic scales `|a| ∉ 2^ℤ`.
* Scaling gap H, `MatedCRT.ScaledBoundedRepresentativesStep`: `WPN-42-scaled-representatives`, GAPS:244. Its quantifier is
  over all `μ : Measure ℂ` and all `Λ` with `IsSubharmonicBall μ Λ 0` and `Bornology.IsBounded Λ` (the repaired form,
  steps3:319; the unbounded form is false, steps3:117-137). It is wider than the LQG measures the consumer applies it to;
  no ambient hypothesis on `μ` is added.
* The nine WPN of the 14:40 operator entry: WPN-36-uniform-cell (`UniformCellSizeUpperStep`), WPN-36-pointwise-event
  (`PointwiseCellAnnulusEnvelopeStep`), WPN-36-pointwise-rates (`PointwiseSameWalkRatesStep`), WPN-42-locality
  (`LQGMeasureLocalityFunctionalStep`), WPN-51-origin (`ConeOriginNullMeasurableStep`), WPN-51-pole
  (`StoppedInterior.StoppedSurplusPoleStep`), WPN-51-geometry (`StoppedInterior.StoppedInteriorGeometryStep`),
  WPN-51-margin (`StoppedInterior.StoppedInteriorMeasurableStep`), WPN-51-layer (`StoppedLayerPotentialStep`).
  Written proofs audited by the 16:25 operator entry: uniform-cell, locality, origin and geometry CORRECT as declared;
  pointwise-event and margin: the declared Steps are false, and the audited repaired forms are the ones to route;
  pointwise-rates, pole and layer not yet returned.
  None is routed into Lean by this file.
* Strict obstacle gap, `MatedCRT.HarmonicBallStrictObstacleGapStep 𝒮` (`DivSandpileLowerBound/Final.lean:32`): the only
  Proposition-4.2-specific hypothesis of `divSandpileLowerBound_prop42` (`Prop42Closure/Assembly.lean`). It is not an input of
  the cone-closure reduction.

## Source-preparation findings (corrections to the owned statements; no Proposed file is edited here)

* F1, Dirichlet normalization. DS11 p. 4 prints `(f₁, f₂)∇ := (2π)⁻¹ ∫_D ∇f₁(z)·∇f₂(z) dz` (checked on the rendered
  page image), and says that with this factor the two-point covariance is `-log|z - w|` rather than `-(2π)⁻¹ log|z - w|`.
  The `(2π)` in the header of `Proposed/DuplantierSheffieldCoordinate2011.lean` (line 14) drops the exponent. The carrier
  `MatedCRT.IsDirichletGFF` (covariance `2π · greenFunction`, `greenFunction` normalized by `-ΔG = δ`) and clause (iii) of the
  B1 prose agree with `(2π)⁻¹`.
* F2, the B1 circle coupling carries an extra Jacobian. The Lean affine test rule is
  `LQGMetric.CircleAvg.affTest r z φ = (r ^ 2)⁻¹ • testAffinePull r z φ` with `testAffinePull r z φ = φ ∘ affMap r z` and
  `LQGMetric.affMap r z x = r⁻¹ • (x + -z)` (printed below). For `ψ(w) = r w + z`, this is the density of the push-forward
  `ψ_*(φ dw)`: the factor `(r ^ 2)⁻¹ = |(ψ⁻¹)'|²` is the change-of-variables factor that the push-forward already contains.
  So for a measure `ν` on `D̃`, `(h ∘ ψ, ν) = (h, ψ_* ν)`, and the circle average coupling is
  `hν ω (Measure.map ψ σ_{z,r})` with normalized arc length `σ_{z,r}` and no weight. The B1 test rule
  `(h ∘ ψ, |ψ′|² · (ρ ∘ ψ)) = (h, ρ)` agrees with this; the B1 measure rule `(h ∘ ψ, ν) = (h, ψ_*(|ψ′|² ν))` does not, since
  the two differ by `|ψ′|² = r²` for an affine dilation. No replacement coupling is proposed here.
* F3, DS11 Prop. 1.1 scope (p. 5). The printed statement asserts weak convergence inside `D` to the limit `e^{γh} dz`.
  `DS11IsLQGLimitInside` also requires `IsLocallyFiniteMeasure m` on all of `ℂ`, which additionally asks finiteness on compact
  sets meeting `∂D`. With `h₀` only `ContinuousOn D`, that is a strengthening. Section 5 expresses the printed local finiteness
  on `D` and proves that the global carrier implies it.
* F4, provenance. `WholePlaneLQGModelStep` (B2; `Proofs/Sec4/Prop42Closure/ConeWholePlaneSteps.lean:57`) is an existence
  input sourced to Harmonic-Balls `LQGMeasureExistence` and `MatedCRT/Proposed/Berestycki2017.lean`. Its Prop is not in
  `MatedCRT/External` (flagged for the operator, not moved). `ConeWholePlaneFieldLawStep` (IDLA eq. (2.4)) is likewise not in
  External.

Nothing in F1-F4 is a numbered closure; each is a residual for the operator. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric ProbabilityTheory
open _root_.HarmonicBalls
open scoped Pointwise ENNReal

namespace PlateauScalingResiduals

/-! ## 1. Exact types of the exported theorems, checked against their Steps -/

/-- The exported plateau-scale theorem. Its conclusion is the plateau-scale Step `PlateauScaleInvarianceStep` itself, and its
arguments are, in this order: I2 (cited), the scaling gap K and the scaling gap H. -/
theorem check_plateauScaleInvarianceStep_assembled :
    LQGVolumeGrowthAllScalesStmt.{0} → MatedCRT.Proposed.DS11CoordinateRuleFixedAffine →
      ScaledBoundedRepresentativesStep → PlateauScaleInvarianceStep :=
  plateauScaleInvarianceStep_assembled

/-- The plateau-scale theorem on the canonical event: I2, the insertion law (input K, as `InsertionLQGScalingLawStep`) and
the dilated regularized family (input H, as `ScaledRegularizedFamilyStep`). -/
theorem check_plateauScaleInvarianceStep_of_canonical :
    LQGVolumeGrowthAllScalesStmt.{0} → InsertionLQGScalingLawStep → ScaledRegularizedFamilyStep →
      PlateauScaleInvarianceStep :=
  plateauScaleInvarianceStep_of_canonical

/-- The insertion scaling law from the coordinate extension K. -/
theorem check_insertionLQGScalingLawStep_of_coordinateRule :
    MatedCRT.Proposed.InsertionCoordinateExtensionStep → InsertionLQGScalingLawStep :=
  insertionLQGScalingLawStep_of_coordinateRule

/-- The dilated regularized family from the bounded representatives H. -/
theorem check_scaledRegularizedFamilyStep_of_representatives :
    ScaledBoundedRepresentativesStep → ScaledRegularizedFamilyStep :=
  scaledRegularizedFamilyStep_of_representatives

/-- B1 (whole-plane volume growth) from I2. -/
theorem check_wholePlaneVolumeGrowthAeStep_of_allScales :
    LQGVolumeGrowthAllScalesStmt.{0} → WholePlaneVolumeGrowthAeStep :=
  wholePlaneVolumeGrowthAeStep_of_allScales

/-- The half-ball/plateau reduction, with the plateau Step as input `hfact1`. -/
theorem check_coneHalfBallClosureInsideStep_of_inputs :
    HarmonicBallLocalSetStmt.{0} → ExistenceHarmonicBallsStmt.{0} → ClusterStrongCompatibilityStmt.{0} →
      PlateauScaleInvarianceStep → VolumeGrowthStmt → WholePlaneVolumeGrowthAeStep → WholePlaneLQGModelStep →
      ConeWholePlaneFieldLawStep → LQGMeasureLocalityFunctionalStep → ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_of_inputs

/-- The exported cone-closure consumer, with the same arguments in the same order as `cone_closure_conditional` below. -/
theorem check_coneHalfBallClosureInsideStep_assembled :
    LQGVolumeGrowthAllScalesStmt.{0} → MatedCRT.Proposed.DS11CoordinateRuleFixedAffine →
      ScaledBoundedRepresentativesStep → HarmonicBallLocalSetStmt.{0} → ExistenceHarmonicBallsStmt.{0} →
      ClusterStrongCompatibilityStmt.{0} → VolumeGrowthStmt → WholePlaneLQGModelStep →
      ConeWholePlaneFieldLawStep → LQGMeasureLocalityFunctionalStep → ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_assembled

/-! ## 2. The conditional consumer, each argument named by its status -/

/-- **The residual conditional consumer of `ConeHalfBallClosureInsideStep`.** The arguments, in order, are:

* cited input I2, the Harmonic-Balls volume growth of every whole-plane LQG measure on every ball (`hI2`);
* cited Harmonic-Balls statements `hloc`, `hEx`, `hSC` (Draft Sections 1 and 5), and cited IDLA Lemma 2.7 `hVG`;
* cited fact `hB2` (existence of the whole-plane LQG measure, flag F4) and cited IDLA eq. (2.4) `hFL`;
* unresolved internal Steps, each a named Prop: the scaling gap K `hDS` (`WPN-42-insertion-coordinate-extension`), the
  scaling gap H `hrep` (`WPN-42-scaled-representatives`), and the locality Step `hLoc` (`WPN-42-locality`).

`HarmonicBallStrictObstacleGapStep` is not an argument: the cone-closure route does not use the strict obstacle gap. -/
theorem cone_closure_conditional
    (hI2 : LQGVolumeGrowthAllScalesStmt.{0})
    (hloc : HarmonicBallLocalSetStmt.{0}) (hEx : ExistenceHarmonicBallsStmt.{0})
    (hSC : ClusterStrongCompatibilityStmt.{0}) (hVG : VolumeGrowthStmt)
    (hB2 : WholePlaneLQGModelStep) (hFL : ConeWholePlaneFieldLawStep)
    (hDS : MatedCRT.Proposed.DS11CoordinateRuleFixedAffine)
    (hrep : ScaledBoundedRepresentativesStep)
    (hLoc : LQGMeasureLocalityFunctionalStep) :
    ConeHalfBallClosureInsideStep :=
  coneHalfBallClosureInsideStep_assembled hI2 hDS hrep hloc hEx hSC hVG hB2 hFL hLoc

/-! ## 3. Universe and applicability of I2 to both field laws -/

/-- I2 at universe `0` (so `Ω : Type`, the universe of `PlateauScaleInvarianceStep`) applies to the field law `(hWP, hLQG)` of
the LQG measure `μ` and to the field law `(hWP'', hLQG'')` of the scaled measure `μ''` produced by input K. Both
applications use the same `Ω`, `P`, insertion `α`, and the same `ae_isLocallyFiniteMeasure_volumeGrowth` at `α < lqgQ γ`. -/
example (hI2 : LQGVolumeGrowthAllScalesStmt.{0}) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC'' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc'' : Ω → ℝ → ℂ → ℝ} {μ μ'' : Ω → Measure ℂ}
    (hWP : IsWholePlaneGFF P hC hcirc) (hLQG : IsLQGMeasureOfField P γ α hcirc μ)
    (hWP'' : IsWholePlaneGFF P hC'' hcirc'') (hLQG'' : IsLQGMeasureOfField P γ α hcirc'' μ'') : True := by
  have _h := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hWP hLQG
  have _h'' := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hWP'' hLQG''
  trivial

/-! ## 4. Not hidden and not literature: the two scaling gaps are named Props -/

-- The two scaling gaps are `def`s whose bodies are printed here (no `axiom`, no `External` declaration).
#print MatedCRT.Proposed.InsertionCoordinateExtensionStep
#print MatedCRT.ScaledBoundedRepresentativesStep

/-! ## 5. Source-preparation check (F3): local finiteness on `D` is what the printed scope needs -/

/-- The printed scope of DS11 Prop. 1.1 (p. 5): the limit `m` is finite on every compact subset of `D`, where the printed
text asserts convergence ("converge weakly inside `D`"). -/
def DS11LocallyFiniteOnD (D : Set ℂ) (m : Measure ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ D → m K < ⊤

/-- The global carrier `DS11IsLQGLimitInside` implies the printed local finiteness on `D`. The converse is not stated by the
printed text: the global carrier also asks `m K < ⊤` for compact `K` that meet `∂D`, which the printed text does not assert
and which can fail when `h₀` is only continuous on `D`. -/
theorem ds11_global_carrier_gives_local_on_D {D : Set ℂ} {γ : ℝ} {hε : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (h : MatedCRT.Proposed.DS11IsLQGLimitInside D γ hε m) : DS11LocallyFiniteOnD D m := by
  intro K hK _
  have _hfin := h.isLocallyFiniteMeasure
  exact hK.measure_lt_top

/-! ## 6. Source-preparation check (F2): the affine test rule carries the inverse Jacobian -/

-- The affine test rule and the affine map, as they are defined in the lattice-probability package.
#print LQGMetric.CircleAvg.affTest
#print LQGMetric.affMap

/-! ## 7. Printed types and axioms -/

#check @plateauScaleInvarianceStep_assembled
#check @coneHalfBallClosureInsideStep_assembled
#check @MatedCRT.divSandpileLowerBound_prop42
#check @MatedCRT.discreteClusterInnerBound_prop42
#check @cone_closure_conditional
#check @LQGVolumeGrowthAllScalesStmt
#check @ae_isLocallyFiniteMeasure_volumeGrowth

#print axioms MatedCRT.wholePlaneVolumeGrowthAeStep_of_allScales
#print axioms MatedCRT.insertionLQGScalingLawStep_of_coordinateRule
#print axioms MatedCRT.scaledRegularizedFamilyStep_of_representatives
#print axioms MatedCRT.plateauScaleInvarianceStep_of_canonical
#print axioms MatedCRT.plateauScaleInvarianceStep_assembled
#print axioms MatedCRT.coneHalfBallClosureInsideStep_assembled
#print axioms MatedCRT.divSandpileLowerBound_prop42
#print axioms MatedCRT.discreteClusterInnerBound_prop42
#print axioms cone_closure_conditional
#print axioms ds11_global_carrier_gives_local_on_D

end PlateauScalingResiduals

end MatedCRT
