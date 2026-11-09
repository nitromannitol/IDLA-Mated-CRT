import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionDirichletProjection
import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionLocalCircleRecovery
import MatedCRT.Proofs.Sec4.Prop42Closure.InsertionScalingLawAssembly

/-!
# Audit: the projection producer composed into the local Dirichlet components (steps3:600-628, 678-713)

Task `z1-steps3-local-decomposition-component-audit`. An exact-type composition with named residuals. It proves no Step
and claims no closure. The composed components are:

* the proved projection producer `MatedCRT.dirichletPairing_projection_gaussian_covariance`
  (`Proofs/Sec4/Prop42Closure/InsertionDirichletProjection.lean`), for the test-pairing observables;
* the circle recovery `MatedCRT.localDirichletHarmonicDecompositionStep_iff_coordinatewise`
  (`Proofs/Sec4/Prop42Closure/InsertionLocalCircleRecovery.lean:128`);
* the scaling consumer `MatedCRT.insertionLQGScalingLawStep_of_components`
  (`Proofs/Sec4/Prop42Closure/InsertionScalingLawAssembly.lean:50`).

The producer covers only pairings, while `IsDirichletGFF` also constrains the circle averages. The residual boundary is
therefore the explicit premise `DirichletProjectionRealization` (per whole-plane GFF and disk) and its universal form
`DirichletProjectionRealizationStep`. Its clauses are: the isonormal realization `IsIsonormalProcess` (the Gaussian
construction, not made here); the two pairing premises of the producer, `DirichletRieszIdentity` and
`DirichletProjectionGreenRealization`; the realization of the GFF observables by the isonormal process; the circle
covariances `hRcov` and the continuous modification `hRcont` of the projected circle averages; and the harmonic remainder
`H` with the coordinatewise identity (steps3:609-621).

Not used anywhere: independence of normalized pieces, finiteness of the zero-boundary limit, and any norm premise. The
literature input is the explicit hypothesis `SheffieldWangCircleAverageAllScaleInteriorStmt.{0}` of the existing consumer.

Credit: this file uses no Leonardo Bonanno declaration directly. The harmonic-balls interface it names,
`HarmonicBalls.GFFObservable` and `IsWholePlaneGFF`, is compared with his `LQGDimension`/`LQGMetric` interfaces in
`REUSE-LEO.md` (section 2), not reused from his code. Bonanno modules reached through the imports are credited in
`InsertionScalingLawAssembly.lean`.
-/

open MeasureTheory ProbabilityTheory HarmonicBalls Set Filter Topology
open scoped Classical

namespace MatedCRT

/-- The circle-average observables (`GFFObservable.circle`), as opposed to the test-function pairings. -/
def IsCircleAverageObs : GFFObservable → Prop
  | .pairing _ => False
  | .circle _ _ => True

/-- **Transfer to `IsDirichletGFF`.** Suppose each admissible observable is realized, almost surely and pointwise in `ω`,
by a family `G` (`o.eval (h ω) (hcirc ω) = G o ω`). Then the four clauses of `IsDirichletGFF` follow from the Gaussian,
centering and covariance statements for `G`, and from the continuity of `hcirc`. This is the structure's definition read
through `hev`; no mathematics is added. -/
theorem isDirichletGFF_of_eval_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Set ℂ}
    {h : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {G : GFFObservable → Ω → ℝ}
    (hev : ∀ (ω : Ω) (o : GFFObservable), IsDirichletGFFObservable D o → o.eval (h ω) (hcirc ω) = G o ω)
    (hgauss : IsGaussianProcess (fun o : DirichletGFFObservable D => fun ω => G o.1 ω) P)
    (hcent : ∀ o : GFFObservable, IsDirichletGFFObservable D o → ∫ ω, G o ω ∂P = 0)
    (hcov : ∀ o o' : GFFObservable, IsDirichletGFFObservable D o → IsDirichletGFFObservable D o' →
      cov[G o, G o'; P] = dirichletGFFCovariance D o o')
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2)
      {p : ℝ × ℂ | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ D}) :
    IsDirichletGFF P D h hcirc := by
  refine ⟨?_, ?_, ?_, hcont⟩
  · have e : (fun o : DirichletGFFObservable D => fun ω => o.1.eval (h ω) (hcirc ω)) =
        fun o : DirichletGFFObservable D => fun ω => G o.1 ω :=
      funext fun o => funext fun ω => hev ω o.1 o.2
    rw [e]
    exact hgauss
  · intro o ho
    have e : (fun ω => o.eval (h ω) (hcirc ω)) =ᵐ[P] fun ω => G o ω :=
      ae_of_all P fun ω => hev ω o ho
    exact (integral_congr_ae e).trans (hcent o ho)
  · intro o o' ho ho'
    rw [show (fun ω => o.eval (h ω) (hcirc ω)) = fun ω => G o ω from funext fun ω => hev ω o ho,
      show (fun ω => o'.eval (h ω) (hcirc ω)) = fun ω => G o' ω from funext fun ω => hev ω o' ho']
    exact hcov o o' ho ho'

/-- **Projected Dirichlet GFF (composition with the producer).** Let `X` be isonormal on `E`, and let `K` be the Dirichlet
subspace of the disk `D`, with the two pairing premises of the producer. The projected observables
`o ↦ X (K.starProjection (repO o))` realize `IsDirichletGFF` on `D`, with `h0 φ = X (P (repO (pairing φ)))` and
`hcirc0 r z = X (P (repO (circle r z)))` on admissible circles, and `0` on the others. The pairing covariance is the proved
producer's. The circle covariances `hRcov` and the continuous modification `hRcont` are residual premises. -/
theorem isDirichletGFF_of_projection {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : Measure Ω} {X : E → Ω → ℝ} {D : Set ℂ} {ev : E → ℂ → ℝ} {repO : GFFObservable → E}
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (hX : IsIsonormalProcess P X)
    (hR1 : DirichletRieszIdentity D ev (fun φ => repO (.pairing φ)) K)
    (hR2 : DirichletProjectionGreenRealization D ev (fun φ => repO (.pairing φ)) K)
    (hRcov : ∀ o o' : GFFObservable, IsDirichletGFFObservable D o → IsDirichletGFFObservable D o' →
      (IsCircleAverageObs o ∨ IsCircleAverageObs o') →
      cov[fun ω => X (K.starProjection (repO o)) ω, fun ω => X (K.starProjection (repO o')) ω; P] =
        dirichletGFFCovariance D o o')
    (hRcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => X (K.starProjection (repO (.circle p.1 p.2))) ω)
      {p : ℝ × ℂ | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ D}) :
    IsDirichletGFF P D (fun ω φ => X (K.starProjection (repO (.pairing φ))) ω)
      (fun ω r z => if Metric.closedBall z r ⊆ D then X (K.starProjection (repO (.circle r z))) ω else 0) := by
  refine isDirichletGFF_of_eval_eq (G := fun o ω => X (K.starProjection (repO o)) ω) ?_ ?_ ?_ ?_ ?_
  · intro ω o ho
    cases o with
    | pairing φ => rfl
    | circle r z =>
      have hball : Metric.closedBall z r ⊆ D := (show 0 < r ∧ Metric.closedBall z r ⊆ D from ho).2
      simp only [GFFObservable.eval, ite_eq_left hball]
  · exact hX.gaussian.comp_right (fun o : DirichletGFFObservable D => K.starProjection (repO o.1))
  · intro o _
    exact hX.centered (K.starProjection (repO o))
  · intro o o' ho ho'
    cases o with
    | pairing φ =>
      cases o' with
      | pairing ψ => exact (dirichletPairing_projection_gaussian_covariance K hX hR1 hR2).2.2 φ ψ ho ho'
      | circle r z => exact hRcov _ _ ho ho' (Or.inr trivial)
    | circle r z => exact hRcov _ _ ho ho' (Or.inl trivial)
  · refine hRcont.mono fun ω hω => hω.congr fun p hp => ?_
    exact ite_eq_left (show 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ D from hp).2

/-- **Projection realization of one whole-plane GFF on one disk: the residual premise** (steps3:603-625). Let `(hC, hcirc)`
be a whole-plane GFF on `Ω`, let `repO` be the representatives of the observables in the energy space `E`, let `ev` be the
Dirichlet-function map, and let `K D` be the Dirichlet subspace of `D`. Then there are an isonormal process `X` on `E` and a
harmonic remainder `H` such that: `X` realizes the admissible observables of `(hC, hcirc)`; the Riesz identity and the
projection-Green realization hold for the pairings (the producer's named premises); the projected circle covariances and the
continuous modification of the projected circle averages hold; and `H` is a.s. harmonic on `D` with
`hcirc ω r z = X (P rep(circle r z)) ω + H ω z` on admissible circles. None of these is proved here. -/
def DirichletProjectionRealization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (repO : GFFObservable → E) (ev : E → ℂ → ℝ) (K : Set ℂ → Submodule ℝ E)
    [∀ D : Set ℂ, (K D).HasOrthogonalProjection] (c : ℂ) (ρ : ℝ) : Prop :=
  ∃ (X : E → Ω → ℝ) (H : Ω → ℂ → ℝ),
    IsIsonormalProcess P X ∧
    DirichletRieszIdentity (Metric.ball c ρ) ev (fun φ => repO (.pairing φ)) (K (Metric.ball c ρ)) ∧
    DirichletProjectionGreenRealization (Metric.ball c ρ) ev (fun φ => repO (.pairing φ)) (K (Metric.ball c ρ)) ∧
    (∀ o : GFFObservable, IsDirichletGFFObservable (Metric.ball c ρ) o →
      ∀ᵐ ω ∂P, X (repO o) ω = o.eval (hC ω) (hcirc ω)) ∧
    (∀ o o' : GFFObservable, IsDirichletGFFObservable (Metric.ball c ρ) o →
      IsDirichletGFFObservable (Metric.ball c ρ) o' → (IsCircleAverageObs o ∨ IsCircleAverageObs o') →
      cov[fun ω => X ((K (Metric.ball c ρ)).starProjection (repO o)) ω,
        fun ω => X ((K (Metric.ball c ρ)).starProjection (repO o')) ω; P] =
        dirichletGFFCovariance (Metric.ball c ρ) o o') ∧
    (∀ᵐ ω ∂P, ContinuousOn
      (fun p : ℝ × ℂ => X ((K (Metric.ball c ρ)).starProjection (repO (.circle p.1 p.2))) ω)
      {p : ℝ × ℂ | 0 < p.1 ∧ Metric.closedBall p.2 p.1 ⊆ Metric.ball c ρ}) ∧
    (∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω)) ∧
    ∀ (r : ℝ) (z : ℂ), 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ →
      ∀ᵐ ω ∂P, hcirc ω r z = X ((K (Metric.ball c ρ)).starProjection (repO (.circle r z))) ω + H ω z

/-- **Projection realization for all whole-plane GFFs and disks: the residual premise of the local Dirichlet step.** It is
`LocalDirichletCoordinatewiseStep` with the Gaussian projection data made explicit as `DirichletProjectionRealization`. -/
def DirichletProjectionRealizationStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (repO : GFFObservable → E) (ev : E → ℂ → ℝ) (K : Set ℂ → Submodule ℝ E)
    [∀ D : Set ℂ, (K D).HasOrthogonalProjection] : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ ({0}ᶜ : Set ℂ) →
      DirichletProjectionRealization P hC hcirc repO ev K c ρ

/-- **Coordinatewise producer from the projection realization.** The proved projection covariance enters through
`isDirichletGFF_of_projection`; the remaining clauses are the named residuals. -/
theorem localDirichletCoordinatewiseStep_of_projectionRealization {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {repO : GFFObservable → E} {ev : E → ℂ → ℝ} {K : Set ℂ → Submodule ℝ E}
    [∀ D : Set ℂ, (K D).HasOrthogonalProjection] (hReal : DirichletProjectionRealizationStep repO ev K) :
    LocalDirichletCoordinatewiseStep := by
  intro Ω _ P _ hC hcirc hGFF c ρ hρ hsub
  obtain ⟨X, H, hX, hR1, hR2, _, hRcov, hRcont, hHarm, hcoord⟩ :=
    hReal Ω P hC hcirc hGFF c ρ hρ hsub
  refine ⟨fun ω φ => X ((K (Metric.ball c ρ)).starProjection (repO (.pairing φ))) ω,
    fun ω r z => if Metric.closedBall z r ⊆ Metric.ball c ρ then
      X ((K (Metric.ball c ρ)).starProjection (repO (.circle r z))) ω else 0, H, ?_, ?_, hHarm, ?_⟩
  · exact isDirichletGFF_of_projection (K (Metric.ball c ρ)) hX hR1 hR2 hRcov hRcont
  · intro ω r z hz
    simp only [ite_eq_right hz]
  · intro r z hr hball
    filter_upwards [hcoord r z hr hball] with ω hω
    simp only [ite_eq_left hball]
    exact hω

/-- **Insertion scaling Step from the projection realization.** The Sheffield-Wang input and the projection realization give
the scaling Step `InsertionLQGScalingLawStep`, through the circle recovery iff and `insertionLQGScalingLawStep_of_components`.
This is a conditional component, not a closure of Proposition 4.2. -/
theorem insertionLQGScalingLawStep_of_projectionRealization {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {repO : GFFObservable → E} {ev : E → ℂ → ℝ} {K : Set ℂ → Submodule ℝ E}
    [∀ D : Set ℂ, (K D).HasOrthogonalProjection]
    (hSWI : SheffieldWangCircleAverageAllScaleInteriorStmt.{0})
    (hReal : DirichletProjectionRealizationStep repO ev K) : InsertionLQGScalingLawStep :=
  insertionLQGScalingLawStep_of_components hSWI
    (localDirichletHarmonicDecompositionStep_iff_coordinatewise.mpr
      (localDirichletCoordinatewiseStep_of_projectionRealization hReal))

/-- **Exact consumer component.** The scaling Step follows from the Sheffield-Wang input and the coordinatewise producer
residual `LocalDirichletCoordinatewiseStep`, through the circle recovery iff and the existing consumer. -/
theorem check_insertionLQGScalingLawStep_of_coordinatewise :
    SheffieldWangCircleAverageAllScaleInteriorStmt.{0} → LocalDirichletCoordinatewiseStep →
      InsertionLQGScalingLawStep :=
  fun hSWI hCW => insertionLQGScalingLawStep_of_components hSWI
    (localDirichletHarmonicDecompositionStep_iff_coordinatewise.mpr hCW)

end MatedCRT

#print axioms MatedCRT.isDirichletGFF_of_projection
#print axioms MatedCRT.localDirichletCoordinatewiseStep_of_projectionRealization
#print axioms MatedCRT.insertionLQGScalingLawStep_of_projectionRealization
#print axioms MatedCRT.check_insertionLQGScalingLawStep_of_coordinatewise
