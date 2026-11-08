import MatedCRT.Proofs.Sec1.EnvironmentScaling.FieldAssembly

/-!
# Radial law of the represented cone

The valid environment contains a distribution-valued cone from Leonardo
Bonanno's post-last-zero construction.  Its recovered circles have the
weak-limit radial law already required by the environment.  This does not
identify those circles with the explicit radial formula: that is a separate
circle-average calculation, and no equivalence of conditioning conventions is
assumed here.  Compare env-steps.tex:217–250.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open HarmonicBalls

namespace MatedCRT.Sec1

/-- The explicit cone representative from the mating-of-trees witness has
both the field law and the weak-limit radial law of the valid environment.
The radial process here is recovered from the distribution; equality with the
post-last-zero formula is a separate assertion. -/
theorem exists_reference_cone_field_and_recovered_radial_law
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hHm : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∃ (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ)
      (ν : Measure (MarkovProcess.ContinuousPath ℝ)),
      LQGMetric.IsWholePlaneGFF X S.P ∧ IsBrownianReal B S.P ∧ IsBrownianReal B' S.P ∧
      IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P ∧
      IsBMConditionedPositive (lqgQ γ - γ) ν ∧
      let H' : Ω → LQGMetric.DistC := fun ω =>
        MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
      (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H' ω φ) ∧
      AEMeasurable H' S.P ∧ S.P.map H = S.P.map H' ∧
      S.P.map (fun ω => radialProcess (distributionCircleVersion (H' ω))) =
        quantumConeRadialLaw γ ν := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hc, ha⟩ := hS.matingOfTrees
  let H' : Ω → LQGMetric.DistC := fun ω =>
    MatedCRTHarmonic.MatedCRT.coneField (X ω)
      (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
  have href : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H' ω φ := by
    filter_upwards [ha] with ω hω
    exact hω.2
  have heq : H =ᵐ[S.P] H' := by
    filter_upwards [hrep, href] with ω hω hω'
    ext φ
    exact (hω φ).symm.trans (hω' φ)
  have hcircle := ae_distributionCircleVersion_eq hS href
  have hradial : (fun ω => radialProcess (distributionCircleVersion (H' ω))) =ᵐ[S.P]
      (fun ω => radialProcess (S.hcirc ω)) := by
    filter_upwards [hcircle] with ω hω
    apply Prod.ext <;> funext t <;>
      exact hω _ (Real.exp_pos _) 0
  obtain ⟨ν, hν, hνlaw⟩ := hS.isQuantumCone.radial_law
  refine ⟨X, B, B', ν, hc.gff, hc.bm_B, hc.bm_B', hc.indep_cone.1,
    hc.indep_cone.2, hν, href, hHm.aemeasurable.congr heq, Measure.map_congr heq, ?_⟩
  rw [Measure.map_congr hradial, hνlaw]

/-- The two radial branches of the reference cone.  The outer branch is
obtained from the drifted Brownian path after its last zero. -/
def referenceConeRadialPair (γ : ℝ) (b b' : ℝ≥0 → ℝ) :
    (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) :=
  let c : ℝ → ℝ := fun u => b' u.toNNReal +
    (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) * u
  let ℓ := MatedCRTHarmonic.MatedCRT.lastZeroR c
  (fun t => b t + γ * t, fun t => c (ℓ + t) - MatedCRTHarmonic.MatedCRT.lqgQ γ * t)

/-- At positive times the inner branch is exactly the corresponding branch
of Bonanno's radial process. -/
theorem referenceConeRadialPair_inner (γ : ℝ) (b b' : ℝ≥0 → ℝ) (t : ℝ≥0) :
    (referenceConeRadialPair γ b b').1 t =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ b b' t := by
  simp [referenceConeRadialPair, MatedCRTHarmonic.MatedCRT.coneRadial]

/-- At positive times the outer branch is the post-last-zero branch of
Bonanno's radial process. -/
theorem referenceConeRadialPair_outer (γ : ℝ) (b b' : ℝ≥0 → ℝ)
    (t : ℝ≥0) (ht : 0 < t) :
    (referenceConeRadialPair γ b b').2 t =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ b b' (-(t : ℝ)) := by
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  simp [referenceConeRadialPair, MatedCRTHarmonic.MatedCRT.coneRadial,
    not_le.mpr (neg_neg_of_pos ht'), sub_eq_add_neg]

/-- The remaining circle-average calculation for a reference cone.  Its
hypothesis is a simultaneous representation by that cone, and its conclusion
identifies the recovered circle process with the actual post-last-zero
formula.  This is an internal proof obligation, not a DMS hypothesis. -/
def ReferenceConeRadialCircleStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ (γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
    S.IsValid 𝒮 γ → ∀ (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ),
    LQGMetric.IsWholePlaneGFF X S.P → IsBrownianReal B S.P → IsBrownianReal B' S.P →
    IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P →
    IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P →
    (∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ =
      MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)) φ) →
    ∀ᵐ ω ∂S.P, radialProcess (distributionCircleVersion
      (MatedCRTHarmonic.MatedCRT.coneField (X ω)
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)))) =
      referenceConeRadialPair γ (fun t => B t ω) (fun t => B' t ω)

/-- Once the reference circles are calculated, the reference post-last-zero
radial pair has the weak-limit conditioned law from the environment. -/
theorem exists_reference_cone_postLastZero_radial_law
    {Ω : Type} [MeasurableSpace Ω] {𝒮 : SpaceFillingSLEModel}
    (hcircle : ReferenceConeRadialCircleStep 𝒮)
    {γ : ℝ} {S : MatedCRTEnv Ω} (hS : S.IsValid 𝒮 γ)
    {H : Ω → LQGMetric.DistC} (hHm : Measurable H)
    (hrep : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC, S.hC ω φ = H ω φ) :
    ∃ (X : Ω → LQGMetric.DistC) (B B' : ℝ≥0 → Ω → ℝ)
      (ν : Measure (MarkovProcess.ContinuousPath ℝ)),
      LQGMetric.IsWholePlaneGFF X S.P ∧ IsBrownianReal B S.P ∧ IsBrownianReal B' S.P ∧
      IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) S.P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) S.P ∧
      IsBMConditionedPositive (lqgQ γ - γ) ν ∧
      S.P.map (fun ω => referenceConeRadialPair γ (fun t => B t ω) (fun t => B' t ω)) =
        quantumConeRadialLaw γ ν := by
  obtain ⟨X, B, B', ν, hX, hB, hB', hi, hi', hν, href, _, _, hlaw⟩ :=
    exists_reference_cone_field_and_recovered_radial_law hS hHm hrep
  refine ⟨X, B, B', ν, hX, hB, hB', hi, hi', hν, ?_⟩
  have heq := hcircle γ Ω S hS X B B' hX hB hB' hi hi' href
  rw [← Measure.map_congr heq, hlaw]

end MatedCRT.Sec1
