import MatedCRT.Proofs.Sec1.EnvironmentScaling.CanonicalReferenceObservableLaw
import MatedCRT.Proofs.Sec1.EnvironmentScaling.ConeObservableIntegrability

/-!
# Integrable reference observables of the actual cone

Assembly of the concrete reference observable law (`CanonicalReferenceObservableLaw.lean`) with the actual radial and
angular integral finiteness (`ConeObservableIntegrability.lean`), for the actual cone `IsQuantumCone`.

Index. The statements hold for an arbitrary family `o : ι → GFFObservable.Admissible` with `ι : Type`. The finite family is
`ι = Fin n` and the countable family is `ι = ℕ`; the proofs use the product σ-algebra only.

Results.
* `ae_observable_radialIntegrable_of_isQuantumCone`: one `P`-almost sure event on which every admissible observable has
  finite radial integrals (`ObservableRadialIntegrable`): the test pairings are integrable and the circle angular integrands
  are interval integrable. Only the cone `IsQuantumCone` is used.
* `aemeasurable_lateralProcess_of_isQuantumCone`, `aemeasurable_coneObservables_of_isQuantumCone`: the lateral process and
  the observable vector of any index family are `P`-a.e. measurable. No measurability of the observables is assumed.
* `ae_coneObservables_eq_transport_of_isQuantumCone`: almost surely, for all admissible `o` at once,
  `o(h) = coneTransport (radialProcess h, lateralProcess h) o`.
* `map_coneObservables_index_eq_reference_assembly`: given the reference conditioned law `hF` and an explicit whole-plane
  lateral witness `(P', hW, hlat)`, the four conjuncts: integrability, a.e. measurability, recovery and the joint law.
* `map_coneObservables_index_eq_reference_witness_assembly`: the same, with the cone's own lateral witness, existential as in
  the lateral clause `IsQuantumCone.lateral_law`.
* `map_coneObservables_index_eq_brownian_assembly`: the reference law produced from a Brownian motion `B`, with the DMS
  Remark 4.4 input `MatedCRT.Proposed.DMS14Remark44PostLastZeroLaw` displayed as a premise.

Premises kept explicit, not discharged. `hF : IsBMConditionedPositive (lqgQ γ - γ) (P0.map F)` is the reference conditioned
positive law; it is the WPN-53 bridge recorded in `docs/campaign/EnvironmentScaling.md`, and it is not proved here.
`hR : DMS14Remark44PostLastZeroLaw` is the held DMS Remark 4.4 input, used only in the Brownian version; it is not promoted
to a source.

Not claimed. No distribution-valued realization of the cone, no continuity of the lateral circle process in `(r, z)` beyond
the cone's own `ae_continuousOn_circle` clause, no environment-scaling or transport closure, and no numbered result. The
assemblies below are conditional on the explicit premises and are not numbered closures.

Credit. Through `CanonicalReferenceObservableLaw` (which imports `Field.lean`) and `ConeObservableIntegrability` (which
imports `CanonicalLateralLawAssembly`, which imports `Field.lean`), this file uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg` (imported at `Field.lean`, line 2). No declaration of his is restated.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open HarmonicBalls
open scoped NNReal

noncomputable section

namespace MatedCRT.Sec1

/-- **Radial integrals of one admissible observable are finite.** For circle averages `hcirc` of a sample, the radial integral
of the observable is finite: a pairing with a test function `φ` gives `x ↦ φ x * h_{|x|}(0)` Lebesgue integrable on `ℂ`, the
integral in `lateralEval` (its radial part agrees with `radialContribution` almost everywhere in `x`); a circle `(r, z)` with
`0 < r` gives the angular integrand `θ ↦ h_{|z + r e^{iθ}|}(0)` interval integrable on `[0, 2π]`, the integrand of the circle
average `Real.circleAverage (fun x ↦ h_{|x|}(0)) z r` in `lateralEval`. A circle through `0` is included: the logarithmic
singularity is integrable in the angle (env-steps.tex:248). -/
def ObservableRadialIntegrable (hcirc : ℝ → ℂ → ℝ) : GFFObservable → Prop
  | .pairing φ => Integrable (fun x : ℂ => φ x * hcirc ‖x‖ 0)
  | .circle r z =>
    IntervalIntegrable (fun θ : ℝ => hcirc ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ 0) volume 0 (2 * Real.pi)

/-- **Radial integrals are finite for every admissible observable, almost surely.** One `P`-almost sure event serves all
admissible observables at once: the test functions by `ae_integrable_test_mul_radial` and the circles by
`ae_forall_circle_intervalIntegrable_of_isQuantumCone`. -/
theorem ae_observable_radialIntegrable_of_isQuantumCone {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ o : GFFObservable.Admissible, ObservableRadialIntegrable (hcirc ω) o.1 := by
  filter_upwards [ae_integrable_test_mul_radial h, ae_forall_circle_intervalIntegrable_of_isQuantumCone h]
    with ω hT hA
  rintro ⟨o, ho⟩
  cases o with
  | pairing φ => exact hT φ ho
  | circle r z => exact hA r z ho

/-- **The lateral process is almost surely measurable.** The lateral part `h - h_{|·|}(0)` of the cone, as a process indexed by
all admissible observables in the product σ-algebra, is `P`-a.e. measurable. This is
`CirclePairing.aemeasurable_lateralProcess` (Proofs/Measurability/ConePairing.lean:263) at the measurability clauses and the
a.s. continuity clause of `IsQuantumCone`. -/
theorem aemeasurable_lateralProcess_of_isQuantumCone {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
  CirclePairing.aemeasurable_lateralProcess h.measurable_pairing h.measurable_circle h.ae_continuousOn_circle

/-- **A.s. recovery of the cone observables.** Almost surely, for every admissible observable `o` at once, `o(h)` equals the
transport of the radial and lateral processes of `h`: `o(h) = coneTransport (radialProcess h, lateralProcess h) o`. This is
`ae_coneObservable_eq_coneTransport` (CanonicalObservableAssembly.lean:171) at the continuity clause of `IsQuantumCone`. -/
theorem ae_coneObservables_eq_transport_of_isQuantumCone {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ o : GFFObservable.Admissible,
      o.1.eval (hC ω) (hcirc ω) = coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) o :=
  ae_coneObservable_eq_coneTransport h.ae_continuousOn_circle

/-- **The observable vector of any index family is almost surely measurable.** For `o : ι → GFFObservable.Admissible`, the vector
`ω ↦ (o i)(h)(ω)` is `P`-a.e. measurable into `ι → ℝ`. The proof transports the measurable radial process and the a.e.
measurable lateral process through the a.s. recovery identity; no measurability of the observables is assumed. -/
theorem aemeasurable_coneObservables_of_isQuantumCone {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {ι : Type} (o : ι → GFFObservable.Admissible) :
    AEMeasurable (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) P := by
  have hrad : Measurable fun ω => radialProcess (hcirc ω) := IsQuantumCone.measurable_radialProcess h
  have hpair : AEMeasurable (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) P :=
    hrad.aemeasurable.prodMk (aemeasurable_lateralProcess_of_isQuantumCone h)
  have hG : Measurable fun p : ConeRadialPaths × (GFFObservable.Admissible → ℝ) =>
      fun i : ι => coneTransport p (o i) :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply (o i)).comp measurable_coneTransport
  have hT : AEMeasurable
      (fun ω i => coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (o i)) P :=
    hG.comp_aemeasurable hpair
  have hV : (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) =ᵐ[P]
      (fun ω i => coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (o i)) := by
    filter_upwards [ae_coneObservables_eq_transport_of_isQuantumCone h] with ω hω
    funext i
    exact hω (o i)
  exact hT.congr hV.symm

/-- **Reference observable law with actual integrability (env-steps.tex:241-272).** Let `h : IsQuantumCone γ P hC hcirc`. Let
`hF : IsBMConditionedPositive (lqgQ γ - γ) (P0.map F)` be the reference conditioned positive law, kept as an explicit premise
(the WPN-53 bridge). Let `(P', hC', hcirc', hW)` be a whole-plane GFF whose lateral law is `hlat`. For any family
`o : ι → GFFObservable.Admissible` (finite `ι = Fin n`, countable `ι = ℕ`):
1. `P`-a.s., every `o i` has finite radial integrals (`ObservableRadialIntegrable`);
2. the observable vector `ω ↦ (o i)(h)(ω)` is `P`-a.e. measurable into `ι → ℝ`;
3. `P`-a.s., `(o i)(h) = coneTransport (radialProcess h, lateralProcess h) (o i)` for all `i`;
4. the joint law of the observable vector is the image of `quantumConeRadialLaw γ (P0.map F) ⊗ P'.map lateralProcess` under
   `coneTransport`, in the product σ-algebra over `ι`. -/
theorem map_coneObservables_index_eq_reference_assembly {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P' hC' hcirc')
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))
    {ι : Type} (o : ι → GFFObservable.Admissible) :
    (∀ᵐ ω ∂P, ∀ i, ObservableRadialIntegrable (hcirc ω) (o i).1) ∧
    AEMeasurable (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) P ∧
    (∀ᵐ ω ∂P, ∀ i, (o i).1.eval (hC ω) (hcirc ω) =
      coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (o i)) ∧
    P.map (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) =
      ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
        (fun p i => coneTransport p (o i)) := by
  let _ := hW
  have hrad : Measurable fun ω => radialProcess (hcirc ω) := IsQuantumCone.measurable_radialProcess h
  have hlatAE : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    aemeasurable_lateralProcess_of_isQuantumCone h
  have hpair : AEMeasurable (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) P :=
    hrad.aemeasurable.prodMk hlatAE
  have hsplit : P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) =
      (P.map (fun ω => radialProcess (hcirc ω))).prod (P.map (fun ω => lateralProcess (hC ω) (hcirc ω))) :=
    h.indep.map_prod_eq_prod_map_map hrad.aemeasurable hlatAE
  have hG : Measurable fun p : ConeRadialPaths × (GFFObservable.Admissible → ℝ) =>
      fun i : ι => coneTransport p (o i) :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply (o i)).comp measurable_coneTransport
  have hV : (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) =ᵐ[P]
      (fun ω i => coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (o i)) := by
    filter_upwards [ae_coneObservables_eq_transport_of_isQuantumCone h] with ω hω
    funext i
    exact hω (o i)
  have hcomp : P.map (fun ω i => coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (o i)) =
      (P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)))).map
        (fun p i => coneTransport p (o i)) :=
    (AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hpair).symm
  have hprod : P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) =
      (quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω))) := by
    rw [hsplit, radialProcess_map_eq_reference h hF, hlat]
  exact ⟨(ae_observable_radialIntegrable_of_isQuantumCone h).mono fun ω hω i => hω (o i),
    aemeasurable_coneObservables_of_isQuantumCone h o,
    (ae_coneObservables_eq_transport_of_isQuantumCone h).mono fun ω hω i => hω (o i),
    by rw [Measure.map_congr hV, hcomp, hprod]⟩

/-- **Reference observable law with the cone's own lateral witness.** As `map_coneObservables_index_eq_reference_assembly`, with
the whole-plane lateral witness taken from the lateral clause `IsQuantumCone.lateral_law` of `h`; the witness is existential,
as in that clause. -/
theorem map_coneObservables_index_eq_reference_witness_assembly {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F))
    {ι : Type} (o : ι → GFFObservable.Admissible) :
    (∀ᵐ ω ∂P, ∀ i, ObservableRadialIntegrable (hcirc ω) (o i).1) ∧
    AEMeasurable (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) P ∧
    (∀ᵐ ω ∂P, ∀ i, (o i).1.eval (hC ω) (hcirc ω) =
      coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (o i)) ∧
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧
      P.map (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) =
        ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
          (fun p i => coneTransport p (o i)) := by
  obtain ⟨Ω', m', P', hC', hcirc', hP', hW, hlat⟩ := h.lateral_law
  let _ := m'
  obtain ⟨h1, h2, h3, h4⟩ := map_coneObservables_index_eq_reference_assembly h hF hW hlat o
  exact ⟨h1, h2, h3, Ω', m', P', hC', hcirc', hP', hW, h4⟩

/-- **Reference observable law from a Brownian motion, with the Remark 4.4 premise displayed.** Let `B` be a Brownian motion on
`(Ω0, P0)` with measurable coordinates, let `0 < γ < 2`, and let `hR : DMS14Remark44PostLastZeroLaw` be the held DMS Remark 4.4
input. The producer `exists_referenceConeConditionedPath_law_of_isBrownianReal` gives the reference path `F`, measurable and
almost surely equal to `referenceConeConditionedPath γ (B · ω)`, whose law `P0.map F` is the conditioned positive law `hF`.
The conjuncts are those of `map_coneObservables_index_eq_reference_assembly`, with `hF` produced from `hR`. -/
theorem map_coneObservables_index_eq_brownian_assembly
    (hR : MatedCRT.Proposed.DMS14Remark44PostLastZeroLaw)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    (B : ℝ≥0 → Ω0 → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P0) (hBm : ∀ t, Measurable (B t))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P' hC' hcirc')
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))
    {ι : Type} (o : ι → GFFObservable.Admissible) :
    (∀ᵐ ω ∂P, ∀ i, ObservableRadialIntegrable (hcirc ω) (o i).1) ∧
    AEMeasurable (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) P ∧
    (∀ᵐ ω ∂P, ∀ i, (o i).1.eval (hC ω) (hcirc ω) =
      coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (o i)) ∧
    ∃ F : Ω0 → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P0, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F) ∧
      P.map (fun ω i => (o i).1.eval (hC ω) (hcirc ω)) =
        ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
          (fun p i => coneTransport p (o i)) := by
  obtain ⟨F, hFm, hFa, hF⟩ := exists_referenceConeConditionedPath_law_of_isBrownianReal hR hγ0 hγ2 B hB hBm
  obtain ⟨h1, h2, h3, h4⟩ := map_coneObservables_index_eq_reference_assembly h hF hW hlat o
  exact ⟨h1, h2, h3, F, hFm, hFa, hF, h4⟩

end MatedCRT.Sec1
