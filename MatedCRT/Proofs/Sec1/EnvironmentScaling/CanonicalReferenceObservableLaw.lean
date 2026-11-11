import MatedCRT.Proofs.Sec1.EnvironmentScaling.CanonicalObservableAssembly
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import MatedCRT.Proofs.Sec1.EnvironmentScaling.CanonicalBrownianPathAssembly

/-!
# Canonical reference observable law: cone observables with a supplied conditioned path law

The conditioned drifted Brownian law of the cone radial process; its
identification with DMS Remark 4.4, pp. 74-75, is the explicit premise `MatedCRT.Proposed.DMS14Remark44PostLastZeroLaw`, and the joint law of the cone observables.

This file specializes `CanonicalObservableAssembly.lean`. The radial clause of `IsQuantumCone` is the existential
`∃ ν, IsBMConditionedPositive (lqgQ γ - γ) ν ∧ P.map radialProcess = quantumConeRadialLaw γ ν`. Here the witness is the
reference law `P0.map F` of a measurable path map `F`, where `IsBMConditionedPositive (lqgQ γ - γ) (P0.map F)` is either
displayed as a premise or produced from a Brownian motion by `exists_referenceConeConditionedPath_law_of_isBrownianReal`
(with the explicit premise `DMS14Remark44PostLastZeroLaw`). The uniqueness of the conditioned positive law
(`isBMConditionedPositive_unique`, `Field.lean`) identifies the two laws. The joint law of the radial and lateral parts is
then transported through `coneTransport`, as in `map_finite_coneObservables_eq` and `map_coneObservables_eq`.

Proved here:
* `radialProcess_map_eq_reference`: the radial law of the cone is `quantumConeRadialLaw γ (P0.map F)`.
* `map_finite_coneObservables_eq_reference`, `map_coneObservables_eq_reference`: the law of a finite family, and the law in
  the product σ-algebra of all admissible observables, for a supplied whole-plane lateral witness `(P', hC', hcirc', hW)`
  with `hlat : P.map lateralProcess = P'.map lateralProcess'`. The witness clauses are those of `IsQuantumCone.lateral_law`:
  `IsWholePlaneGFF P' hC' hcirc'` and equality of the lateral laws (the probability property of `P'` is an instance
  argument). The independence clause `IsQuantumCone.indep` enters through `h`. The witness `hW` is not used by the identity,
  which needs only `hlat`; it is kept so that the hypotheses match `lateral_law`.
* `map_finite_coneObservables_eq_reference_witness`, `map_coneObservables_eq_reference_witness`: the same identities with the
  witness taken from the lateral clause of `h` (existential form).
* `map_finite_coneObservables_eq_brownian_reference`, `map_coneObservables_eq_brownian_reference`: a Brownian motion `B` on
  `(Ω0, P0)` with measurable coordinates gives the reference path `F` (measurable, almost surely equal to
  `referenceConeConditionedPath γ (B · ω)`, with `P0.map F` the conditioned positive law), under the displayed premise
  `hR : DMS14Remark44PostLastZeroLaw` and `0 < γ < 2`. The sublinear growth is discharged in `CanonicalBrownianPathAssembly`.

Credit. `Field.lean`, which supplies `isBMConditionedPositive_unique` and is imported here, imports Leonardo Bonanno's
LatticeProb modules `LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg` (the average module: measurable circle averages and
heat-kernel mollifications) and `LatticeProb.Bonanno.LQGMetric.Field.Measurable` (the field module it imports). Both are
adapted from Bonanno's lean-formalizations (github.com/leobon12/lean-formalizations, commit 31e7483). `Field.lean`'s header
states that its observable-law bridge uses Bonanno's LatticeProb field results via
`HarmonicBalls.Proofs.Sec8.WholePlaneObservableLaw`. This file does not import those modules directly.

Not claimed. The weak-limit identification of the conditioned law, which is the content of `DMS14Remark44PostLastZeroLaw`, is
held as an explicit premise and not proved. The represented-circle recovery, a distribution-valued realization of the cone,
and sublinear radial growth as a radial majorant (`RadialLogMajorant`) are not used here.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open HarmonicBalls
open scoped NNReal

noncomputable section

namespace MatedCRT.Sec1

/-- **Radial law with the reference conditioned path law.** For a `γ`-quantum cone `h` and a reference law `P0.map F` that is
a conditioned positive law of drift `lqgQ γ - γ` (`IsBMConditionedPositive`), the radial process of `h` has law
`quantumConeRadialLaw γ (P0.map F)`. The witness `ν` of the radial clause of `IsQuantumCone` is identified with `P0.map F`
by the uniqueness of the conditioned positive law (`isBMConditionedPositive_unique`, `Field.lean`). -/
theorem radialProcess_map_eq_reference
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F)) :
    P.map (fun ω => radialProcess (hcirc ω)) = quantumConeRadialLaw γ (P0.map F) := by
  obtain ⟨ν, hν, hνlaw⟩ := h.radial_law
  rw [hνlaw, isBMConditionedPositive_unique hν hF]

/-- **Finite-dimensional law of the cone observables with the reference radial law.** Let `h : IsQuantumCone γ P hC hcirc`,
let `P0.map F` be a conditioned positive law (`hF`), and let `(P', hC', hcirc', hW)` be a whole-plane GFF whose lateral law is
`hlat`. For a finite family `c` of admissible observables, the law of the observable vector is the image of
`quantumConeRadialLaw γ (P0.map F) ⊗ P'.map lateralProcess` under `coneTransport`. -/
theorem map_finite_coneObservables_eq_reference
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P' hC' hcirc')
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))
    {n : ℕ} (c : Fin n → GFFObservable.Admissible) :
    P.map (fun ω i => (c i).1.eval (hC ω) (hcirc ω)) =
      ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
        (fun p i => coneTransport p (c i)) := by
  let _ := hW
  exact map_finite_coneObservables_eq h (P0.map F) (radialProcess_map_eq_reference h hF) _ hlat c

/-- **Joint law of all cone observables with the reference radial law.** The hypotheses are those of
`map_finite_coneObservables_eq_reference`. The law of the whole family of admissible observables, in the product σ-algebra,
is the image of `quantumConeRadialLaw γ (P0.map F) ⊗ P'.map lateralProcess` under `coneTransport`. No countability of the
observables is used. -/
theorem map_coneObservables_eq_reference
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P' hC' hcirc')
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω))) :
    P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) =
      ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
        coneTransport := by
  let _ := hW
  exact map_coneObservables_eq h (P0.map F) (radialProcess_map_eq_reference h hF) _ hlat

/-- **Finite-dimensional law with the reference radial law and the cone's own lateral witness.** As
`map_finite_coneObservables_eq_reference`, with the whole-plane lateral witness taken from the lateral clause
`IsQuantumCone.lateral_law` of `h`; the witness is existential, as in that clause. -/
theorem map_finite_coneObservables_eq_reference_witness
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F))
    {n : ℕ} (c : Fin n → GFFObservable.Admissible) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧
      P.map (fun ω i => (c i).1.eval (hC ω) (hcirc ω)) =
        ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
          (fun p i => coneTransport p (c i)) := by
  obtain ⟨Ω', m', P', hC', hcirc', hP', hW, hlat⟩ := h.lateral_law
  let _ := m'
  exact ⟨Ω', m', P', hC', hcirc', hP', hW, map_finite_coneObservables_eq_reference h hF hW hlat c⟩

/-- **Joint law of all cone observables with the reference radial law and the cone's own lateral witness.** As
`map_coneObservables_eq_reference`, with the whole-plane lateral witness taken from `IsQuantumCone.lateral_law` of `h`. -/
theorem map_coneObservables_eq_reference_witness
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F)) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧
      P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) =
        ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
          coneTransport := by
  obtain ⟨Ω', m', P', hC', hcirc', hP', hW, hlat⟩ := h.lateral_law
  let _ := m'
  exact ⟨Ω', m', P', hC', hcirc', hP', hW, map_coneObservables_eq_reference h hF hW hlat⟩

/-- **Finite-dimensional law from a Brownian motion, with the Remark 4.4 premise displayed.** Let `B` be a Brownian motion
on `(Ω0, P0)` with measurable coordinates and `0 < γ < 2`. The premise `hR : DMS14Remark44PostLastZeroLaw` is the held DMS
Remark 4.4 input; the sublinear growth is discharged. Then there is a measurable reference path `F`, almost surely equal to
`referenceConeConditionedPath γ (B · ω)`, whose law `P0.map F` is the conditioned positive law, and the finite-dimensional law
of the cone observables is the image of `quantumConeRadialLaw γ (P0.map F) ⊗ P'.map lateralProcess` under `coneTransport`
for the supplied whole-plane lateral witness. -/
theorem map_finite_coneObservables_eq_brownian_reference
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
    {n : ℕ} (c : Fin n → GFFObservable.Admissible) :
    ∃ F : Ω0 → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P0, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F) ∧
      P.map (fun ω i => (c i).1.eval (hC ω) (hcirc ω)) =
        ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
          (fun p i => coneTransport p (c i)) := by
  obtain ⟨F, hFm, hFa, hF⟩ := exists_referenceConeConditionedPath_law_of_isBrownianReal hR hγ0 hγ2 B hB hBm
  exact ⟨F, hFm, hFa, hF, map_finite_coneObservables_eq_reference h hF hW hlat c⟩

/-- **Joint law of all cone observables from a Brownian motion, with the Remark 4.4 premise displayed.** As
`map_finite_coneObservables_eq_brownian_reference`, for the law of the whole family of admissible observables in the product
σ-algebra. -/
theorem map_coneObservables_eq_brownian_reference
    (hR : MatedCRT.Proposed.DMS14Remark44PostLastZeroLaw)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    (B : ℝ≥0 → Ω0 → ℝ) (hB : ProbabilityTheory.IsBrownianReal B P0) (hBm : ∀ t, Measurable (B t))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P' hC' hcirc')
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω))) :
    ∃ F : Ω0 → MarkovProcess.ContinuousPath ℝ, Measurable F ∧
      (∀ᵐ ω ∂P0, ∀ t : ℝ≥0, F ω t = referenceConeConditionedPath γ (fun s => B s ω) t) ∧
      IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F) ∧
      P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) =
        ((quantumConeRadialLaw γ (P0.map F)).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
          coneTransport := by
  obtain ⟨F, hFm, hFa, hF⟩ := exists_referenceConeConditionedPath_law_of_isBrownianReal hR hγ0 hγ2 B hB hBm
  exact ⟨F, hFm, hFa, hF, map_coneObservables_eq_reference h hF hW hlat⟩

end MatedCRT.Sec1
