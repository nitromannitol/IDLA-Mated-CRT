import MatedCRT.Proofs.Sec1.EnvironmentScaling.IntegrableReferenceObservables
import MatedCRT.Proofs.Sec1.EnvironmentScaling.DistributionCode

/-!
# Countable observable identification for the represented-field grid route

The countable family of admissible observables consumed by the represented-field grid route, with its joint law and
recovery from the checked reference observable exports of `IntegrableReferenceObservables.lean`. The family has two
parts.

* Code tests. `planeDistributionCode.test : LQGMetric.CoordJ → LQGMetric.TestC` is the countable family of actual plane
  tests of Leonardo Bonanno's countable Borel code: `CoordJ = (ℕ × ℕ) →₀ ℤ` and `comb` in
  `LatticeProb.Bonanno.LQGMetric.Field.StandardBorelDistOn`, and the measurable embedding `measurableEmbedding_pairJ` in
  `LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange`. Their pairings are the admissible observables
  `codeTestObservable c`.
* Dyadic grid circles. `gridCircleObservable q` is the circle average of radius `k / 2 ^ n` with `k > 0`, about the centre
  `FieldCircle.gridPt m a d` (`MatedCRT/Proofs/Measurability/FieldCircle.lean`). The indices are the quantifiers of
  `RescaledConeDistributionCircleGridStep` (`Field.lean`).

The code `d ↦ (d (test c))_c` is a measurable embedding of distributions into `CoordJ → ℝ`
(`planeDistributionCode.embedding`, `DistributionCode.lean`). So the joint law of the countable pairings determines the law
of every measurable representing distribution. This is the distribution half of the countable determining-family argument
of env-steps.tex:264–272. The circle-process half, the law on `C(E, ℝ)` from countably many grid circles, is not part of
this file.

The statements take the WPN-53 premise `hF : IsBMConditionedPositive (lqgQ γ - γ) (P0.map F)` and an explicit
whole-plane witness with its lateral-law identities as hypotheses, and assume nothing else beyond the cone predicates and
the represented distributions. No rescaling, no environment-scaling closure and no same-space field construction is proved
here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open HarmonicBalls
open scoped NNReal

namespace MatedCRT.Sec1

/-- The index of a dyadic grid circle `(k / 2 ^ n, FieldCircle.gridPt m a d)` with `k > 0`, with the quantifiers of
`RescaledConeDistributionCircleGridStep`. -/
structure GridCircleIndex where
  n : ℕ
  m : ℕ
  k : ℤ
  a : ℤ
  d : ℤ
  k_pos : 0 < k

instance : Countable GridCircleIndex := by
  refine Function.Injective.countable (f := fun q : GridCircleIndex => (q.n, q.m, q.k, q.a, q.d)) ?_
  rintro ⟨n, m, k, a, d, hk⟩ ⟨n', m', k', a', d', hk'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- The countable index of the represented-field observable family: the code tests, indexed by `LQGMetric.CoordJ`, and
the dyadic grid circles. -/
abbrev CountableObservableIndex : Type := LQGMetric.CoordJ ⊕ GridCircleIndex

theorem countable_countableObservableIndex : Countable CountableObservableIndex := inferInstance

/-- The admissible pairing with the code test `planeDistributionCode.test c`. -/
def codeTestObservable (c : LQGMetric.CoordJ) : GFFObservable.Admissible :=
  ⟨.pairing (planeDistributionCode.test c), by
    show IsTestFunction Set.univ (planeDistributionCode.test c)
    exact ⟨(planeDistributionCode.test c).contDiff, (planeDistributionCode.test c).hasCompactSupport,
      (planeDistributionCode.test c).tsupport_subset⟩⟩

/-- The admissible dyadic grid circle `(k / 2 ^ n, FieldCircle.gridPt m a d)`. -/
def gridCircleObservable (q : GridCircleIndex) : GFFObservable.Admissible :=
  ⟨.circle ((q.k : ℝ) / 2 ^ q.n) (FieldCircle.gridPt q.m q.a q.d), by
    show 0 < (q.k : ℝ) / 2 ^ q.n
    exact div_pos (by exact_mod_cast q.k_pos) (by positivity)⟩

/-- The exact countable observable family of the represented-field grid route. -/
def countableObservable : CountableObservableIndex → GFFObservable.Admissible
  | .inl c => codeTestObservable c
  | .inr q => gridCircleObservable q

/-- Restriction of a vector indexed by the countable family to its code-test coordinates. -/
theorem measurable_codeRestrict :
    Measurable (fun (v : CountableObservableIndex → ℝ) (c : LQGMetric.CoordJ) => v (Sum.inl c)) :=
  Measurable.of_eval fun c => measurable_pi_apply (Sum.inl c)

/-- Finite-vector measurability: every finite list of the family gives an a.e. measurable vector of observables. -/
theorem aemeasurable_countableObservables_finite {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) {n : ℕ}
    (j : Fin n → CountableObservableIndex) :
    AEMeasurable (fun ω (i : Fin n) => (countableObservable (j i)).1.eval (hC ω) (hcirc ω)) P :=
  aemeasurable_coneObservables_of_isQuantumCone h fun i => countableObservable (j i)

/-- Countable-product measurability: the whole countable family is an a.e. measurable vector. -/
theorem aemeasurable_countableObservables {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    AEMeasurable (fun ω (i : CountableObservableIndex) => (countableObservable i).1.eval (hC ω) (hcirc ω)) P :=
  aemeasurable_coneObservables_of_isQuantumCone h countableObservable

/-- The countable code vector of pairings `(hC ω (test c))_c` is a.e. measurable. -/
theorem aemeasurable_codeTests {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    AEMeasurable (fun ω (c : LQGMetric.CoordJ) => hC ω (planeDistributionCode.test c)) P :=
  measurable_codeRestrict.comp_aemeasurable (aemeasurable_countableObservables h)

/-- Recovery: almost surely, every member of the countable family equals its reference transport. -/
theorem ae_countableObservables_recovery {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ i : CountableObservableIndex, (countableObservable i).1.eval (hC ω) (hcirc ω) =
      coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (countableObservable i) :=
  (ae_coneObservables_eq_transport_of_isQuantumCone h).mono fun _ hω i => hω (countableObservable i)

/-- Joint law of the countable family under the reference. The WPN-53 premise `hF` and the whole-plane witness
`hW` with its lateral law `hlat` are explicit hypotheses; the conclusion is the reference assembly of
`map_coneObservables_index_eq_reference_assembly` at the index `CountableObservableIndex`. -/
theorem map_countableObservables_eq_reference {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F))
    {Ωw : Type} [MeasurableSpace Ωw] {Pw : Measure Ωw} [IsProbabilityMeasure Pw]
    {hCw : Ωw → (ℂ → ℝ) → ℝ} {hcircw : Ωw → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF Pw hCw hcircw)
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      Pw.map (fun ω => lateralProcess (hCw ω) (hcircw ω))) :
    P.map (fun ω (i : CountableObservableIndex) => (countableObservable i).1.eval (hC ω) (hcirc ω)) =
      ((quantumConeRadialLaw γ (P0.map F)).prod (Pw.map (fun ω => lateralProcess (hCw ω) (hcircw ω)))).map
        (fun p i => coneTransport p (countableObservable i)) :=
  (map_coneObservables_index_eq_reference_assembly h hF hW hlat countableObservable).2.2.2

/-- Joint law of the code-test pairings under the reference: the restriction of the countable family's law to the
code-test coordinates. -/
theorem map_codeTests_eq_reference {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F))
    {Ωw : Type} [MeasurableSpace Ωw] {Pw : Measure Ωw} [IsProbabilityMeasure Pw]
    {hCw : Ωw → (ℂ → ℝ) → ℝ} {hcircw : Ωw → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF Pw hCw hcircw)
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      Pw.map (fun ω => lateralProcess (hCw ω) (hcircw ω))) :
    P.map (fun ω (c : LQGMetric.CoordJ) => hC ω (planeDistributionCode.test c)) =
      (((quantumConeRadialLaw γ (P0.map F)).prod (Pw.map (fun ω => lateralProcess (hCw ω) (hcircw ω)))).map
        (fun p i => coneTransport p (countableObservable i))).map
        (fun (v : CountableObservableIndex → ℝ) (c : LQGMetric.CoordJ) => v (Sum.inl c)) := by
  rw [← map_countableObservables_eq_reference h hF hW hlat]
  exact (AEMeasurable.map_map_of_aemeasurable measurable_codeRestrict.aemeasurable
    (aemeasurable_countableObservables h)).symm

/-- Two cone environments with the same reference data have equal laws of their code-test pairings. -/
theorem map_codeTests_eq_of_reference {γ : ℝ} {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) (h' : IsQuantumCone γ P' hC' hcirc')
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F))
    {Ωw : Type} [MeasurableSpace Ωw] {Pw : Measure Ωw} [IsProbabilityMeasure Pw]
    {hCw : Ωw → (ℂ → ℝ) → ℝ} {hcircw : Ωw → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF Pw hCw hcircw)
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      Pw.map (fun ω => lateralProcess (hCw ω) (hcircw ω)))
    (hlat' : P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)) =
      Pw.map (fun ω => lateralProcess (hCw ω) (hcircw ω))) :
    P.map (fun ω (c : LQGMetric.CoordJ) => hC ω (planeDistributionCode.test c)) =
      P'.map (fun ω (c : LQGMetric.CoordJ) => hC' ω (planeDistributionCode.test c)) := by
  rw [map_codeTests_eq_reference h hF hW hlat, map_codeTests_eq_reference h' hF hW hlat']

/-- Countable determining family: the pairings `(d (test c))_c` determine a distribution, because
`planeDistributionCode.embedding` is a measurable embedding. Equal laws of the code vectors of two measurable
distributions therefore give equal laws of the distributions. -/
theorem map_eq_of_codeTests_map_eq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC} (hH : Measurable H)
    (hH' : Measurable H')
    (hcode : P.map (fun ω (c : LQGMetric.CoordJ) => H ω (planeDistributionCode.test c)) =
      P'.map (fun ω (c : LQGMetric.CoordJ) => H' ω (planeDistributionCode.test c))) :
    P.map H = P'.map H' := by
  refine MeasurableEmbedding.map_injective planeDistributionCode.embedding ?_
  rw [Measure.map_map planeDistributionCode.embedding.measurable hH,
    Measure.map_map planeDistributionCode.embedding.measurable hH']
  exact hcode

/-- Represented distributions under the reference: two measurable distributions representing the cone observables of two
cone environments with the same reference data (WPN-53 premise `hF`, whole-plane witness `hW`, lateral identities `hlat`
and `hlat'`) have equal laws. The representation `hrep` and `hrep'` is an explicit hypothesis, as is the measurability of
the representing distributions. -/
theorem map_represented_distribution_eq_of_reference {γ : ℝ} {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) (h' : IsQuantumCone γ P' hC' hcirc')
    {Ω0 : Type} [MeasurableSpace Ω0] {P0 : Measure Ω0} [IsProbabilityMeasure P0]
    {F : Ω0 → MarkovProcess.ContinuousPath ℝ}
    (hF : IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P0.map F))
    {Ωw : Type} [MeasurableSpace Ωw] {Pw : Measure Ωw} [IsProbabilityMeasure Pw]
    {hCw : Ωw → (ℂ → ℝ) → ℝ} {hcircw : Ωw → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF Pw hCw hcircw)
    (hlat : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) =
      Pw.map (fun ω => lateralProcess (hCw ω) (hcircw ω)))
    (hlat' : P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)) =
      Pw.map (fun ω => lateralProcess (hCw ω) (hcircw ω)))
    {H : Ω → LQGMetric.DistC} {H' : Ω' → LQGMetric.DistC} (hH : Measurable H) (hH' : Measurable H')
    (hrep : ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestC, hC ω φ = H ω φ)
    (hrep' : ∀ᵐ ω ∂P', ∀ φ : LQGMetric.TestC, hC' ω φ = H' ω φ) :
    P.map H = P'.map H' := by
  apply map_eq_of_codeTests_map_eq hH hH'
  have e₁ : (fun ω (c : LQGMetric.CoordJ) => H ω (planeDistributionCode.test c)) =ᵐ[P]
      (fun ω (c : LQGMetric.CoordJ) => hC ω (planeDistributionCode.test c)) := by
    filter_upwards [hrep] with ω hω
    funext c
    exact (hω _).symm
  have e₂ : (fun ω (c : LQGMetric.CoordJ) => H' ω (planeDistributionCode.test c)) =ᵐ[P']
      (fun ω (c : LQGMetric.CoordJ) => hC' ω (planeDistributionCode.test c)) := by
    filter_upwards [hrep'] with ω hω
    funext c
    exact (hω _).symm
  rw [Measure.map_congr e₁, Measure.map_congr e₂]
  exact map_codeTests_eq_of_reference h h' hF hW hlat hlat'

end MatedCRT.Sec1
