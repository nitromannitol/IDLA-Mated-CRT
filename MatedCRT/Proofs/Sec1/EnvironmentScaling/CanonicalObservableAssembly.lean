import MatedCRT.Proofs.Sec1.EnvironmentScaling.CanonicalLateralLawAssembly
import MatedCRT.Proofs.Sec1.EnvironmentScaling.MeasurableAngularIntegrals
import MatedCRT.Proofs.Measurability.ConePairing

/-!
# Canonical observable assembly: finite-dimensional laws of cone observables

Radial integrability, finiteness of the angular integrals for circles
through zero, and their determination by countably many radial evaluations; the Gaussian covariance fixes
the lateral law, and independence in the cone predicate identifies the joint law of the cone observables with the lateral
GFF plus the independent radial function. The source cites Duplantier–Miller–Sheffield (Lemma 4.9 and Definition 4.10) for the
distribution-valued cone; this file does not use that citation (Duplantier–Miller–Sheffield, arXiv:1409.7055).

Definitions: `Defs/QuantumCone.lean` (`IsQuantumCone`, `radialProcess`, `quantumConeRadialLaw`, `lateralProcess`) and
`GFFObservable` (`eval`, `IsAdmissible`; Harmonic-Balls-LQG). Inputs: `CanonicalLateralLawAssembly.lean` (lateral-law
and radial-independence conventions), `Field.lean` (`IsQuantumCone.measurable_radialProcess`, `IsQuantumCone.lateral_law`),
`ConePairing.lean` (`CirclePairing.radialVersion`, the jointly measurable dyadic radial version and its identity with the
radial function for continuous fields).

Proved here:
* `coneTransport`: transport of a pair of logarithmic radial paths and a lateral family to a family of cone observables,
  adding the radial contribution of each observable (`∫ φ(x) h_{|x|}(0) dx` for a pairing, the circle average of
  `x ↦ h_{|x|}(0)` for a circle). It is measurable (`measurable_coneTransport`).
* `ae_coneObservable_eq_coneTransport`: the observable equality. Almost surely, every admissible observable of the field
  equals the transport of its radial and lateral parts. No integrability is assumed: the two integrals agree because the
  integrands agree off the null set `{0}` (pairings) or off the countable set `circleZeroAngles` (circle averages).
* `map_finite_coneObservables_eq`: for a finite family of admissible observables, the law of the observable vector is the
  image under `coneTransport` of `quantumConeRadialLaw γ ν ⊗ Q`, where `ν` is an explicitly supplied radial law and `Q` is the
  actual lateral law. The product form comes from the independence clause of the cone predicate.
* `map_finite_coneObservables_eq_of_lateral_witness`: the same identity with `Q` the lateral law of a whole-plane GFF witness,
  as supplied by the lateral clause of the cone predicate.

Remaining canonical inputs, not derived here: the identification of the explicit radial law `ν` with a post-last-zero or
conditioned Brownian law (this is where `DMS14Remark44PostLastZeroLaw`, `Proposed/DuplantierMillerSheffieldCone2014.lean`,
would enter; this file does not use it); the represented-circle recovery of a distribution; sublinear radial
growth (`RadialLogMajorant`); the continuity of the cone's circle process (taken from `IsQuantumCone.ae_continuousOn_circle`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open HarmonicBalls

noncomputable section

namespace MatedCRT.Sec1

/-- The two logarithmic radial paths of a field: `t ↦ h_{e^{-t}}(0)` and `s ↦ h_{e^s}(0)`, as in `radialProcess`. -/
abbrev ConeRadialPaths := (NNReal → ℝ) × (NNReal → ℝ)

/-- The circle values `h_r(0)` recovered from the two logarithmic paths: `v.2 (log r)` for `r ≥ 1` and `v.1 (-log r)`
for `r < 1`. This is the radial circle map used in Field.lean, stated for a general pair of paths. -/
def radialCircleOfPaths (v : ConeRadialPaths) (r : ℝ) (_z : ℂ) : ℝ :=
  if 1 ≤ r then v.2 (Real.toNNReal (Real.log r)) else v.1 (Real.toNNReal (-Real.log r))

lemma measurable_radialCircleOfPaths (r : ℝ) (z : ℂ) :
    Measurable (fun v : ConeRadialPaths => radialCircleOfPaths v r z) := by
  by_cases hr : 1 ≤ r
  · simp only [radialCircleOfPaths, hr, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_snd
  · simp only [radialCircleOfPaths, hr, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_fst

/-- For `r > 0` the radial circle values of the radial process of a field `a` are the circle averages `a r 0`. -/
lemma radialCircleOfPaths_radialProcess (a : ℝ → ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    radialCircleOfPaths (radialProcess a) r z = a r 0 := by
  by_cases h : 1 ≤ r
  · have hl := Real.log_nonneg h
    simp only [radialCircleOfPaths, h, ↓reduceIte, radialProcess, Real.coe_toNNReal _ hl, Real.exp_log hr]
  · have hl : Real.log r ≤ 0 := Real.log_nonpos hr.le (le_of_not_ge h)
    simp only [radialCircleOfPaths, h, ↓reduceIte, radialProcess, Real.coe_toNNReal _ (neg_nonneg.mpr hl),
      neg_neg, Real.exp_log hr]

/-- Off the origin the dyadic radial version of the radial process of a field is the radial function: if
`s ↦ a s 0` is continuous on `(0, ∞)`, then `radialVersion (radialProcess a) s = a s 0` for `s > 0`. -/
lemma radialVersion_radialProcess_eq (a : ℝ → ℂ → ℝ)
    (hc : ContinuousOn (fun p : ℝ × ℂ => a p.1 p.2) (Ioi 0 ×ˢ univ)) {s : ℝ} (hs : 0 < s) :
    CirclePairing.radialVersion radialCircleOfPaths (radialProcess a) s = a s 0 := by
  have hc0 : ContinuousOn (fun t : ℝ => a t 0) (Ioi 0) :=
    hc.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))).continuousOn
      fun t ht => ⟨ht, mem_univ _⟩
  have h1 : CirclePairing.radialVersion radialCircleOfPaths (radialProcess a) s =
      CirclePairing.radialVersion (fun _ : Unit => a) () s := by
    unfold CirclePairing.radialVersion
    congr 1
    funext n
    by_cases hn : 0 < ⌈s * 2 ^ n⌉
    · have hp : 0 < CirclePairing.dyadicCeil n s :=
        div_pos (Int.cast_pos.2 hn) (by positivity)
      simp [CirclePairing.radialApprox, hn, radialCircleOfPaths_radialProcess a hp]
    · simp [CirclePairing.radialApprox, hn]
  rw [h1, CirclePairing.radialVersion_eq (ω := ()) (hcirc := fun _ : Unit => a) hc0 hs]

/-- The radial contribution of an observable to the radial paths `v`: `∫ φ(x) h_{|x|}(0) dx` for a pairing, and the
circle average of `x ↦ h_{|x|}(0)` for a circle. The radial function is the jointly measurable dyadic version
`CirclePairing.radialVersion`, so that the contribution is measurable in `v`. -/
def radialContribution (v : ConeRadialPaths) : GFFObservable → ℝ
  | .pairing φ => ∫ x, φ x * CirclePairing.radialVersion radialCircleOfPaths v ‖x‖
  | .circle r z => Real.circleAverage (fun x => CirclePairing.radialVersion radialCircleOfPaths v ‖x‖) z r

/-- The cone transport: adds the radial contribution of the radial paths `p.1` to the lateral family `p.2`, observable by
observable. -/
def coneTransport (p : ConeRadialPaths × (GFFObservable.Admissible → ℝ)) :
    GFFObservable.Admissible → ℝ :=
  fun o => p.2 o + radialContribution p.1 o.1

lemma measurable_radialContribution_pairing (φ : ℂ → ℝ) (hφ : Continuous φ) :
    Measurable fun v : ConeRadialPaths => radialContribution v (.pairing φ) := by
  have hr := CirclePairing.measurable_radialVersion (fun r z _ => measurable_radialCircleOfPaths r z)
  have hf : StronglyMeasurable fun p : ConeRadialPaths × ℂ =>
      φ p.2 * CirclePairing.radialVersion radialCircleOfPaths p.1 ‖p.2‖ :=
    ((hφ.measurable.comp measurable_snd).mul
      (hr.comp (measurable_fst.prodMk measurable_snd.norm))).stronglyMeasurable
  exact (hf.integral_prod_right' (ν := volume)).measurable

lemma measurable_radialContribution_circle (r : ℝ) (z : ℂ) :
    Measurable fun v : ConeRadialPaths => radialContribution v (.circle r z) := by
  have hr := CirclePairing.measurable_radialVersion (fun r z _ => measurable_radialCircleOfPaths r z)
  have e : (fun v : ConeRadialPaths => radialContribution v (.circle r z)) = fun v =>
      (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi),
        CirclePairing.radialVersion radialCircleOfPaths v ‖circleMap z r θ‖ := by
    funext v
    simp only [radialContribution]
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity), smul_eq_mul]
  have hf : StronglyMeasurable fun p : ConeRadialPaths × ℝ =>
      CirclePairing.radialVersion radialCircleOfPaths p.1 ‖circleMap z r p.2‖ :=
    (hr.comp (measurable_fst.prodMk
      ((continuous_circleMap z r).measurable.comp measurable_snd).norm)).stronglyMeasurable
  rw [e]
  exact ((hf.integral_prod_right' (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).measurable).const_mul _

/-- The cone transport is jointly measurable in the radial paths and the lateral family. -/
lemma measurable_coneTransport : Measurable coneTransport := by
  apply measurable_pi_iff.mpr
  rintro ⟨o, ho⟩
  have hL : Measurable fun p : ConeRadialPaths × (GFFObservable.Admissible → ℝ) => p.2 ⟨o, ho⟩ :=
    (measurable_pi_apply _).comp measurable_snd
  cases o with
  | pairing φ =>
    exact hL.add ((measurable_radialContribution_pairing φ ho.1.continuous).comp measurable_fst)
  | circle r z =>
    exact hL.add ((measurable_radialContribution_circle r z).comp measurable_fst)

/-- Circle averages of two functions agree when the functions agree off `0` and the radius is positive: the circle
`θ ↦ z + r e^{iθ}` passes through `0` only on the countable set `circleZeroAngles z r`, which is null. -/
lemma circleAverage_congr_of_ne_zero {f g : ℂ → ℝ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hfg : ∀ x : ℂ, x ≠ 0 → f x = g x) :
    Real.circleAverage f z r = Real.circleAverage g z r := by
  have hae : ∀ᵐ θ : ℝ ∂(volume : Measure ℝ), θ ∉ circleZeroAngles z r := by
    rw [ae_iff]
    simpa using volume_circleZeroAngles (z := z) hr
  simp only [Real.circleAverage_def, smul_eq_mul]
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity)]
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [hae] with θ hθ _
  apply hfg
  intro h0
  apply hθ
  show ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ = 0
  rw [mul_comm I]
  exact norm_eq_zero.mpr h0

/-- Complex Lebesgue-almost every point is nonzero. -/
lemma ae_ne_zero_complex : ∀ᵐ x : ℂ ∂(volume : Measure ℂ), x ≠ 0 := by
  rw [ae_iff]
  simp

/-- **Observable equality.** Let `hcirc` have circle averages continuous on `(0, ∞) × ℂ` almost
surely. Then almost surely, for every admissible observable `o`, the value `o(h)` of the field equals the transport of its
radial process and its lateral process: `o(h) = coneTransport (radialProcess h, lateralProcess h) o`. The identity needs no
integrability assumption, because both sides use the same integrals up to a null set. -/
theorem ae_coneObservable_eq_coneTransport {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ∀ᵐ ω ∂P, ∀ o : GFFObservable.Admissible,
      o.1.eval (hC ω) (hcirc ω) =
        coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) o := by
  filter_upwards [hcont] with ω hω
  rintro ⟨o, ho⟩
  cases o with
  | pairing φ =>
    have hint : ∫ x : ℂ, φ x * CirclePairing.radialVersion radialCircleOfPaths (radialProcess (hcirc ω)) ‖x‖
        = ∫ x : ℂ, φ x * hcirc ω ‖x‖ 0 := by
      refine integral_congr_ae ?_
      filter_upwards [ae_ne_zero_complex] with x hx
      simp only [radialVersion_radialProcess_eq (hcirc ω) hω (norm_pos_iff.mpr hx)]
    simp only [GFFObservable.eval, coneTransport, lateralProcess, lateralEval, radialContribution]
    rw [hint]
    ring
  | circle r z =>
    have hr : 0 < r := ho
    have havg : Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r =
        Real.circleAverage (fun x => CirclePairing.radialVersion radialCircleOfPaths (radialProcess (hcirc ω)) ‖x‖) z r :=
      circleAverage_congr_of_ne_zero (f := fun x => hcirc ω ‖x‖ 0)
        (g := fun x => CirclePairing.radialVersion radialCircleOfPaths (radialProcess (hcirc ω)) ‖x‖)
        hr (fun x hx => (radialVersion_radialProcess_eq (hcirc ω) hω (norm_pos_iff.mpr hx)).symm)
    simp only [GFFObservable.eval, coneTransport, lateralProcess, lateralEval, radialContribution]
    rw [havg]
    ring

/-- **Finite-dimensional law of the cone observables.** Let `h : IsQuantumCone γ P hC hcirc`. Let `ν` be an explicitly
supplied radial law with `P.map (radialProcess ∘ hcirc) = quantumConeRadialLaw γ ν`, and `Q` the actual lateral law
`P.map (lateralProcess ∘ (hC, hcirc)) = Q`. For a finite family `c` of admissible observables, the law of the observable
vector is the image of `quantumConeRadialLaw γ ν ⊗ Q` under `coneTransport`. The product form is the independence clause
of the cone predicate; the transport is the observable equality `ae_coneObservable_eq_coneTransport`. -/
theorem map_finite_coneObservables_eq {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    (ν : Measure (MarkovProcess.ContinuousPath ℝ))
    (hν : P.map (fun ω => radialProcess (hcirc ω)) = quantumConeRadialLaw γ ν)
    (Q : Measure (GFFObservable.Admissible → ℝ))
    (hQ : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) = Q)
    {n : ℕ} (c : Fin n → GFFObservable.Admissible) :
    P.map (fun ω i => (c i).1.eval (hC ω) (hcirc ω)) =
      ((quantumConeRadialLaw γ ν).prod Q).map (fun p i => coneTransport p (c i)) := by
  have hcont := h.ae_continuousOn_circle
  have hrad : Measurable fun ω => radialProcess (hcirc ω) :=
    IsQuantumCone.measurable_radialProcess h
  have hlat : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    CirclePairing.aemeasurable_lateralProcess h.measurable_pairing h.measurable_circle hcont
  have hpair : AEMeasurable (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) P :=
    hrad.aemeasurable.prodMk hlat
  have hsplit : P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) =
      (P.map (fun ω => radialProcess (hcirc ω))).prod (P.map (fun ω => lateralProcess (hC ω) (hcirc ω))) :=
    h.indep.map_prod_eq_prod_map_map hrad.aemeasurable hlat
  have hG : Measurable fun p : ConeRadialPaths × (GFFObservable.Admissible → ℝ) =>
      fun i : Fin n => coneTransport p (c i) :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply (c i)).comp measurable_coneTransport
  have hV : (fun ω i => (c i).1.eval (hC ω) (hcirc ω)) =ᵐ[P]
      (fun ω i => coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (c i)) := by
    filter_upwards [ae_coneObservable_eq_coneTransport hcont] with ω hω
    funext i
    exact hω (c i)
  have hcomp : P.map (fun ω i => coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)) (c i)) =
      (P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)))).map
        (fun p i => coneTransport p (c i)) :=
    (AEMeasurable.map_map_of_aemeasurable hG.aemeasurable hpair).symm
  have hprod : P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) =
      (quantumConeRadialLaw γ ν).prod Q := by
    rw [hsplit, hν, hQ]
  rw [Measure.map_congr hV, hcomp, hprod]

/-- **Joint law of all cone observables.** For `h : IsQuantumCone γ P hC hcirc`, with the explicitly
supplied radial law `quantumConeRadialLaw γ ν` and the actual lateral law `Q`, the law of the whole family of admissible
observables, in the product σ-algebra, is the image of `quantumConeRadialLaw γ ν ⊗ Q` under `coneTransport`. No
countability of the observables is used: the observable equality holds almost surely for all of them at once. -/
theorem map_coneObservables_eq {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    (ν : Measure (MarkovProcess.ContinuousPath ℝ))
    (hν : P.map (fun ω => radialProcess (hcirc ω)) = quantumConeRadialLaw γ ν)
    (Q : Measure (GFFObservable.Admissible → ℝ))
    (hQ : P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) = Q) :
    P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) =
      ((quantumConeRadialLaw γ ν).prod Q).map coneTransport := by
  have hcont := h.ae_continuousOn_circle
  have hrad : Measurable fun ω => radialProcess (hcirc ω) :=
    IsQuantumCone.measurable_radialProcess h
  have hlat : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    CirclePairing.aemeasurable_lateralProcess h.measurable_pairing h.measurable_circle hcont
  have hpair : AEMeasurable (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) P :=
    hrad.aemeasurable.prodMk hlat
  have hsplit : P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) =
      (P.map (fun ω => radialProcess (hcirc ω))).prod (P.map (fun ω => lateralProcess (hC ω) (hcirc ω))) :=
    h.indep.map_prod_eq_prod_map_map hrad.aemeasurable hlat
  have hV : (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) =ᵐ[P]
      (fun ω => coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) := by
    filter_upwards [ae_coneObservable_eq_coneTransport hcont] with ω hω
    funext o
    exact hω o
  have hcomp : P.map (fun ω => coneTransport (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) =
      (P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω)))).map coneTransport :=
    (AEMeasurable.map_map_of_aemeasurable measurable_coneTransport.aemeasurable hpair).symm
  have hprod : P.map (fun ω => (radialProcess (hcirc ω), lateralProcess (hC ω) (hcirc ω))) =
      (quantumConeRadialLaw γ ν).prod Q := by
    rw [hsplit, hν, hQ]
  rw [Measure.map_congr hV, hcomp, hprod]

/-- **Finite-dimensional law with the lateral law of a whole-plane witness.** The same identity as
`map_finite_coneObservables_eq`, with the actual lateral law taken from the lateral clause `IsQuantumCone.lateral_law` of
the cone: it is the lateral law of some whole-plane GFF `(P', hC', hcirc')`. -/
theorem map_finite_coneObservables_eq_of_lateral_witness {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc)
    (ν : Measure (MarkovProcess.ContinuousPath ℝ))
    (hν : P.map (fun ω => radialProcess (hcirc ω)) = quantumConeRadialLaw γ ν)
    {n : ℕ} (c : Fin n → GFFObservable.Admissible) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧
      P.map (fun ω i => (c i).1.eval (hC ω) (hcirc ω)) =
        ((quantumConeRadialLaw γ ν).prod (P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω)))).map
          (fun p i => coneTransport p (c i)) := by
  obtain ⟨Ω', m', P', hC', hcirc', hP', hW, hlat⟩ := h.lateral_law
  let _ := m'
  exact ⟨Ω', m', P', hC', hcirc', hP', hW, map_finite_coneObservables_eq h ν hν _ hlat c⟩

/-- **Representation independence.** Two representations `h`, `h'` of the `γ`-quantum cone (possibly on different
probability spaces) have the same finite-dimensional laws of cone observables. The radial laws agree by
`IsQuantumCone.radial_law_eq` and the lateral laws by `IsQuantumCone.lateral_law_eq`; the law is then the one of
`map_finite_coneObservables_eq`, which depends only on the radial law and the lateral law. -/
theorem map_finite_coneObservables_eq_of_isQuantumCone {γ : ℝ}
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) (h' : IsQuantumCone γ P' hC' hcirc')
    {n : ℕ} (c : Fin n → GFFObservable.Admissible) :
    P.map (fun ω i => (c i).1.eval (hC ω) (hcirc ω)) =
      P'.map (fun ω i => (c i).1.eval (hC' ω) (hcirc' ω)) := by
  obtain ⟨ν, -, hν⟩ := h.radial_law
  have hν' : P'.map (fun ω => radialProcess (hcirc' ω)) = quantumConeRadialLaw γ ν := by
    rw [← hν]
    exact (IsQuantumCone.radial_law_eq h h').symm
  rw [map_finite_coneObservables_eq h ν hν _ rfl c, map_finite_coneObservables_eq h' ν hν' _ rfl c,
    IsQuantumCone.lateral_law_eq h h']

/-- **Representation independence of the joint law of all cone observables.** Two representations of the `γ`-quantum cone,
possibly on different probability spaces, have the same joint law of the admissible observables in the product σ-algebra. -/
theorem map_coneObservables_eq_of_isQuantumCone {γ : ℝ}
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) (h' : IsQuantumCone γ P' hC' hcirc') :
    P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) =
      P'.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC' ω) (hcirc' ω)) := by
  obtain ⟨ν, -, hν⟩ := h.radial_law
  have hν' : P'.map (fun ω => radialProcess (hcirc' ω)) = quantumConeRadialLaw γ ν := by
    rw [← hν]
    exact (IsQuantumCone.radial_law_eq h h').symm
  rw [map_coneObservables_eq h ν hν _ rfl, map_coneObservables_eq h' ν hν' _ rfl,
    IsQuantumCone.lateral_law_eq h h']

end MatedCRT.Sec1
