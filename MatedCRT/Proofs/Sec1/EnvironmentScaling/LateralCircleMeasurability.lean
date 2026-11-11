import MatedCRT.Proofs.Sec1.EnvironmentScaling.MeasurableAngularIntegrals
import MatedCRT.Proofs.Measurability.ConePairing

/-!
# Lateral circle observables of the actual field: angular integrals, countable arrays, lateral law

Sources: the lateral observables `ℓ(r,z)`, `ℓ(φ)` and finiteness of the lateral integrals, circles through zero; `Defs/QuantumCone.lean:63-68` (`lateralEval`, `lateralProcess`); the `lateral_law`
clause of `IsQuantumCone`, which stays an explicit hypothesis.

* `aemeasurable_lateralCircle`: the lateral circle coordinate `h_r(z) - Real.circleAverage (x ↦ h_{|x|}(0)) z r` is
  a.e. measurable for every `r > 0` and every `z`, circles through `0` included.
* `lateralCircleCoord_eq_normalized`: the same coordinate written with the angular integral
  `(2π)⁻¹ ∫_{[0,2π]} h_{|z + r e^{iθ}|}(0) dθ`.
* `ae_intervalIntegrable_lateralCircle_through_zero`, `ae_integrableOn_lateralCircle_through_zero`: for a circle through
  `0` (`‖z‖ = r`) the angular integrand has a logarithmic singularity; under the explicit radial log majorant
  `RadialLogMajorant` it is a.s. Lebesgue integrable on `[0, 2π]`.
* `lateralArray`: countably many lateral observables, read from the jointly measurable version
  `CirclePairing.lateralVersionEval` (ConePairing.lean). It is measurable as an `ℕ → ℝ`-valued map, equals the lateral
  process at all of its coordinates simultaneously on the a.s. continuity event, and its pullbacks by measurable
  functionals are measurable and a.s. equal to the pullbacks of the lateral process.
* `map_lateralArray_eq_of_lateral_law`, `lateralArray_law_of_isQuantumCone`: the law identity of `lateral_law` is an
  explicit hypothesis; it is pushed to the countable arrays. Measurability does not give that law, and the Gaussian
  covariance identification is not used here.

The a.e. measurability of the whole lateral process, `CirclePairing.aemeasurable_lateralProcess`, is reused, not
reproved.
-/

open MeasureTheory Set Filter Topology Complex
open HarmonicBalls

namespace MatedCRT.Sec1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The radial log majorant at the centre `0`, on the radii `(0, 2r]`: almost surely `|h_t(0)| ≤ C (1 + |log t|)`.
This is the analytic premise (sublinear growth of the radial process
`t ↦ h_{e^{-t}}(0)`); it is taken as an explicit hypothesis, not derived here. -/
def RadialLogMajorant (hcirc : Ω → ℝ → ℂ → ℝ) (P : Measure Ω) (r : ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 2 * r → |hcirc ω t 0| ≤ C * (1 + |Real.log t|)

omit [MeasurableSpace Ω] in
/-- The lateral circle coordinate of the field, `ℓ(r,z) = h_r(z) - Real.circleAverage (x ↦ h_{|x|}(0)) z r`: the
circle case of `MatedCRT.lateralEval` (Defs/QuantumCone.lean:63-66). -/
noncomputable def lateralCircleCoord (hcirc : Ω → ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  hcirc ω r z - Real.circleAverage (fun x => hcirc ω ‖x‖ 0) z r

omit [MeasurableSpace Ω] in
/-- The circle observable of `lateralEval` is the lateral circle coordinate. -/
lemma lateralEval_circle_eq (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) (ω : Ω) :
    MatedCRT.lateralEval (hC ω) (hcirc ω) (.circle r z) = lateralCircleCoord hcirc r z ω :=
  rfl

omit [MeasurableSpace Ω] in
/-- **Angular integral of the lateral circle coordinate.**  At the actual field,
`ℓ(r,z) = h_r(z) - (2π)⁻¹ ∫_{[0,2π]} h_{|z + r e^{iθ}|}(0) dθ`. -/
lemma lateralCircleCoord_eq_normalized (hcirc : Ω → ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) (ω : Ω) :
    lateralCircleCoord hcirc r z ω = hcirc ω r z - (2 * Real.pi)⁻¹ *
      ∫ θ in Icc 0 (2 * Real.pi), hcirc ω ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ 0 := by
  have h := circleAverage_eq_normalized (fun s => hcirc ω s 0) z r
  unfold lateralCircleCoord
  rw [h]

/-- **The lateral circle coordinate is a.e. measurable.**  Under measurable circle averages `ω ↦ h_r(z)` and an a.s.
continuous circle average process, `ω ↦ ℓ(r,z)` is a.e. measurable for every `r > 0` and every `z`; the angular part is
the specialization `X s ω = h_s(0)` of `aemeasurable_realCircleAverage`. -/
theorem aemeasurable_lateralCircle {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    AEMeasurable (fun ω => lateralCircleCoord hcirc r z ω) P := by
  have hX : ∀ᵐ ω ∂P, ContinuousOn (fun s => hcirc ω s 0) (Ioi 0) :=
    hcont.mono fun ω hω => MatedCRT.CirclePairing.continuousOn_radial hω
  have hA := aemeasurable_realCircleAverage P (fun s ω => hcirc ω s 0)
    (fun s hs => hmc s 0 hs) hX z hr
  exact (hmc r z hr).aemeasurable.sub hA

/-- **Circles through zero: the angular integrand is a.s. interval integrable.**  For `‖z‖ = r` the integrand
`θ ↦ h_{|z + r e^{iθ}|}(0)` has a logarithmic singularity at one angle; under the radial log
majorant it is a.s. interval integrable on `[0, 2π]`. -/
theorem ae_intervalIntegrable_lateralCircle_through_zero {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) (hlog : RadialLogMajorant hcirc P r) :
    ∀ᵐ ω ∂P, IntervalIntegrable
      (fun θ : ℝ => hcirc ω ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ 0) volume 0 (2 * Real.pi) := by
  have hX : ∀ᵐ ω ∂P, ContinuousOn (fun s => hcirc ω s 0) (Ioi 0) :=
    hcont.mono fun ω hω => MatedCRT.CirclePairing.continuousOn_radial hω
  exact ae_intervalIntegrable_circle_through_zero P (fun s ω => hcirc ω s 0) hX hr hz hlog

/-- **Finite angular integral on circles through zero.**  Almost surely the angular integrand is Lebesgue integrable on
`[0, 2π]`, so `∫_{[0,2π]} h_{|z + r e^{iθ}|}(0) dθ` is a genuine finite integral and `ℓ(r,z)` is a finite real number. -/
theorem ae_integrableOn_lateralCircle_through_zero {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ = r) (hlog : RadialLogMajorant hcirc P r) :
    ∀ᵐ ω ∂P, IntegrableOn
      (fun θ : ℝ => hcirc ω ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ 0) (Icc 0 (2 * Real.pi)) := by
  filter_upwards [ae_intervalIntegrable_lateralCircle_through_zero hcont hr hz hlog] with ω hω
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).1 hω

omit [MeasurableSpace Ω] in
/-- The countable array of lateral observables along the admissible coordinates `c n`, read from the jointly measurable
version `CirclePairing.lateralVersionEval` (ConePairing.lean). -/
noncomputable def lateralArray (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (c : ℕ → GFFObservable.Admissible) (ω : Ω) : ℕ → ℝ :=
  fun n => MatedCRT.CirclePairing.lateralVersionEval hC hcirc ω (c n).1

/-- **The countable lateral array is measurable** (product σ-algebra on `ℕ → ℝ`). -/
theorem measurable_lateralArray {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hmp : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) (c : ℕ → GFFObservable.Admissible) :
    Measurable (lateralArray hC hcirc c) := by
  refine Measurable.of_eval fun n => ?_
  exact (measurable_pi_apply (c n)).comp (MatedCRT.CirclePairing.measurable_lateralVersion hmp hmc)

omit [MeasurableSpace Ω] in
/-- On the a.s. continuity event of a single point `ω`, the countable array equals the lateral process at all of its
coordinates simultaneously (`ConePairing.lateralVersion_eq`: one event serves every coordinate). -/
theorem lateralArray_eq_of_continuousOn {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ω : Ω}
    (hc : ContinuousOn (fun s => hcirc ω s 0) (Ioi 0)) (c : ℕ → GFFObservable.Admissible) :
    lateralArray hC hcirc c ω = fun n => MatedCRT.lateralProcess (hC ω) (hcirc ω) (c n) := by
  funext n
  exact congrFun (MatedCRT.CirclePairing.lateralVersion_eq hc) (c n)

/-- Almost surely, the countable array equals the lateral process along `c`, at all coordinates at once. -/
theorem ae_lateralArray_eq {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (c : ℕ → GFFObservable.Admissible) :
    ∀ᵐ ω ∂P, lateralArray hC hcirc c ω = fun n => MatedCRT.lateralProcess (hC ω) (hcirc ω) (c n) := by
  filter_upwards [hcont] with ω hω
  exact lateralArray_eq_of_continuousOn (MatedCRT.CirclePairing.continuousOn_radial hω) c

/-- **Measurable array pullback.**  For a measurable functional `G` of the countable array, `ω ↦ G (ℓ(c ·)(ω))` is
measurable. -/
theorem measurable_lateralArray_pullback {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hmp : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) (c : ℕ → GFFObservable.Admissible)
    {E : Type*} [MeasurableSpace E] {G : (ℕ → ℝ) → E} (hG : Measurable G) :
    Measurable fun ω => G (lateralArray hC hcirc c ω) :=
  hG.comp (measurable_lateralArray hmp hmc c)

/-- The pullback equals, almost surely, the same functional of the lateral process along `c`. -/
theorem ae_pullback_lateralArray_eq {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (c : ℕ → GFFObservable.Admissible) {E : Type*} {G : (ℕ → ℝ) → E} :
    (fun ω => G (lateralArray hC hcirc c ω)) =ᵐ[P]
      fun ω => G (fun n => MatedCRT.lateralProcess (hC ω) (hcirc ω) (c n)) := by
  filter_upwards [ae_lateralArray_eq hcont c] with ω hω
  rw [hω]

/-- **The lateral law on countable arrays, from an explicit law identity.**  Given the identity of the laws of the
lateral processes, `P.map lateralProcess = P'.map lateralProcess'` (the `lateral_law` clause, taken as a hypothesis),
the laws of the countable lateral arrays along `c` agree.  Both lateral processes are a.e. measurable
(`CirclePairing.aemeasurable_lateralProcess`), so both push-forwards are genuine laws. -/
theorem map_lateralArray_eq_of_lateral_law {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hmp : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ)
    (hmc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hmp' : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC' ω φ)
    (hmc' : ∀ r z, 0 < r → Measurable fun ω => hcirc' ω r z)
    (hcont' : ∀ᵐ ω ∂P', ContinuousOn (fun p : ℝ × ℂ => hcirc' ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hlaw : P.map (fun ω => MatedCRT.lateralProcess (hC ω) (hcirc ω)) =
      P'.map (fun ω => MatedCRT.lateralProcess (hC' ω) (hcirc' ω)))
    (c : ℕ → GFFObservable.Admissible) :
    P.map (fun ω n => MatedCRT.lateralProcess (hC ω) (hcirc ω) (c n)) =
      P'.map (fun ω n => MatedCRT.lateralProcess (hC' ω) (hcirc' ω) (c n)) := by
  have hev : Measurable fun f : GFFObservable.Admissible → ℝ => fun n : ℕ => f (c n) :=
    Measurable.of_eval fun n => measurable_pi_apply (c n)
  have hA := MatedCRT.CirclePairing.aemeasurable_lateralProcess hmp hmc hcont
  have hA' := MatedCRT.CirclePairing.aemeasurable_lateralProcess hmp' hmc' hcont'
  calc P.map (fun ω n => MatedCRT.lateralProcess (hC ω) (hcirc ω) (c n))
      = (P.map (fun ω => MatedCRT.lateralProcess (hC ω) (hcirc ω))).map (fun f n => f (c n)) :=
        (AEMeasurable.map_map_of_aemeasurable hev.aemeasurable hA).symm
    _ = (P'.map (fun ω => MatedCRT.lateralProcess (hC' ω) (hcirc' ω))).map (fun f n => f (c n)) := by
        rw [hlaw]
    _ = P'.map (fun ω n => MatedCRT.lateralProcess (hC' ω) (hcirc' ω) (c n)) :=
        AEMeasurable.map_map_of_aemeasurable hev.aemeasurable hA'

/-- **The lateral law of a quantum cone, on countable arrays.**  The `lateral_law` clause of `IsQuantumCone` (kept
explicit: the existence of a whole-plane GFF `(P', hC', hcirc')` with the same lateral law) yields the same law for the
countable lateral arrays along any `c`.  The clause itself is not derived from measurability. -/
theorem lateralArray_law_of_isQuantumCone {γ : ℝ} {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hQ : MatedCRT.IsQuantumCone γ P hC hcirc)
    (c : ℕ → GFFObservable.Admissible) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ),
      IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧
      P.map (fun ω n => MatedCRT.lateralProcess (hC ω) (hcirc ω) (c n)) =
        P'.map (fun ω n => MatedCRT.lateralProcess (hC' ω) (hcirc' ω) (c n)) := by
  obtain ⟨Ω', inst, P', hC', hcirc', hP', hW, hlaw⟩ := hQ.lateral_law
  exact ⟨Ω', inst, P', hC', hcirc', hP', hW,
    map_lateralArray_eq_of_lateral_law hQ.measurable_pairing hQ.measurable_circle hQ.ae_continuousOn_circle
      hW.measurable_pairing hW.measurable_circle hW.ae_continuousOn_circle hlaw c⟩

end MatedCRT.Sec1
