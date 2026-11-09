import MatedCRT.Proofs.Sec1.EnvironmentScaling.AngularLogIntegrability
import MatedCRT.Proofs.Sec1.EnvironmentScaling.CanonicalLateralLawAssembly
import MatedCRT.Proofs.Sec1.EnvironmentScaling.RadialLogMajorantProof

/-!
# Actual-cone observable integrability: fixed circles, countable families and tests

Component of `notes/env-steps/env-steps.tex:241-251` (Gaussian bounds, logarithmic majorant, through-zero angular
integrability and countable radial approximation), for the actual quantum cone of `IsQuantumCone`.

Hypotheses. Every statement assumes only the cone `IsQuantumCone γ P hC hcirc` (with `[IsProbabilityMeasure P]` where
the radial law is used). The radial log majorant `RadialLogMajorant` is not a premise here: it is derived from the
radial-law clause by `radialLogMajorant_of_isQuantumCone` (RadialLogMajorantProof.lean), and the angular integrals are
finite by the deterministic circle lemma `intervalIntegrable_radial_circle` (AngularLogIntegrability.lean). No `hlog`,
sublinearity or Gaussian band step premise appears, and no conclusion-shaped observable-integrability hypothesis is used.

Results. Event quantifiers are exact; `P`-almost sure statements are `∀ᵐ ω ∂P`.
* `ae_forall_radialLogMajorant_of_isQuantumCone`: a common majorant. On one event, for every radius `r` at once, the
  radial evaluations `t ↦ h_t(0)` obey `|h_t(0)| ≤ C_r (1 + |log t|)` on `(0, 2r]`. This is the event behind the
  stronger all-circle statement below.
* `aemeasurable_lateralCircle_of_isQuantumCone`: the lateral circle coordinate `ℓ(r,z)` is a.e. measurable for every
  `r > 0` and every `z`, circles through `0` included. `aemeasurable_lateralCircleArray_of_isQuantumCone`: the
  countable array along admissible circles `cc n = (r_n, z_n)` is a.e. measurable into `ℕ → ℝ`.
* `ae_intervalIntegrable_lateralCircle_of_isQuantumCone`, `ae_integrableOn_lateralCircle_of_isQuantumCone`: a fixed
  through-zero circle (`0 < r`, `‖z‖ = r`). `ae_intervalIntegrable_circle_of_isQuantumCone`: a fixed admissible circle
  (`0 < r`, any `z`); the circles away from `0` use only the joint continuity of the circle average process.
* `ae_circleArray_intervalIntegrable_of_isQuantumCone`, `ae_circleArray_integrableOn_of_isQuantumCone`: a countable
  family of admissible circles, one event for all `n` at once (the second is the through-zero form of
  `ae_circleArray_integrableOn`, with its premise `RadialLogMajorant` discharged).
* `ae_testPairing_countable_of_isQuantumCone`, `ae_countable_observables_of_isQuantumCone`: a countable family of test
  functions `φ m` with `IsTestFunction Set.univ (φ m)` together with the countable circles, on one event.
* `ae_forall_circle_intervalIntegrable_of_isQuantumCone`: the all-circle event, `∀ r z, 0 < r → …`, exposed separately.
  It is immediate from the common majorant and the joint continuity event, and it is stronger than the countable events.

Not claimed: continuity of `ℓ` in `(r, z)`, measurability of the lateral process for all circles at once, and any
environment-scaling closure.

Credit. `ae_circleArray_integrableOn_of_isQuantumCone` reuses `ae_circleArray_integrableOn`
(CanonicalLateralLawAssembly.lean), whose `Field` import uses Leonardo Bonanno's `LatticeProb` field modules
(`LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg`, `LatticeProb.Bonanno.LQGMetric.Field.Measurable`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open HarmonicBalls

namespace MatedCRT.Sec1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Angular integrand away from zero.** Let `g` be jointly continuous on `(0, ∞) × ℂ`. For a circle `(r, z)` with
`0 < r` and `‖z‖ ≠ r`, the circle does not pass through `0`: `‖z + r e^{iθ}‖ > 0` for every `θ`, so the integrand
`θ ↦ g(‖z + r e^{iθ}‖, 0)` is continuous on `ℝ` and interval integrable on `[0, 2π]`. No radial majorant is used. -/
theorem intervalIntegrable_circle_away_of_continuousOn {g : ℝ → ℂ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℂ => g p.1 p.2) (Ioi 0 ×ˢ univ)) {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ ≠ r) :
    IntervalIntegrable (fun θ : ℝ => g ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ 0) volume 0 (2 * Real.pi) := by
  have hpos : ∀ θ : ℝ, 0 < ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ := by
    intro θ
    refine norm_pos_iff.2 fun h0 => hz ?_
    rw [eq_neg_of_add_eq_zero_left h0, norm_neg, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hcts : Continuous fun θ : ℝ => (‖z + (r : ℂ) * exp (I * (θ : ℂ))‖, (0 : ℂ)) := by
    fun_prop
  have hmaps : ∀ θ : ℝ, (‖z + (r : ℂ) * exp (I * (θ : ℂ))‖, (0 : ℂ)) ∈ Ioi 0 ×ˢ (univ : Set ℂ) :=
    fun θ => ⟨hpos θ, mem_univ _⟩
  exact Continuous.intervalIntegrable (hg.comp_continuous hcts hmaps) _ _

/-- **Common radial log majorant of an actual cone.** Almost surely, for every radius `r` at once, the radial
evaluations `t ↦ h_t(0)` satisfy `|h_t(0)| ≤ C (1 + |log t|)` for `0 < t ≤ 2r`, with a constant `C` depending on `r`.
The event does not depend on `r`: it is the joint continuity event of the circle average process
(`IsQuantumCone.ae_continuousOn_circle`) intersected with the rational envelope event of the radial process, which comes
from the radial-law clause (`ae_isRationalEnvelope_innerRadial`). The deterministic inward bound `inward_log_bound` gives
one constant on `(0, 1]`, and the compact annulus `[1, 2r]` gives the constant on `[1, 2r]`. -/
theorem ae_forall_radialLogMajorant_of_isQuantumCone {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 2 * r → |hcirc ω t 0| ≤ C * (1 + |Real.log t|) := by
  filter_upwards [h.ae_continuousOn_circle, ae_isRationalEnvelope_innerRadial h] with ω hcont hE
  have hF : ContinuousOn (fun t : ℝ => hcirc ω t 0) (Ioi 0) :=
    MatedCRT.CirclePairing.continuousOn_radial hcont
  obtain ⟨n, hn⟩ := inward_log_bound hF hE
  intro r
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2 * r)).exists_bound_of_continuousOn
    (hF.mono fun t ht => lt_of_lt_of_le one_pos ht.1)
  refine ⟨max (n : ℝ) M, fun t ht0 ht2 => ?_⟩
  rcases le_total t 1 with ht1 | ht1
  · calc |hcirc ω t 0| ≤ (n : ℝ) * (1 + |Real.log t|) := hn t ht0 ht1
      _ ≤ max (n : ℝ) M * (1 + |Real.log t|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hb := hM t ⟨ht1, ht2⟩
    simp only [Real.norm_eq_abs] at hb
    calc |hcirc ω t 0| ≤ M := hb
      _ ≤ max (n : ℝ) M := le_max_right _ _
      _ ≤ max (n : ℝ) M * (1 + |Real.log t|) :=
          le_mul_of_one_le_right (le_trans (Nat.cast_nonneg n) (le_max_left _ _))
            (by linarith [abs_nonneg (Real.log t)])

/-- **Fixed through-zero circle, actual cone.** For `0 < r` and `‖z‖ = r`, almost surely the angular integrand
`θ ↦ h_{|z + r e^{iθ}|}(0)` is interval integrable on `[0, 2π]`. The only input is the cone hypothesis: the radial log
majorant at `r` is derived from the radial law (`radialLogMajorant_of_isQuantumCone`), not assumed. -/
theorem ae_intervalIntegrable_lateralCircle_of_isQuantumCone {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : ‖z‖ = r) :
    ∀ᵐ ω ∂P, IntervalIntegrable (fun θ : ℝ => hcirc ω ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ 0) volume 0 (2 * Real.pi) :=
  ae_intervalIntegrable_lateralCircle_through_zero h.ae_continuousOn_circle hr hz
    (radialLogMajorant_of_isQuantumCone h r)

/-- **Fixed through-zero circle, `IntegrableOn` form.** For `0 < r` and `‖z‖ = r`, almost surely the angular integrand is
integrable on `[0, 2π]`, so `∫_{[0,2π]} h_{|z + r e^{iθ}|}(0) dθ` is a finite Lebesgue integral. -/
theorem ae_integrableOn_lateralCircle_of_isQuantumCone {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : ‖z‖ = r) :
    ∀ᵐ ω ∂P, IntegrableOn (fun θ : ℝ => hcirc ω ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ 0) (Icc 0 (2 * Real.pi)) :=
  ae_integrableOn_lateralCircle_through_zero h.ae_continuousOn_circle hr hz
    (radialLogMajorant_of_isQuantumCone h r)

/-- **Fixed admissible circle, actual cone.** For `0 < r` and any centre `z` (through zero or not), almost surely the
angular integrand is interval integrable on `[0, 2π]`. Through-zero circles use the radial log majorant; the others
use only the joint continuity of the circle average process. -/
theorem ae_intervalIntegrable_circle_of_isQuantumCone {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) {z : ℂ} {r : ℝ}
    (hr : 0 < r) :
    ∀ᵐ ω ∂P, IntervalIntegrable (fun θ : ℝ => hcirc ω ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ 0) volume 0 (2 * Real.pi) := by
  by_cases hz : ‖z‖ = r
  · exact ae_intervalIntegrable_lateralCircle_of_isQuantumCone h hr hz
  · filter_upwards [h.ae_continuousOn_circle] with ω hω
    exact intervalIntegrable_circle_away_of_continuousOn (g := hcirc ω) hω hr hz

/-- **All admissible circles, one event (exposed separately).** Almost surely, for every radius `r > 0` and every centre
`z` at once, the angular integrand `θ ↦ h_{|z + r e^{iθ}|}(0)` is interval integrable on `[0, 2π]`. The event is the
intersection of the joint continuity event with the common radial log majorant event
(`ae_forall_radialLogMajorant_of_isQuantumCone`); it is stronger than the countable events below. -/
theorem ae_forall_circle_intervalIntegrable_of_isQuantumCone {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ (r : ℝ) (z : ℂ), 0 < r →
      IntervalIntegrable (fun θ : ℝ => hcirc ω ‖z + (r : ℂ) * exp (I * (θ : ℂ))‖ 0) volume 0 (2 * Real.pi) := by
  filter_upwards [h.ae_continuousOn_circle, ae_forall_radialLogMajorant_of_isQuantumCone h] with ω hcont hmaj
  intro r z hr
  by_cases hz : ‖z‖ = r
  · obtain ⟨C, hbd⟩ := hmaj r
    exact intervalIntegrable_radial_circle (MatedCRT.CirclePairing.continuousOn_radial hcont) hr hz
      (le_refl (2 * r)) hbd
  · exact intervalIntegrable_circle_away_of_continuousOn (g := hcirc ω) hcont hr hz

/-- **Lateral circle coordinate is a.e. measurable, actual cone.** For `0 < r` and every centre `z`, the lateral circle
coordinate `ℓ(r,z) = h_r(z) - Real.circleAverage (x ↦ h_{|x|}(0)) z r` is a.e. measurable, circles through `0` included.
It uses the measurability and joint continuity clauses of `IsQuantumCone` (`measurable_circle`, `ae_continuousOn_circle`). -/
theorem aemeasurable_lateralCircle_of_isQuantumCone {γ : ℝ} {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    AEMeasurable (fun ω => lateralCircleCoord hcirc r z ω) P :=
  aemeasurable_lateralCircle h.measurable_circle h.ae_continuousOn_circle hr z

/-- **Countable lateral array is a.e. measurable, actual cone.** For a countable family `cc n = (r_n, z_n)` of admissible
circles (`0 < r_n`), the array `ω ↦ (n ↦ ℓ(r_n, z_n))` is a.e. measurable into `ℕ → ℝ` with the product σ-algebra. -/
theorem aemeasurable_lateralCircleArray_of_isQuantumCone {γ : ℝ} {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) (cc : ℕ → ℝ × ℂ) (hcc : ∀ n, 0 < (cc n).1) :
    AEMeasurable (fun ω n => lateralCircleCoord hcirc (cc n).1 (cc n).2 ω) P :=
  AEMeasurable.of_eval fun n => aemeasurable_lateralCircle_of_isQuantumCone h (hcc n) (cc n).2

/-- **Countable admissible circles, one event.** Almost surely, for all `n` at once, the angular integrand of the circle
`(r_n, z_n)` is interval integrable on `[0, 2π]`, for every admissible circle of the family (`0 < r_n`, any centre). -/
theorem ae_circleArray_intervalIntegrable_of_isQuantumCone {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) (cc : ℕ → ℝ × ℂ)
    (hcc : ∀ n, 0 < (cc n).1) :
    ∀ᵐ ω ∂P, ∀ n, IntervalIntegrable
      (fun θ : ℝ => hcirc ω ‖(cc n).2 + ((cc n).1 : ℂ) * exp (I * (θ : ℂ))‖ 0) volume 0 (2 * Real.pi) :=
  (ae_forall_circle_intervalIntegrable_of_isQuantumCone h).mono fun _ hω n =>
    hω (cc n).1 (cc n).2 (hcc n)

/-- **Countable through-zero circles, one event (consumer form).** Almost surely, for all `n` at once, every circle of the
family through zero (`‖z_n‖ = r_n`) has an angular integrand integrable on `[0, 2π]`. This is
`ae_circleArray_integrableOn` (CanonicalLateralLawAssembly.lean) with its premise `RadialLogMajorant` at `r_n` discharged by
`radialLogMajorant_of_isQuantumCone`; no `hlog` premise remains. -/
theorem ae_circleArray_integrableOn_of_isQuantumCone {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) (cc : ℕ → ℝ × ℂ)
    (hcc : ∀ n, 0 < (cc n).1) :
    ∀ᵐ ω ∂P, ∀ n, ‖(cc n).2‖ = (cc n).1 →
      IntegrableOn (fun θ : ℝ => hcirc ω ‖(cc n).2 + ((cc n).1 : ℂ) * exp (I * (θ : ℂ))‖ 0)
        (Icc 0 (2 * Real.pi)) :=
  ae_circleArray_integrableOn h.ae_continuousOn_circle cc hcc
    (fun n _ => radialLogMajorant_of_isQuantumCone h (cc n).1)

/-- **Countable test functions, one event.** Almost surely, for all `m` at once, every test function `φ m` with
`IsTestFunction Set.univ (φ m)` gives the integrable pairing `x ↦ φ m x * h_{|x|}(0)`. This is
`ae_integrable_test_mul_radial`, read at the countable family. -/
theorem ae_testPairing_countable_of_isQuantumCone {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) (φ : ℕ → ℂ → ℝ) :
    ∀ᵐ ω ∂P, ∀ m : ℕ, IsTestFunction Set.univ (φ m) →
      Integrable (fun x : ℂ => φ m x * hcirc ω ‖x‖ 0) :=
  (ae_integrable_test_mul_radial h).mono fun _ hω m => hω (φ m)

/-- **Countable circles and countable tests, one event.** Almost surely: every through-zero circle of the countable family
`cc` has an integrable angular integrand on `[0, 2π]`, and every test function `φ m` of the countable family gives an
integrable pairing. The validity conditions are kept: `0 < (cc n).1` for the admissible circles, `IsTestFunction` for
the tests. -/
theorem ae_countable_observables_of_isQuantumCone {γ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsQuantumCone γ P hC hcirc) (cc : ℕ → ℝ × ℂ)
    (hcc : ∀ n, 0 < (cc n).1) (φ : ℕ → ℂ → ℝ) :
    ∀ᵐ ω ∂P, (∀ n, ‖(cc n).2‖ = (cc n).1 →
        IntegrableOn (fun θ : ℝ => hcirc ω ‖(cc n).2 + ((cc n).1 : ℂ) * exp (I * (θ : ℂ))‖ 0)
          (Icc 0 (2 * Real.pi))) ∧
      ∀ m : ℕ, IsTestFunction Set.univ (φ m) → Integrable (fun x : ℂ => φ m x * hcirc ω ‖x‖ 0) :=
  (ae_circleArray_integrableOn_of_isQuantumCone h cc hcc).and (ae_testPairing_countable_of_isQuantumCone h φ)

end MatedCRT.Sec1
