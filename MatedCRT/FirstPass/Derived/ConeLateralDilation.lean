import MatedCRT.FirstPass.LPBridge.LateralProcessAEMeasurable
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field
import HarmonicBalls.FirstPass.S11ak.Dilation

/-!
# Dilation invariance of the lateral circle averages of a quantum cone

The lateral part `h - h_{|·|}(0)` of a whole-plane GFF (and so of a quantum cone) is invariant in law under the
dilations `x ↦ R x`.  Here this is proved for the lateral circle averages
`h_r(z) - (average over ∂B_r(z) of x ↦ h_{|x|}(0))` indexed by the circles `∂B_r(z)` which do not pass through the
origin (`r ≠ |z|`): on these circles the radial function `x ↦ h_{|x|}(0)` is continuous, so the circle average is a
genuine integral and the lateral circle average of the dilated normalised field `h(R·) - h_R(0)` is the lateral circle
average of `h` over the dilated circle.  The dilated normalised field is again a whole-plane GFF
(`HarmonicBalls.S11ak.isWholePlaneGFF_dilate`), and two whole-plane GFFs have the same lateral law
(`IsWholePlaneGFF.lateral_law_eq`).

## Main results
* `IsWholePlaneGFF.map_lateralNonsingular_dilate`: the law of the lateral circle averages along the dilated circles is
  the law of the lateral circle averages.
* `IsQuantumCone.map_lateralNonsingular_dilate`: the same for a quantum cone.
-/

open MeasureTheory Filter Topology Set HarmonicBalls
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- The circles `∂B_r(z)` (`r > 0`) which do not pass through the origin. -/
abbrev NonsingularCircle : Type := {p : Set.Ioi (0 : ℝ) × ℂ // (p.1 : ℝ) ≠ ‖p.2‖}

/-- The dilation `(r, z) ↦ (R r, R z)` of the nonsingular circles, `R > 0`. -/
def dilateCircle {R : ℝ} (hR : 0 < R) (p : NonsingularCircle) : NonsingularCircle :=
  ⟨(⟨R * (p.1.1 : ℝ), mul_pos hR p.1.1.2⟩, (R : ℂ) * p.1.2), by
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    intro h'
    exact p.2 (mul_left_cancel₀ hR.ne' h')⟩

/-- The lateral circle averages of a sample along the nonsingular circles. -/
noncomputable def projCircle (l : GFFObservable.Admissible → ℝ) : NonsingularCircle → ℝ :=
  fun p => l ⟨GFFObservable.circle (p.1.1 : ℝ) p.1.2, p.1.1.2⟩

/-- The lateral circle averages along the dilated circles. -/
noncomputable def projCircleDil {R : ℝ} (hR : 0 < R) (l : GFFObservable.Admissible → ℝ) :
    NonsingularCircle → ℝ :=
  fun p => projCircle l (dilateCircle hR p)

lemma measurable_projCircle : Measurable projCircle :=
  Measurable.of_eval fun _ => measurable_pi_apply _

lemma measurable_projCircleDil {R : ℝ} (hR : 0 < R) : Measurable (projCircleDil hR) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- Circle averages under a dilation of the plane. -/
lemma circleAverage_dilate (g : ℂ → ℝ) {R r : ℝ} (z : ℂ) :
    Real.circleAverage g ((R : ℂ) * z) (R * r) = Real.circleAverage (fun x => g ((R : ℂ) * x)) z r := by
  have hmap : ∀ θ : ℝ, circleMap ((R : ℂ) * z) (R * r) θ = (R : ℂ) * circleMap z r θ := by
    intro θ
    simp only [circleMap]
    push_cast
    ring
  simp only [Real.circleAverage_def, hmap]

/-- The lateral circle average of the dilated normalised field over a nonsingular circle is the lateral circle average
of the field over the dilated circle. -/
lemma lateralProcess_dilate_circle {hC : (ℂ → ℝ) → ℝ} {hcirc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun s => hcirc s 0) (Ioi 0)) {R : ℝ} (hR : 0 < R) (p : NonsingularCircle) :
    projCircle (lateralProcess (S11ak.dilPairing R hC (hcirc R 0)) (S11ak.dilCirc R hcirc)) p =
      projCircleDil hR (lateralProcess hC hcirc) p := by
  obtain ⟨⟨⟨r, hr⟩, z⟩, hrz⟩ := p
  simp only [projCircle, projCircleDil, dilateCircle, lateralProcess, lateralEval, S11ak.dilCirc]
  have hcirc_int : ContinuousOn (fun x : ℂ => hcirc (R * ‖x‖) 0) (Metric.sphere z |r|) := by
    have hne : ∀ x ∈ Metric.sphere z |r|, 0 < ‖x‖ := by
      intro x hx
      rw [mem_sphere_iff_norm, abs_of_pos (show (0 : ℝ) < r from hr)] at hx
      by_contra hle
      have hx0 : x = 0 := norm_le_zero_iff.1 (not_lt.1 hle)
      rw [hx0, zero_sub, norm_neg] at hx
      exact hrz hx.symm
    exact hcont.comp (f := fun x : ℂ => R * ‖x‖) (by fun_prop : Continuous fun x : ℂ => R * ‖x‖).continuousOn
      (fun x hx => mul_pos hR (hne x hx))
  have hint : CircleIntegrable (fun x : ℂ => hcirc (R * ‖x‖) 0) z r :=
    ContinuousOn.circleIntegrable' (by simpa using hcirc_int)
  have hsub : Real.circleAverage (fun x : ℂ => hcirc (R * ‖x‖) (R * 0) - hcirc R 0) z r =
      Real.circleAverage (fun x : ℂ => hcirc (R * ‖x‖) 0) z r - hcirc R 0 := by
    simp only [mul_zero]
    rw [Real.circleAverage_fun_sub hint (circleIntegrable_const _ _ _), Real.circleAverage_const]
  have hscale : Real.circleAverage (fun y : ℂ => hcirc ‖y‖ 0) ((R : ℂ) * z) (R * r) =
      Real.circleAverage (fun x : ℂ => hcirc (R * ‖x‖) 0) z r := by
    rw [circleAverage_dilate]
    congr 1
    funext x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
  rw [hsub, hscale]
  ring


lemma map_comp_aemeasurable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure Ω} {f : α → β} (hf : Measurable f) {g : Ω → α} (hg : AEMeasurable g P) :
    P.map (fun ω => f (g ω)) = (P.map g).map f :=
  (AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hg).symm

/-- **Dilation invariance of the lateral circle averages of a whole-plane GFF.**  For `R > 0`, the lateral circle
averages along the circles `∂B_{R r}(R z)` have the same law as those along `∂B_r(z)` (nonsingular circles). -/
theorem map_lateralCircle_dilate_gff {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {R : ℝ} (hR : 0 < R) :
    P.map (fun ω => projCircleDil hR (lateralProcess (hC ω) (hcirc ω))) =
      P.map (fun ω => projCircle (lateralProcess (hC ω) (hcirc ω))) := by
  have hG' := S11ak.isWholePlaneGFF_dilate hG hR
  have hae : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    MatedCRT.ConeMeanZeroRestriction.lateralProcessAEMeasurable_holds.2 Ω P hC hcirc inferInstance hG
  have hae' : AEMeasurable (fun ω => lateralProcess (S11ak.dilPairing R (hC ω) (hcirc ω R 0))
      (S11ak.dilCirc R (hcirc ω))) P :=
    MatedCRT.ConeMeanZeroRestriction.lateralProcessAEMeasurable_holds.2 Ω P _ _ inferInstance hG'
  have h1 : (fun ω => projCircleDil hR (lateralProcess (hC ω) (hcirc ω))) =ᵐ[P]
      fun ω => projCircle (lateralProcess (S11ak.dilPairing R (hC ω) (hcirc ω R 0))
        (S11ak.dilCirc R (hcirc ω))) := by
    filter_upwards [hG.ae_continuousOn_circle] with ω hω
    have hcont : ContinuousOn (fun s => hcirc ω s 0) (Ioi 0) :=
      hω.comp (f := fun s : ℝ => (s, (0 : ℂ))) (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs, mem_univ _⟩)
    funext p
    exact (lateralProcess_dilate_circle hcont hR p).symm
  have h2 := MatedCRT.Sec1.IsWholePlaneGFF.lateral_law_eq hG' hG
  rw [Measure.map_congr h1, map_comp_aemeasurable measurable_projCircle hae', h2,
    ← map_comp_aemeasurable measurable_projCircle hae]

/-- **Dilation invariance of the lateral circle averages of a quantum cone** (the lateral part has the law of the
lateral part of a whole-plane GFF). -/
theorem map_lateralCircle_dilate_cone {Ω : Type} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsQuantumCone γ P hC hcirc) {R : ℝ} (hR : 0 < R) :
    P.map (fun ω => projCircleDil hR (lateralProcess (hC ω) (hcirc ω))) =
      P.map (fun ω => projCircle (lateralProcess (hC ω) (hcirc ω))) := by
  obtain ⟨Ω', m', P', hC', hcirc', hP', hG', hlaw⟩ := h.lateral_law
  let _ := m'
  have hae : AEMeasurable (fun ω => lateralProcess (hC ω) (hcirc ω)) P :=
    MatedCRT.ConeMeanZeroRestriction.lateralProcessAEMeasurable_holds.1 γ Ω P hC hcirc inferInstance h
  have hae' : AEMeasurable (fun ω => lateralProcess (hC' ω) (hcirc' ω)) P' :=
    MatedCRT.ConeMeanZeroRestriction.lateralProcessAEMeasurable_holds.2 Ω' P' hC' hcirc' hP' hG'
  have e1 : ∀ f : (GFFObservable.Admissible → ℝ) → (NonsingularCircle → ℝ), Measurable f →
      P.map (fun ω => f (lateralProcess (hC ω) (hcirc ω))) =
        P'.map (fun ω => f (lateralProcess (hC' ω) (hcirc' ω))) := by
    intro f hf
    rw [map_comp_aemeasurable hf hae, hlaw, ← map_comp_aemeasurable hf hae']
  rw [e1 _ (measurable_projCircleDil hR), e1 _ measurable_projCircle]
  exact map_lateralCircle_dilate_gff hG' hR

end MatedCRT.FirstPass.Derived
