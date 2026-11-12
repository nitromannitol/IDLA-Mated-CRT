import MatedCRT.FirstPass.Derived.ConeGFFCoupling2
import MatedCRT.FirstPass.S2y.ConeCircInt240

/-!
# The coupled whole-plane field has the lateral part of the quantum cone almost surely

Let `(hC, hcirc)` be the circle average embedding of a `γ`-quantum cone (`IsQuantumCone`, Definition 2.1) and let
`(coneCouplingPairing, coneGFFCircle)` be the field obtained by replacing its radial part
`h_{|x|}(0)` by `h_{|x|}(0) + γ log |x|` inside the unit disc and by `h_1(0) + w(log |x|) - w(0)` outside it, for a
continuous path `w`. The lateral part `h - h_{|·|}(0)` is unchanged on pairings for every sample, and on the circle
`∂B_r(z)` as soon as `x ↦ h_{|x|}(0)` is integrable on that circle (`lateralEval_coneGFF_circle`).

This file shows that the latter integrability holds almost surely for a fixed circle, also when the circle passes
through the origin, by the internal angular-integrability theorem `ae_intervalIntegrable_radial_circle` (which uses
only the measurability, the joint continuity and the radial law of the cone). Consequently, for every admissible
observable fixed in advance, almost surely the lateral observables of the coupled field and of the cone agree,
simultaneously for all continuous paths `w`.

* `measurable_comp_norm_of_continuousOn`: `x ↦ f(|x|)` is measurable when `f` is continuous on `(0, ∞)`.
* `circleIntegrable_log_norm`: `x ↦ log |x|` is integrable on every circle.
* `ae_circleIntegrable_coneRadial`: a.s. `x ↦ h_{|x|}(0)` is integrable on a fixed circle of positive radius.
* `lateralEval_coneGFF_circle_of_continuous`: the lateral circle average of the coupled field is that of the cone on
  every circle on which `x ↦ h_{|x|}(0)` is integrable.
* `ae_lateralProcess_coneGFF_apply`: the almost sure equality of the lateral processes at a fixed observable.
-/

open MeasureTheory Set HarmonicBalls
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- A function `f` continuous on `(0, ∞)`, composed with the norm, is measurable on `ℂ` (the value `f 0` at the
origin is a single point). -/
theorem measurable_comp_norm_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0)) :
    Measurable fun x : ℂ => f ‖x‖ := by
  classical
  have hm : Measurable ((Ioi (0 : ℝ)).piecewise f (fun _ => f 0)) :=
    hf.measurable_piecewise continuousOn_const measurableSet_Ioi
  have heq : (fun x : ℂ => f ‖x‖) = fun x => (Ioi (0 : ℝ)).piecewise f (fun _ => f 0) ‖x‖ := by
    funext x
    by_cases hx : 0 < ‖x‖
    · rw [Set.piecewise_eq_of_mem _ _ _ (show ‖x‖ ∈ Ioi (0 : ℝ) from hx)]
    · rw [Set.piecewise_eq_of_notMem _ _ _ (show ‖x‖ ∉ Ioi (0 : ℝ) from hx)]
      rw [le_antisymm (not_lt.1 hx) (norm_nonneg x)]
  rw [heq]
  exact hm.comp measurable_norm

/-- The radial profile `ρ ↦ c_ρ(0)` of a circle average process continuous on `(0, ∞) × ℂ` is continuous on
`(0, ∞)`. -/
theorem continuousOn_radial_of_continuousOn {c : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun ρ : ℝ => c ρ 0) (Ioi 0) :=
  hc.comp (f := fun ρ : ℝ => (ρ, (0 : ℂ))) (continuousOn_id.prodMk continuousOn_const)
    (fun _ hρ => ⟨hρ, mem_univ _⟩)

/-- `x ↦ log |x|` is integrable on every circle (also on circles through the origin). -/
theorem circleIntegrable_log_norm (z : ℂ) (r : ℝ) :
    CircleIntegrable (fun x : ℂ => Real.log ‖x‖) z r := by
  simpa using circleIntegrable_log_norm_sub_const (a := (0 : ℂ)) (c := z) r

section Cone

variable {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- For a `γ`-quantum cone and a fixed circle `∂B_r(z)`, `r > 0`, almost surely `x ↦ h_{|x|}(0)` is integrable on
that circle, also when the circle passes through the origin. -/
theorem ae_circleIntegrable_coneRadial (hQ : IsQuantumCone γ P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, CircleIntegrable (fun x => hcirc ω ‖x‖ 0) z r := by
  filter_upwards [MatedCRT.ae_intervalIntegrable_radial_circle hQ.measurable_circle
    hQ.ae_continuousOn_circle hQ.radial_law r z hr, hQ.ae_continuousOn_circle] with ω hω hc
  have hm : Measurable fun θ : ℝ => hcirc ω ‖circleMap z r θ‖ 0 :=
    (measurable_comp_norm_of_continuousOn (continuousOn_radial_of_continuousOn hc)).comp
      (continuous_circleMap z r).measurable
  unfold CircleIntegrable
  exact hω.mono_fun hm.aestronglyMeasurable (ae_of_all _ fun θ => by simp)

end Cone

/-- The coupled field has the lateral circle average of the cone on every circle on which `x ↦ h_{|x|}(0)` is
integrable, when `ρ ↦ h_ρ(0)` is continuous on `(0, ∞)` and the path `w` is continuous. -/
theorem lateralEval_coneGFF_circle_of_continuous (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) {hcirc : ℝ → ℂ → ℝ}
    {w : ℝ≥0 → ℝ} (hc : ContinuousOn (fun ρ => hcirc ρ 0) (Ioi 0)) (hw : Continuous w) {r : ℝ} {z : ℂ}
    (h₁ : CircleIntegrable (fun x => hcirc ‖x‖ 0) z r) :
    lateralEval (coneCouplingPairing γ hC hcirc w) (coneGFFCircle γ hcirc w) (.circle r z) =
      lateralEval hC hcirc (.circle r z) :=
  lateralEval_coneGFF_circle γ hC hcirc w h₁ (circleIntegrable_log_norm z r)
    (continuous_coneCouplingRemainder γ hc hw).continuousOn.circleIntegrable'

section Cone

variable {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- For a `γ`-quantum cone and an admissible observable `o` fixed in advance, almost surely the lateral observable
`o` of the coupled field equals that of the cone, simultaneously for all continuous paths `w`. -/
theorem ae_lateralProcess_coneGFF_apply (hQ : IsQuantumCone γ P hC hcirc) (o : GFFObservable.Admissible) :
    ∀ᵐ ω ∂P, ∀ w : ℝ≥0 → ℝ, Continuous w →
      lateralProcess (coneCouplingPairing γ (hC ω) (hcirc ω) w) (coneGFFCircle γ (hcirc ω) w) o =
        lateralProcess (hC ω) (hcirc ω) o := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ =>
    exact ae_of_all _ fun ω w _ => lateralEval_coneGFF_pairing γ (hC ω) (hcirc ω) w φ
  | circle r z =>
    filter_upwards [ae_circleIntegrable_coneRadial hQ (show 0 < r from ho) z,
      hQ.ae_continuousOn_circle] with ω h₁ hc w hw
    exact lateralEval_coneGFF_circle_of_continuous γ (hC ω)
      (continuousOn_radial_of_continuousOn hc) hw h₁

end Cone

end MatedCRT.FirstPass.Derived
