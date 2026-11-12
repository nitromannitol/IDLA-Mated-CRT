import MatedCRT.FirstPass.Derived.ConeGFFCoupling
import LatticeProb.LQG.MassFunctional
import LatticeProb.LQG.LocalMeasureKernel2

/-!
# Coupling the quantum cone with a whole-plane field: exact form and continuity

The circle averages of the coupled whole-plane field `h^ℂ` of `ConeGFFCoupling` are written in the exact form
`h^ℂ_r(z) = h_r(z) + γ (log |·|)_r(z) - rem_r(z)` (`coneGFFCircle`), where `h` is the quantum cone and `rem` the
remainder of the coupling, which vanishes on the closed unit disk. Then:

* the cone is `h^ℂ - γ log |·|` plus the circle average of `rem`, at every radius and centre
  (`coneCircle_eq_addCircleAverage`), so the γ-LQG approximations of the cone are those of the field
  `h^ℂ - γ log |·|` shifted by the circle averages of a continuous function (Weyl scaling);
* `h^ℂ` has the radial profile of the coupling (`coneGFFCircle_norm`, `radialProcess_coneGFFCircle`) and the cone's
  lateral part on pairings and on every circle on which the radial part of the cone is integrable
  (`lateralEval_coneGFF_pairing`, `lateralEval_coneGFF_circle`);
* if the circle averages of the cone are continuous on `(0, ∞) × ℂ` and the path `w` is continuous, the remainder is
  continuous (`continuous_coneCouplingRemainder`) and so are the circle averages of `h^ℂ`
  (`continuousOn_coneGFFCircle`).
-/

open MeasureTheory Set HarmonicBalls
open scoped NNReal

namespace MatedCRT.FirstPass.Derived

/-- The circle averages of the whole-plane field coupled with the cone, in the exact form
`h_r(z) + γ (log |·|)_r(z) - rem_r(z)`. -/
noncomputable def coneGFFCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  hcirc r z + γ * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r -
    Real.circleAverage (coneCouplingRemainder γ hcirc w) z r

/-- **The cone is the coupled field minus `γ log |·|`, plus the circle average of the remainder**, at every radius and
centre. -/
theorem coneCircle_eq_addCircleAverage (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) :
    hcirc = LatticeProb.Gauss.addCircleAverage
      (LatticeProb.Gauss.fieldCircleAverage γ (coneGFFCircle γ hcirc w)) (coneCouplingRemainder γ hcirc w) := by
  funext r z
  simp only [LatticeProb.Gauss.addCircleAverage, LatticeProb.Gauss.fieldCircleAverage, coneGFFCircle]
  ring

/-- The circle average of the coupled field over `∂B_{|x|}(0)` is the radial profile at `x`. -/
theorem coneGFFCircle_norm (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) (x : ℂ) :
    coneGFFCircle γ hcirc w ‖x‖ 0 = coneCouplingRadial γ hcirc w x := by
  have hsph : ∀ y ∈ Metric.sphere (0 : ℂ) |‖x‖|, ‖y‖ = ‖x‖ := by
    intro y hy
    rw [mem_sphere_zero_iff_norm, abs_norm] at hy
    exact hy
  have h1 : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) 0 ‖x‖ = Real.log ‖x‖ :=
    Real.circleAverage_const_on_circle fun y hy => by rw [hsph y hy]
  have h2 : Real.circleAverage (coneCouplingRemainder γ hcirc w) 0 ‖x‖ = coneCouplingRemainder γ hcirc w x :=
    Real.circleAverage_const_on_circle fun y hy => by simp only [coneCouplingRemainder, hsph y hy]
  rw [coneGFFCircle, h1, h2, coneCouplingRadial_eq]

/-- The radial process only depends on the circle averages centred at the origin with positive radius. -/
theorem radialProcess_congr {f g : ℝ → ℂ → ℝ} (h : ∀ ρ : ℝ, 0 < ρ → f ρ 0 = g ρ 0) :
    radialProcess f = radialProcess g := by
  unfold radialProcess
  congr 1 <;> funext t <;> exact h _ (Real.exp_pos _)

/-- The radial process of the coupled field: `t ↦ h_{e^{-t}}(0) - γ t` and `s ↦ h_1(0) + w(s) - w(0)`. -/
theorem radialProcess_coneGFFCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ) :
    radialProcess (coneGFFCircle γ hcirc w) =
      (fun t : ℝ≥0 => hcirc (Real.exp (-(t : ℝ))) 0 - γ * t, fun s : ℝ≥0 => hcirc 1 0 + (w s - w 0)) := by
  rw [← radialProcess_coneCouplingCircle γ hcirc w]
  apply radialProcess_congr
  intro ρ hρ
  have h1 := coneGFFCircle_norm γ hcirc w (ρ : ℂ)
  have h2 := coneCouplingCircle_norm γ hcirc w (ρ : ℂ)
  rw [Complex.norm_of_nonneg hρ.le] at h1 h2
  rw [h1, h2]

/-- The coupled field has the cone's lateral pairings. -/
theorem lateralEval_coneGFF_pairing (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ)
    (φ : ℂ → ℝ) :
    lateralEval (coneCouplingPairing γ hC hcirc w) (coneGFFCircle γ hcirc w) (.pairing φ) =
      lateralEval hC hcirc (.pairing φ) := by
  simp only [lateralEval, coneCouplingPairing, coneGFFCircle_norm]
  ring

/-- The coupled field has the cone's lateral circle average on every circle on which the radial part of the cone,
`log |·|` and the remainder are integrable. -/
theorem lateralEval_coneGFF_circle (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ℝ≥0 → ℝ)
    {r : ℝ} {z : ℂ} (h₁ : CircleIntegrable (fun x => hcirc ‖x‖ 0) z r)
    (h₂ : CircleIntegrable (fun x : ℂ => Real.log ‖x‖) z r)
    (h₃ : CircleIntegrable (coneCouplingRemainder γ hcirc w) z r) :
    lateralEval (coneCouplingPairing γ hC hcirc w) (coneGFFCircle γ hcirc w) (.circle r z) =
      lateralEval hC hcirc (.circle r z) := by
  have key := circle_eq_fieldCircleAverage_coneCoupling_add γ hcirc w h₁ h₂ h₃
  rw [fieldCircleAverage, coneCouplingCircle] at key
  have hfun : (fun x : ℂ => coneGFFCircle γ hcirc w ‖x‖ 0) = coneCouplingRadial γ hcirc w :=
    funext (coneGFFCircle_norm γ hcirc w)
  simp only [lateralEval]
  rw [hfun, coneGFFCircle]
  linarith

/-- The remainder of the coupling is continuous when `ρ ↦ h_ρ(0)` is continuous on `(0, ∞)` and `w` is continuous. -/
theorem continuous_coneCouplingRemainder (γ : ℝ) {hcirc : ℝ → ℂ → ℝ} {w : ℝ≥0 → ℝ}
    (hc : ContinuousOn (fun ρ => hcirc ρ 0) (Ioi 0)) (hw : Continuous w) :
    Continuous (coneCouplingRemainder γ hcirc w) := by
  unfold coneCouplingRemainder
  refine continuous_if_le continuous_norm continuous_const continuousOn_const ?_ ?_
  · have hpos : ∀ x ∈ {x : ℂ | 1 ≤ ‖x‖}, 0 < ‖x‖ := fun x hx => lt_of_lt_of_le one_pos hx
    have hn : ContinuousOn (fun x : ℂ => hcirc ‖x‖ 0) {x : ℂ | 1 ≤ ‖x‖} :=
      hc.comp continuous_norm.continuousOn fun x hx => hpos x hx
    have hlog : ContinuousOn (fun x : ℂ => Real.log ‖x‖) {x : ℂ | 1 ≤ ‖x‖} :=
      continuous_norm.continuousOn.log fun x hx => (hpos x hx).ne'
    have hwl : ContinuousOn (fun x : ℂ => w (Real.toNNReal (Real.log ‖x‖))) {x : ℂ | 1 ≤ ‖x‖} :=
      hw.comp_continuousOn (continuous_real_toNNReal.comp_continuousOn hlog)
    exact ((hn.sub continuousOn_const).sub (hwl.sub continuousOn_const)).add (continuousOn_const.mul hlog)
  · intro x hx
    simp [hx]

/-- The circle averages of the coupled field are continuous on `(0, ∞) × ℂ` when those of the cone are and the path
`w` is continuous. -/
theorem continuousOn_coneGFFCircle (γ : ℝ) {hcirc : ℝ → ℂ → ℝ} {w : ℝ≥0 → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (hw : Continuous w) :
    ContinuousOn (fun p : ℝ × ℂ => coneGFFCircle γ hcirc w p.1 p.2) (Ioi 0 ×ˢ univ) := by
  have hc : ContinuousOn (fun ρ => hcirc ρ 0) (Ioi 0) :=
    hcont.comp (continuous_id.prodMk continuous_const).continuousOn fun ρ hρ => ⟨hρ, mem_univ _⟩
  have hrem := LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center
    (continuous_coneCouplingRemainder γ hc hw)
  have hlog : ContinuousOn (fun p : ℝ × ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) p.2 p.1)
      (Ioi 0 ×ˢ univ) := by
    have heq : EqOn (fun p : ℝ × ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) p.2 p.1)
        (fun p => Real.log (max p.1 ‖p.2‖)) (Ioi 0 ×ˢ univ) := fun p hp =>
      LatticeProb.LocalMeasureKernel.LocalDecoderCommon.circleAverage_log_norm_eq_max hp.1 p.2
    refine ContinuousOn.congr ?_ heq
    refine (continuous_fst.max (continuous_norm.comp continuous_snd)).continuousOn.log ?_
    intro p hp
    exact (lt_of_lt_of_le hp.1 (le_max_left _ _)).ne'
  exact (hcont.add (continuousOn_const.mul hlog)).sub hrem.continuousOn

end MatedCRT.FirstPass.Derived
