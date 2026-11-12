import MatedCRT.FirstPass.LPBridge.WholePlaneContinuousVersion
import MatedCRT.Defs.QuantumCone
import LatticeProb.LQG.MassFunctional
import LatticeProb.LQG.LocalMeasureKernel2

/-!
# Cone data from a whole-plane GFF and an independent path: definitions, continuity, measurability

Let `(hC₁, hcirc₁)` be the pairings and circle averages of a whole-plane GFF `h^ℂ` (normalized so that
`h^ℂ_1(0) = 0` almost surely) and `w` a continuous path (a sample of the conditioned Brownian motion `B̂`). The field
of the `γ`-quantum cone built from them is `h = h^ℂ - γ log |·|` on the closed unit disk, with the radial part
`s ↦ h_{e^s}(0)` replaced outside the unit disk by `w(s) - γ s`. Writing `ρ = |x|` and
`c(ρ) = h^ℂ_ρ(0)`, the replacement is the continuous radial function
`coneRefProfile c w ρ = (w(log⁺ ρ) - w(0)) - (c(max ρ 1) - c(1))`, which vanishes for `ρ ≤ 1` and equals
`w(log ρ) - w(0) - c(ρ) + c(1)` for `ρ ≥ 1`; the cone circle averages and pairings add `coneRefProfile` to those of
`h^ℂ - γ log |·|` (`coneRefCircle`, `coneRefPairing`).

This file proves: for continuous `c` and `w`, the profile is continuous on `ℂ` and the cone circle averages are
continuous on `(0, ∞) × ℂ`; and, on the product space `Ω₁ × C(ℝ≥0, ℝ)`, the profile is jointly measurable, so the
cone pairings and the cone circle averages are random variables.
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set HarmonicBalls MarkovProcess
open scoped NNReal

/-- The radial correction of the cone built from a radial profile `hc ρ = h^ℂ_ρ(0)` and a path `w`:
`(w(log⁺ ρ) - w(0)) - (hc(max ρ 1) - hc(1))`. It vanishes for `ρ ≤ 1`. -/
noncomputable def coneRefProfile (hc : ℝ → ℝ) (w : ContinuousPath ℝ) (ρ : ℝ) : ℝ :=
  (w (Real.log (max ρ 1)).toNNReal - w 0) - (hc (max ρ 1) - hc 1)

/-- The radial correction as a function on the plane. -/
noncomputable def coneRefField (hcirc : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ) (x : ℂ) : ℝ :=
  coneRefProfile (fun ρ => hcirc ρ 0) w ‖x‖

/-- The circle averages of the cone built from the circle averages `hcirc` of a whole-plane GFF `h^ℂ` and a path `w`:
those of `h = h^ℂ - γ log |·|` plus the circle averages of the radial correction. -/
noncomputable def coneRefCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  fieldCircleAverage γ hcirc r z + Real.circleAverage (coneRefField hcirc w) z r

/-- The pairings of the cone built from the pairings `hC` of a whole-plane GFF `h^ℂ` and a path `w`:
those of `h = h^ℂ - γ log |·|` plus the pairings with the radial correction. -/
noncomputable def coneRefPairing (γ : ℝ) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (w : ContinuousPath ℝ)
    (φ : ℂ → ℝ) : ℝ :=
  fieldPairing γ hC φ + ∫ x, φ x * coneRefField hcirc w x

theorem coneRefProfile_of_le {hc : ℝ → ℝ} {w : ContinuousPath ℝ} {ρ : ℝ} (h : ρ ≤ 1) :
    coneRefProfile hc w ρ = 0 := by
  have : max ρ 1 = 1 := max_eq_right h
  simp [coneRefProfile, this]

/-- Continuity of the radial correction on the plane. -/
theorem continuous_coneRefField {hcirc : ℝ → ℂ → ℝ}
    (hc : ContinuousOn (fun ρ => hcirc ρ 0) (Ioi 0)) (w : ContinuousPath ℝ) :
    Continuous (coneRefField hcirc w) := by
  unfold coneRefField coneRefProfile
  have hm : Continuous fun x : ℂ => max ‖x‖ 1 := continuous_norm.max continuous_const
  have hpos : ∀ x : ℂ, 0 < max ‖x‖ 1 := fun x => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlog : Continuous fun x : ℂ => Real.log (max ‖x‖ 1) := hm.log fun x => (hpos x).ne'
  have h1 : Continuous fun x : ℂ => w (Real.log (max ‖x‖ 1)).toNNReal :=
    w.continuous.comp (continuous_real_toNNReal.comp hlog)
  have h2 : Continuous fun x : ℂ => hcirc (max ‖x‖ 1) 0 :=
    hc.comp_continuous hm fun x => hpos x
  exact (h1.sub continuous_const).sub (h2.sub continuous_const)

/-- The circle averages of the cone are continuous on `(0, ∞) × ℂ` when those of the whole-plane GFF are. -/
theorem continuousOn_coneRefCircle (γ : ℝ) {hcirc : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Ioi 0 ×ˢ univ)) (w : ContinuousPath ℝ) :
    ContinuousOn (fun p : ℝ × ℂ => coneRefCircle γ hcirc w p.1 p.2) (Ioi 0 ×ˢ univ) := by
  have hc : ContinuousOn (fun ρ => hcirc ρ 0) (Ioi 0) :=
    hcont.comp (continuous_id.prodMk continuous_const).continuousOn fun ρ hρ => ⟨hρ, mem_univ _⟩
  have hrem := LatticeProb.Gauss.Section6.continuous_circleAverage_radius_center
    (continuous_coneRefField hc w)
  have hlog : ContinuousOn (fun p : ℝ × ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) p.2 p.1)
      (Ioi 0 ×ˢ univ) := by
    have heq : EqOn (fun p : ℝ × ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) p.2 p.1)
        (fun p => Real.log (max p.1 ‖p.2‖)) (Ioi 0 ×ˢ univ) := fun p hp =>
      LatticeProb.LocalMeasureKernel.LocalDecoderCommon.circleAverage_log_norm_eq_max hp.1 p.2
    refine ContinuousOn.congr ?_ heq
    refine (continuous_fst.max (continuous_norm.comp continuous_snd)).continuousOn.log ?_
    intro p hp
    exact (lt_of_lt_of_le hp.1 (le_max_left _ _)).ne'
  unfold coneRefCircle fieldCircleAverage
  exact (hcont.sub (continuousOn_const.mul hlog)).add hrem.continuousOn

section Measurable

variable {Ω₁ : Type*} [MeasurableSpace Ω₁] {hcirc : Ω₁ → ℝ → ℂ → ℝ}

/-- Joint measurability of the evaluation of a continuous path. -/
theorem measurable_eval_uncurry :
    Measurable fun q : ℝ≥0 × ContinuousPath ℝ => q.2 q.1 :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (s : ℝ≥0) (w : ContinuousPath ℝ) => w s) (fun w => w.continuous)
    fun s => (continuous_eval_const s).measurable

/-- The radial correction is jointly measurable in the point `x`, the GFF sample and the path, given that the GFF
circle averages are jointly measurable in `(r, z, ω₁)`. -/
theorem measurable_coneRefField
    (hmeas : Measurable fun q : (Ioi (0 : ℝ) × ℂ) × Ω₁ => hcirc q.2 q.1.1 q.1.2) :
    Measurable fun q : ℂ × (Ω₁ × ContinuousPath ℝ) => coneRefField (hcirc q.2.1) q.2.2 q.1 := by
  unfold coneRefField coneRefProfile
  have hmx : Measurable fun q : ℂ × (Ω₁ × ContinuousPath ℝ) => max ‖q.1‖ 1 :=
    (measurable_norm.comp measurable_fst).max measurable_const
  have hpos : ∀ q : ℂ × (Ω₁ × ContinuousPath ℝ), 0 < max ‖q.1‖ 1 := fun q =>
    lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlog : Measurable fun q : ℂ × (Ω₁ × ContinuousPath ℝ) => (Real.log (max ‖q.1‖ 1)).toNNReal :=
    measurable_real_toNNReal.comp (Real.measurable_log.comp hmx)
  have h1 : Measurable fun q : ℂ × (Ω₁ × ContinuousPath ℝ) => q.2.2 (Real.log (max ‖q.1‖ 1)).toNNReal :=
    measurable_eval_uncurry.comp (hlog.prodMk (measurable_snd.comp measurable_snd))
  have h0 : Measurable fun q : ℂ × (Ω₁ × ContinuousPath ℝ) => q.2.2 0 :=
    measurable_eval_uncurry.comp (measurable_const.prodMk (measurable_snd.comp measurable_snd))
  have h2 : Measurable fun q : ℂ × (Ω₁ × ContinuousPath ℝ) => hcirc q.2.1 (max ‖q.1‖ 1) 0 := by
    have hsub : Measurable fun q : ℂ × (Ω₁ × ContinuousPath ℝ) => (⟨max ‖q.1‖ 1, hpos q⟩ : Ioi (0 : ℝ)) :=
      hmx.subtype_mk
    exact hmeas.comp ((hsub.prodMk measurable_const).prodMk (measurable_fst.comp measurable_snd))
  have h3 : Measurable fun q : ℂ × (Ω₁ × ContinuousPath ℝ) => hcirc q.2.1 1 0 := by
    have h1pos : (1 : ℝ) ∈ Ioi (0 : ℝ) := by norm_num
    have : Measurable fun _ : ℂ × (Ω₁ × ContinuousPath ℝ) =>
        (Prod.mk (Subtype.mk (1 : ℝ) h1pos) (0 : ℂ) : Ioi (0 : ℝ) × ℂ) := measurable_const
    exact hmeas.comp (this.prodMk (measurable_fst.comp measurable_snd))
  exact (h1.sub h0).sub (h2.sub h3)


variable {hC : Ω₁ → (ℂ → ℝ) → ℝ}

/-- Each pairing of the cone with a test function is a random variable. -/
theorem measurable_coneRefPairing (γ : ℝ)
    (hmeas : Measurable fun q : (Ioi (0 : ℝ) × ℂ) × Ω₁ => hcirc q.2 q.1.1 q.1.2)
    (hpair : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Measurable fun p : Ω₁ × ContinuousPath ℝ => coneRefPairing γ (hC p.1) (hcirc p.1) p.2 φ := by
  unfold coneRefPairing fieldPairing
  refine (((hpair φ hφ).comp measurable_fst).sub measurable_const).add ?_
  have hF := measurable_coneRefField hmeas
  have hφm : Measurable φ := hφ.1.continuous.measurable
  have hu : Measurable fun q : (Ω₁ × ContinuousPath ℝ) × ℂ =>
      φ q.2 * coneRefField (hcirc q.1.1) q.1.2 q.2 :=
    (hφm.comp measurable_snd).mul (hF.comp measurable_swap)
  exact (hu.stronglyMeasurable.integral_prod_right (ν := volume)).measurable

/-- Each circle average of positive radius of the cone is a random variable. -/
theorem measurable_coneRefCircle (γ : ℝ)
    (hmeas : Measurable fun q : (Ioi (0 : ℝ) × ℂ) × Ω₁ => hcirc q.2 q.1.1 q.1.2)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Measurable fun p : Ω₁ × ContinuousPath ℝ => coneRefCircle γ (hcirc p.1) p.2 r z := by
  unfold coneRefCircle fieldCircleAverage
  have hcirc1 : Measurable fun ω => hcirc ω r z := by
    have hr' : r ∈ Ioi (0 : ℝ) := hr
    exact hmeas.comp (measurable_const.prodMk measurable_id :
      Measurable fun ω : Ω₁ => (((⟨r, hr'⟩ : Ioi (0 : ℝ)), z), ω))
  have hcirc2 : Measurable fun p : Ω₁ × ContinuousPath ℝ =>
      Real.circleAverage (coneRefField (hcirc p.1) p.2) z r := by
    simp only [Real.circleAverage_def]
    refine Measurable.const_smul (?_ : Measurable fun p : Ω₁ × ContinuousPath ℝ =>
      ∫ θ in (0 : ℝ)..2 * Real.pi, coneRefField (hcirc p.1) p.2 (circleMap z r θ)) ((2 * Real.pi)⁻¹)
    have hfun : (fun p : Ω₁ × ContinuousPath ℝ =>
        ∫ θ in (0 : ℝ)..2 * Real.pi, coneRefField (hcirc p.1) p.2 (circleMap z r θ)) =
        fun p => ∫ θ in Ioc 0 (2 * Real.pi), coneRefField (hcirc p.1) p.2 (circleMap z r θ) :=
      funext fun p => intervalIntegral.integral_of_le (by positivity)
    rw [hfun]
    have hu : Measurable fun q : (Ω₁ × ContinuousPath ℝ) × ℝ =>
        coneRefField (hcirc q.1.1) q.1.2 (circleMap z r q.2) :=
      (measurable_coneRefField hmeas).comp
        (Measurable.prodMk ((continuous_circleMap z r).measurable.comp measurable_snd) measurable_fst)
    exact (hu.stronglyMeasurable.integral_prod_right
      (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).measurable
  exact ((hcirc1.comp measurable_fst).sub measurable_const).add hcirc2

end Measurable

end MatedCRT.FirstPass.Derived
