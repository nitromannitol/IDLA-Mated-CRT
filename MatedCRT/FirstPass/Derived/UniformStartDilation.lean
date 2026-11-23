import MatedCRT.FirstPass.Derived.UniformStartVariableRadiusTransfer
import MatedCRT.FirstPass.Derived.CmpEDistKnots
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ExitTimeClockChange
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkContinuity
import HarmonicBalls.Proofs.Sec6.BrownianScaling

/-!
# Dilation of stopped paths, of curves modulo time parametrization and of planar Brownian motion

Deterministic and Brownian scaling facts used to compare the stopped embedded walk at a mesh `ε` with the walk of a
cone-rescaled environment at a reciprocal mesh:

* `pathExitTime_ball_mul`, `stopAtExit_ball_mul`: the dilate `r f` of a path leaves `B_{rR}(0)` when `f` leaves
  `B_R(0)`, and the stopped dilate is the dilate of the stopped path;
* `stopAtExit_comp_mul`: stopping commutes with a positive linear change of time;
* `cmpEDist_mul_comp_mul_lt`: a dilation by `r` multiplies `cmpEDist` by `r`, and a linear change of time does not
  change it;
* `interpolatedWalk_eq_mul_of_vertexPoint`: dilated embedded vertices give the dilated interpolated walk;
* `planarBrownianMotion_mul_apply`: planar Brownian motion from `r z` is the image of planar Brownian motion from
  `z` under `b ↦ r b(r⁻² ·)` (Brownian scaling), for the measure of every set of paths.
-/

set_option autoImplicit false

open Set Metric MeasureTheory HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.UniformStartDilation

/-- The dilate `r f` of a path leaves `B_{rR}(0)` exactly when `f` leaves `B_R(0)`. -/
theorem pathExitTime_ball_mul {r : ℝ} (hr : 0 < r) (R : ℝ) (f : ℝ≥0 → ℂ) :
    pathExitTime (ball (0 : ℂ) (r * R)) (fun t => (r : ℂ) * f t) = pathExitTime (ball (0 : ℂ) R) f := by
  have h : ∀ t, ((r : ℂ) * f t ∈ ball (0 : ℂ) (r * R) ↔ f t ∈ ball (0 : ℂ) R) := by
    intro t
    rw [mem_ball_zero_iff, mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact ⟨fun h => lt_of_mul_lt_mul_left h hr.le, fun h => mul_lt_mul_of_pos_left h hr⟩
  unfold pathExitTime
  simp only [h]

/-- The dilate `r f` stopped at its exit from `B_{rR}(0)` is the dilate of `f` stopped at its exit from `B_R(0)`. -/
theorem stopAtExit_ball_mul {r : ℝ} (hr : 0 < r) (R : ℝ) (f : ℝ≥0 → ℂ) :
    stopAtExit (ball (0 : ℂ) (r * R)) (fun t => (r : ℂ) * f t) =
      fun t => (r : ℂ) * stopAtExit (ball (0 : ℂ) R) f t := by
  funext t
  unfold stopAtExit
  rw [pathExitTime_ball_mul hr R f]

/-- Stopping at the exit from an open set commutes with the positive linear change of time `t ↦ c t`. -/
theorem stopAtExit_comp_mul {U : Set ℂ} (hU : IsOpen U) (b : ContinuousPath ℂ) {c : ℝ≥0} (hc : 0 < c) :
    stopAtExit U (fun t => b (c * t)) = fun t => stopAtExit U ⇑b (c * t) := by
  have hψ : StrictMono fun t : ℝ≥0 => c * t := fun s t hst => mul_lt_mul_of_pos_left hst hc
  have hφ : ∀ s : ℝ≥0, c * (c⁻¹ * s) = s := fun s => mul_inv_cancel_left₀ hc.ne' s
  have hE := pathExitTime_comp hU b hψ hφ
  funext t
  unfold stopAtExit
  by_cases htop : pathExitTime U ⇑b = ⊤
  · simp only [hE, htop, ↓reduceIte, eq_self]
  · simp only [hE, htop, ↓reduceIte, ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
    generalize (pathExitTime U ⇑b).toNNReal = σ
    congr 1
    rcases le_total t (c⁻¹ * σ) with h | h
    · have h' : c * t ≤ σ := by
        have h2 : c * t ≤ c * (c⁻¹ * σ) := by gcongr
        rwa [hφ] at h2
      rw [min_eq_left h, min_eq_left h']
    · have h' : σ ≤ c * t := by
        have h2 : c * (c⁻¹ * σ) ≤ c * t := by gcongr
        rwa [hφ] at h2
      rw [min_eq_right h, min_eq_right h', hφ]

/-- **Dilation and linear time change of curves modulo time parametrization.** If `cmpEDist F G < a` and
`r a ≤ d` with `r > 0`, then the dilate `r F` and the dilated, linearly time-changed path `t ↦ r G (c t)` are at
`cmpEDist`-distance less than `d`. -/
theorem cmpEDist_mul_comp_mul_lt {F G : ℝ≥0 → ℂ} {a r d : ℝ} (hr : 0 < r) {c : ℝ≥0} (hc : 0 < c)
    (h : cmpEDist F G < ENNReal.ofReal a) (had : r * a ≤ d) :
    cmpEDist (fun t => (r : ℂ) * F t) (fun t => (r : ℂ) * G (c * t)) < ENNReal.ofReal d := by
  have hφ' := h
  unfold cmpEDist at hφ'
  obtain ⟨φ, hφ⟩ := iInf_lt_iff.1 hφ'
  obtain ⟨q, hq0, hXq, hqa⟩ := ENNReal.lt_iff_exists_real_btwn.1 hφ
  have hqa' : q < a := by
    have := ENNReal.toReal_lt_of_lt_ofReal hqa
    rwa [ENNReal.toReal_ofReal hq0] at this
  let ψ : ℝ≥0 ≃o ℝ≥0 := φ.trans (OrderIso.mulLeft₀ c⁻¹ (inv_pos.2 hc))
  have hψ : ∀ t, c * ψ t = φ t := fun t => mul_inv_cancel_left₀ hc.ne' (φ t)
  have hdist : ∀ t, dist ((r : ℂ) * F t) ((r : ℂ) * G (c * ψ t)) ≤ r * q := by
    intro t
    rw [hψ, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, ← dist_eq_norm]
    have hlt : edist (F t) (G (φ t)) < ENNReal.ofReal q :=
      lt_of_le_of_lt (le_iSup (fun t => edist (F t) (G (φ t))) t) hXq
    exact mul_le_mul_of_nonneg_left (edist_lt_ofReal.1 hlt).le hr.le
  refine lt_of_le_of_lt (CmpEDistKnots.cmpEDist_le_of_orderIso (f := fun t => (r : ℂ) * F t)
    (g := fun t => (r : ℂ) * G (c * t)) ψ hdist) ?_
  have hd : 0 < d := lt_of_lt_of_le (mul_pos hr (lt_of_le_of_lt hq0 hqa')) had
  exact (ENNReal.ofReal_lt_ofReal_iff hd).2 (lt_of_lt_of_le (mul_lt_mul_of_pos_left hqa' hr) had)

/-- Dilated embedded vertices give the dilated interpolated walk. -/
theorem interpolatedWalk_eq_mul_of_vertexPoint {ε₁ ε₂ : ℝ} {η₁ η₂ : ℝ → ℂ} {a : ℂ}
    (h : ∀ k, vertexPoint ε₁ η₁ k = a * vertexPoint ε₂ η₂ k) (m : ℝ) (w : ℕ → ℤ) (t : ℝ≥0) :
    interpolatedWalk ε₁ η₁ m w t = a * interpolatedWalk ε₂ η₂ m w t := by
  unfold interpolatedWalk
  simp only [h]
  ring

/-- The time factor `r⁻²` of Brownian scaling by `r`. -/
noncomputable def dilationTime (r : ℝ) : ℝ≥0 :=
  (Real.toNNReal r)⁻¹ ^ 2

theorem dilationTime_pos {r : ℝ} (hr : 0 < r) : 0 < dilationTime r :=
  pow_pos (inv_pos.2 (Real.toNNReal_pos.2 hr)) 2

theorem coe_dilationTime {r : ℝ} (hr : 0 < r) : (dilationTime r : ℝ) = (r⁻¹) ^ 2 := by
  simp [dilationTime, Real.coe_toNNReal r hr.le]

/-- The Brownian scaling map `b ↦ r b(r⁻² ·)` on continuous planar paths. -/
noncomputable def dilationPath {r : ℝ} (hr : 0 < r) : ContinuousPath ℂ ≃ₜ ContinuousPath ℂ :=
  Section6.spacetimePathHomeomorph (Homeomorph.smulOfNeZero r hr.ne') (dilationTime r) (dilationTime_pos hr)

theorem dilationPath_apply {r : ℝ} (hr : 0 < r) (b : ContinuousPath ℂ) (t : ℝ≥0) :
    dilationPath hr b t = (r : ℂ) * b (dilationTime r * t) := by
  simp [dilationPath, Section6.spacetimePathHomeomorph_apply, Complex.real_smul]

/-- **Brownian scaling for arbitrary sets of paths.** For `r > 0`, the measure under planar Brownian motion from
`r z` of any set `E` of paths is the measure under planar Brownian motion from `z` of the paths `b` with
`r b(r⁻² ·) ∈ E`. -/
theorem planarBrownianMotion_mul_apply {r : ℝ} (hr : 0 < r) (z : ℂ) (E : Set (ContinuousPath ℂ)) :
    planarBrownianMotion ((r : ℂ) * z) E = planarBrownianMotion z {b | dilationPath hr b ∈ E} := by
  have hscale : (Real.sqrt (dilationTime r : ℝ))⁻¹ = r := by
    rw [coe_dilationTime hr, Real.sqrt_sq (inv_nonneg.2 hr.le), inv_inv]
  have hmap : (planarBrownianMotion z).map (dilationPath hr).toMeasurableEquiv = planarBrownianMotion (r • z) :=
    Section6.planarBrownianMotion_map_spacetime_smul z hr (dilationTime_pos hr) hscale
  rw [← Complex.real_smul, ← hmap]
  exact MeasurableEquiv.map_apply _ _

end MatedCRT.UniformStartDilation
