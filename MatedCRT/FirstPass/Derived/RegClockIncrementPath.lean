import MatedCRT.FirstPass.Derived.RegClockOccupationIdentity
import HarmonicBalls.FirstPass.LPBridge.M1
import LatticeProb.Gauss.GFFAffineInvariance
import LatticeProb.LQG.GMCL1Rate

/-!
# The dyadic increment of the regularized clock along a fixed path

Fix a path `b` that stays in `B_r(z) ⊆ B_ρ(0)` before the time `σ(b)`, and a continuous weight `g ≥ 0` that
vanishes on `B_ε(0)` and outside `B_r(z)`. Almost surely in the whole-plane GFF, the regularized clock integrals
`T_δ = ∫_{[0,σ(b)]} g(b_u) dF_δ(u)` at `δ = ε/2` and `δ = ε` are Gaussian multiplicative chaos integrals of the
singular weight `g(x) |x|^{-γ²}` against the occupation measure `ν_b = (du|_{[0,σ(b)]}) ∘ b⁻¹`
(`setLIntegral_regClockMeasure_toReal_eq_integral_occupation`). The `L¹` rate of the dyadic increment of the
chaos of the whole-plane GFF over a general base measure (`IsWholePlaneGFF.integral_abs_integral_increment_le`,
recentred at the unit circle) therefore bounds `E |T_{ε/2} - T_ε|` for this path.
-/

open MeasureTheory Set Filter Topology Metric MarkovProcess HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.KilledOccupation

/-- The singular weight of a continuous `g` vanishing on `B_ε(0)` is continuous. -/
lemma continuous_singularWeight (γ : ℝ) {g : ℂ → ℝ} (hg : Continuous g) {ε : ℝ} (hε : 0 < ε)
    (hgε : ∀ x, g x ≠ 0 → ε ≤ ‖x‖) : Continuous (singularWeight γ g) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x = 0
  · subst hx
    have h0 : singularWeight γ g =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hε] with w hw
      have hgw : g w = 0 := by
        by_contra h
        have := hgε w h
        rw [mem_ball_zero_iff] at hw
        linarith
      simp [singularWeight, hgw]
    exact continuousAt_const.congr h0.symm
  · have hl : ContinuousAt (fun w : ℂ => Real.log ‖w‖) x :=
      (Real.continuousAt_log (norm_ne_zero_iff.2 hx)).comp continuous_norm.continuousAt
    exact hg.continuousAt.mul (continuousAt_const.mul hl).neg.rexp

/-- The occupation measure `ν_b = (du|_{[0,s]}) ∘ b⁻¹` of a path on a finite time interval is finite. -/
lemma isFiniteMeasure_occupation (s : ℝ≥0) (b : ContinuousPath ℂ) :
    IsFiniteMeasure ((lebNN.restrict (Icc 0 s)).map fun u => b u) := by
  have : IsFiniteMeasure (lebNN.restrict (Icc 0 s)) :=
    ⟨by rw [Measure.restrict_apply_univ, lebNN_Icc]; exact ENNReal.coe_lt_top⟩
  infer_instance

/-- A continuous function is integrable against the occupation measure `ν_b = (du|_{[0,s]}) ∘ b⁻¹` of a path
on a finite time interval. -/
lemma integrable_occupation_of_continuous {f : ℂ → ℝ} (hf : Continuous f) (s : ℝ≥0) (b : ContinuousPath ℂ) :
    Integrable f ((lebNN.restrict (Icc 0 s)).map fun u => b u) := by
  have hbm : Measurable fun u : ℝ≥0 => b u := (map_continuous b).measurable
  rw [integrable_map_measure hf.aestronglyMeasurable hbm.aemeasurable]
  have hfb : Continuous (f ∘ fun u : ℝ≥0 => b u) := hf.comp (map_continuous b)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := s)).exists_bound_of_continuousOn hfb.continuousOn
  exact Measure.integrableOn_of_bounded (by rw [lebNN_Icc]; exact ENNReal.coe_ne_top)
    hfb.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hC))

/-- **`L¹` bound for the dyadic increment of the regularized clock along a fixed path.** Let `h^ℂ` be a whole-plane
GFF, `B_r(z) ⊆ B_ρ(0)`, `0 < ε < 1 - ρ`, `g ≥ 0` continuous, vanishing on `B_ε(0)` and outside `B_r(z)`, and let
the path `b` stay in `B_r(z)` before `σ(b)`. Then for `γ ≤ α ≤ 2γ` and `t > 0`,
`E |T_{ε/2} - T_ε| ≤ ε^{γ²/2} ((B I / t + t) / 2 + 2 (∫ |g̃| dν_b) e^{log(1/ε) (γ²/2 - (α - γ)²/2)})`, where
`T_δ = ∫_{[0,σ(b)]} g(b_u) dF_δ(u)`, `g̃ = singularWeight γ g`, `B = (2^{γ²} - 1) e^{log(1/ε) (2γ² - (2γ - α)²/2)}`
and `I = ∫_{|x - x'| < 2ε} |g̃(x)| |g̃(x')| d(ν_b ⊗ ν_b)`. -/
theorem integral_abs_regClock_dyadic_increment_le {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hc : Ω' → ℝ → ℂ → ℝ} (hwp : HarmonicBalls.IsWholePlaneGFF P' hC' hc)
    (γ : ℝ) {ρ r ε : ℝ} {z : ℂ} (hball : ball z r ⊆ ball 0 ρ) (hε : 0 < ε) (hερ : ε < 1 - ρ)
    {g : ℂ → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hgε : ∀ x, g x ≠ 0 → ε ≤ ‖x‖)
    (hgr : ∀ x, g x ≠ 0 → x ∈ ball z r)
    (σ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) (hb : ∀ s : ℝ≥0, s < σ b → b s ∈ ball z r)
    {α t : ℝ} (hγα : γ ≤ α) (hα : α ≤ 2 * γ) (ht : 0 < t) :
    ∫ ω', |(∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (g (b u))
          ∂regClockMeasure γ (ε / 2) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') σ b).toReal -
        (∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (g (b u))
          ∂regClockMeasure γ ε (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω') σ b).toReal| ∂P' ≤
      ε ^ (γ ^ 2 / 2) * (((Real.exp (γ ^ 2 * Real.log 2) - 1) *
          Real.exp (Real.log (1 / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
          (∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator
            (fun p => |singularWeight γ g p.1| * |singularWeight γ g p.2|) p
            ∂(((lebNN.restrict (Icc 0 (σ b))).map fun u => b u).prod
              ((lebNN.restrict (Icc 0 (σ b))).map fun u => b u))) / t + t) / 2 +
        2 * (∫ x, |singularWeight γ g x| ∂((lebNN.restrict (Icc 0 (σ b))).map fun u => b u)) *
          Real.exp (Real.log (1 / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2))) := by
  set ν : Measure ℂ := (lebNN.restrict (Icc 0 (σ b))).map fun u => b u with hν
  have hνf : IsFiniteMeasure ν := isFiniteMeasure_occupation (σ b) b
  have hh := (LPBridge.isWholePlaneGFF_iff P' hC' hc).1 hwp
  have hswc := continuous_singularWeight γ hg hε hgε
  have hgR : ∀ x, singularWeight γ g x ≠ 0 → ‖x‖ + ε ≤ 1 := fun x hx => by
    have hgx : g x ≠ 0 := fun h => hx (by simp [singularWeight, h])
    have := mem_ball_zero_iff.1 (hball (hgr x hgx))
    linarith
  have hLP := hh.integral_abs_integral_increment_le hε one_pos ν hswc.measurable
    (integrable_occupation_of_continuous hswc (σ b) b) hgR hγα hα ht
  refine (integral_congr_ae ?_).trans_le hLP
  filter_upwards [hwp.ae_continuousOn_circle, hh.ae_circleAverage_one_zero] with ω hcont h10
  have hε2 : 0 < ε / 2 := half_pos hε
  have hgε2 : ∀ x, g x ≠ 0 → ε / 2 ≤ ‖x‖ := fun x hx => by linarith [hgε x hx]
  have hint : ∀ δ, 0 < δ → Integrable (fun x => singularWeight γ g x *
      (δ ^ (γ ^ 2 / 2) * Real.exp (γ * (hc ω δ x - hc ω 1 0)))) ν := fun δ hδ => by
    have hxc : Continuous fun x : ℂ => hc ω δ x :=
      hcont.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hδ, mem_univ x⟩)
    exact integrable_occupation_of_continuous
      (hswc.mul (continuous_const.mul (continuous_const.mul (hxc.sub continuous_const)).rexp)) (σ b) b
  have e1 : (∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (g (b u))
      ∂regClockMeasure γ (ε / 2) (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω) σ b).toReal = _ :=
    setLIntegral_regClockMeasure_toReal_eq_integral_occupation γ hcont h10 hball hε2
      (by linarith) hg.measurable hg0 hgε2 σ b hb
  have e2 : (∫⁻ u in Icc 0 (σ b), ENNReal.ofReal (g (b u))
      ∂regClockMeasure γ ε (clockPsi (fun ω' => fieldCircleAverage γ (hc ω')) ω) σ b).toReal = _ :=
    setLIntegral_regClockMeasure_toReal_eq_integral_occupation γ hcont h10 hball hε hερ
      hg.measurable hg0 hgε σ b hb
  rw [e1, e2, ← integral_sub (hint _ hε2) (hint _ hε)]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

end MatedCRT.KilledOccupation
