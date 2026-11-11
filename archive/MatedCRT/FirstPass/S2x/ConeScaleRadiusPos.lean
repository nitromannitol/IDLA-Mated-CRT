import MatedCRT.Defs.QuantumCone

/-!
# Positivity of the cone scale radius (Step `ConeScaleRadiusPosStep`, PRO Section 2, eq:cone-scale-radius l.451)

`coneScaleRadius γ c b = sSup {r > 0 : c r 0 + Q log r = γ⁻¹ log b}`. The deterministic core: if `r ↦ c r 0 + Q log r`
is continuous on `(0, ∞)`, tends to `-∞` as `r → 0+` and to `+∞` as `r → ∞`, the level set is nonempty (intermediate
value theorem) and bounded above, so its supremum is positive. The two limits are the almost sure divergences of the
radial process of the quantum cone (Definition 2.1); they are the named input `hlim` below, not proved here.
-/

open MeasureTheory Filter Topology Set
open _root_.HarmonicBalls

namespace MatedCRT.FirstPass2x

/-- Deterministic core of the positivity of a level-set supremum: a function `f` continuous on `(0, ∞)` with
`f → -∞` at `0+` and `f → +∞` at `∞` has nonempty, bounded above level set `{r > 0 : f r = c}`, hence
`sSup {r > 0 : f r = c} > 0`. -/
theorem sSup_level_pos_of_limits {f : ℝ → ℝ} (c : ℝ) (hf : ContinuousOn f (Ioi 0))
    (h0 : Tendsto f (𝓝[>] 0) atBot) (hinf : Tendsto f atTop atTop) :
    0 < sSup {r : ℝ | 0 < r ∧ f r = c} := by
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), f r < c := h0.eventually (Iio_mem_atBot c)
  obtain ⟨a, hac, ha0⟩ := (hev.and eventually_mem_nhdsWithin).exists
  have hac' : f a < c := hac
  have ha0' : 0 < a := ha0
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hinf.eventually (Ioi_mem_atTop c))
  have hab : a < max M (a + 1) := lt_of_lt_of_le (lt_add_one a) (le_max_right _ _)
  have hfb : c < f (max M (a + 1)) := hM _ (le_max_left _ _)
  have hIcc : ContinuousOn f (Icc a (max M (a + 1))) :=
    hf.mono (fun x hx => lt_of_lt_of_le ha0' hx.1)
  obtain ⟨x, hx, hxc⟩ := intermediate_value_Icc hab.le hIcc ⟨hac'.le, hfb.le⟩
  have hxpos : 0 < x := lt_of_lt_of_le ha0' hx.1
  have hbdd : BddAbove {r : ℝ | 0 < r ∧ f r = c} := by
    refine ⟨M, fun r hr => ?_⟩
    by_contra hlt
    have hlt' : M < r := not_le.1 hlt
    have hcr : c < f r := hM r hlt'.le
    exact hcr.ne' hr.2
  exact lt_of_lt_of_le hxpos (le_csSup hbdd ⟨hxpos, hxc⟩)

/-- The cone scale radius is positive when the radial part `r ↦ c r 0 + Q log r` diverges at both ends (deterministic
form of `ConeScaleRadiusPosStep`, for one circle average process `c` continuous on `(0, ∞) × ℂ`). -/
theorem coneScaleRadius_pos_of_limits (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (b : ℝ)
    (hcont : ContinuousOn (fun r : ℝ => hcirc r 0 + lqgQ γ * Real.log r) (Ioi 0))
    (h0 : Tendsto (fun r : ℝ => hcirc r 0 + lqgQ γ * Real.log r) (𝓝[>] 0) atBot)
    (hinf : Tendsto (fun r : ℝ => hcirc r 0 + lqgQ γ * Real.log r) atTop atTop) :
    0 < coneScaleRadius γ hcirc b := by
  unfold coneScaleRadius
  exact sSup_level_pos_of_limits (γ⁻¹ * Real.log b) hcont h0 hinf

/-- **`ConeScaleRadiusPosStep` reduced to the radial divergence.** Given the almost sure two-sided divergence `hlim` of
the radial part `r ↦ h_r(0) + Q log r` of a quantum cone (its limits at `0+` and at `∞`), a.s. `0 < R_b` for every
`b`. Continuity on `(0, ∞)` comes from the a.s. continuity of the circle average process (`IsQuantumCone`). -/
theorem ae_coneScaleRadius_pos_of_limits {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hcone : IsQuantumCone γ P hC hcirc) (b : ℝ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun r : ℝ => hcirc ω r 0 + lqgQ γ * Real.log r) (𝓝[>] 0) atBot ∧
      Tendsto (fun r : ℝ => hcirc ω r 0 + lqgQ γ * Real.log r) atTop atTop) :
    ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b := by
  filter_upwards [hcone.ae_continuousOn_circle, hlim] with ω hω hl
  refine coneScaleRadius_pos_of_limits γ (hcirc ω) b ?_ hl.1 hl.2
  have hr0 : ContinuousOn (fun r : ℝ => hcirc ω r 0) (Ioi 0) :=
    hω.comp (continuousOn_id.prodMk continuousOn_const) (fun r hr => ⟨hr, mem_univ _⟩)
  have hlog : ContinuousOn (fun r : ℝ => lqgQ γ * Real.log r) (Ioi 0) :=
    continuousOn_const.mul (Real.continuousOn_log.mono (fun x (hx : x ∈ Ioi (0 : ℝ)) => hx.ne'))
  exact hr0.add hlog

end MatedCRT.FirstPass2x
