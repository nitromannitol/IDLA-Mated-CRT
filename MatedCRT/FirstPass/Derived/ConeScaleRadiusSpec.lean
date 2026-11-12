import MatedCRT.Defs.QuantumCone

/-!
# The cone scale radius is a last visit

The cone scale radius `R_b = sup {r > 0 : h_r(0) + Q log r = γ⁻¹ log b}` of `MatedCRT.Defs.QuantumCone`
(eq:cone-scale-radius).  This file records the deterministic part of its well-definedness.  Write
`f s = h_{e^s}(0) + Q s`.  If `f` is continuous, tends to `+∞` at `+∞` and to `-∞` at `-∞` (which holds
almost surely for the quantum cone: `f (-t)` is a Brownian motion with negative drift and `f s` for `s ≥ 0` is
Brownian motion with positive drift conditioned to stay positive), then the level set `{f = c}` is nonempty and
bounded above, the supremum `R_b` is attained, and `f > c` strictly beyond the last visit.
-/

open Filter Topology Set

namespace MatedCRT.FirstPass.Derived

open HarmonicBalls

/-- Deterministic well-definedness of the cone scale radius: for a continuous radial level function
`f s = h_{e^s}(0) + Q s` tending to `±∞` at `±∞`, `R_b > 0` is a point of the level set `{r > 0 : f (log r) = c}`
(`c = γ⁻¹ log b`), and `f (log r) > c` for every `r > R_b`. -/
theorem coneScaleRadius_spec {γ : ℝ} {hcirc : ℝ → ℂ → ℝ} {b : ℝ}
    (hcont : Continuous fun s : ℝ => hcirc (Real.exp s) 0)
    (hup : Tendsto (fun s : ℝ => hcirc (Real.exp s) 0 + lqgQ γ * s) atTop atTop)
    (hdown : Tendsto (fun s : ℝ => hcirc (Real.exp s) 0 + lqgQ γ * s) atBot atBot) :
    0 < coneScaleRadius γ hcirc b ∧
      hcirc (coneScaleRadius γ hcirc b) 0 + lqgQ γ * Real.log (coneScaleRadius γ hcirc b)
        = γ⁻¹ * Real.log b ∧
      ∀ r : ℝ, coneScaleRadius γ hcirc b < r →
        γ⁻¹ * Real.log b < hcirc r 0 + lqgQ γ * Real.log r := by
  set Q := lqgQ γ with hQ
  set c := γ⁻¹ * Real.log b with hc
  set f : ℝ → ℝ := fun s => hcirc (Real.exp s) 0 + Q * s with hf
  have hfc : Continuous f := hcont.add (continuous_const.mul continuous_id)
  set S : Set ℝ := f ⁻¹' {c} with hS
  have hSclosed : IsClosed S := isClosed_singleton.preimage hfc
  -- nonempty by the intermediate value theorem
  obtain ⟨s₁, hs₁⟩ := (hup.eventually (eventually_gt_atTop c)).exists_forall_of_atTop
  obtain ⟨s₀, hs₀⟩ := (hdown.eventually (eventually_lt_atBot c)).exists_forall_of_atBot
  have hne : S.Nonempty := by
    have hle : min s₀ s₁ ≤ max s₀ s₁ := (min_le_left _ _).trans (le_max_left _ _)
    have hsub := intermediate_value_Icc hle hfc.continuousOn
    have hlow : f (min s₀ s₁) < c := hs₀ _ (min_le_left _ _)
    have hhigh : c < f (max s₀ s₁) := hs₁ _ (le_max_right _ _)
    obtain ⟨s, -, hs⟩ := hsub ⟨hlow.le, hhigh.le⟩
    exact ⟨s, hs⟩
  have hbdd : BddAbove S := by
    refine ⟨s₁, fun s hs => ?_⟩
    by_contra hlt
    have hlt := not_le.mp hlt
    have := hs₁ s hlt.le
    simp only [hS, mem_preimage, mem_singleton_iff] at hs
    linarith
  set sL : ℝ := sSup S with hsL
  have hsLmem : sL ∈ S := hSclosed.csSup_mem hne hbdd
  have hfsL : f sL = c := hsLmem
  -- the set in the definition is the image of `S` under `exp`
  have himg : {r : ℝ | 0 < r ∧ hcirc r 0 + Q * Real.log r = c} = Real.exp '' S := by
    ext r
    constructor
    · rintro ⟨hr, hrc⟩
      refine ⟨Real.log r, ?_, Real.exp_log hr⟩
      simp only [hS, hf, mem_preimage, mem_singleton_iff, Real.exp_log hr]
      exact hrc
    · rintro ⟨s, hs, rfl⟩
      refine ⟨Real.exp_pos s, ?_⟩
      simp only [hS, hf, mem_preimage, mem_singleton_iff] at hs
      simpa [Real.log_exp] using hs
  have hR : coneScaleRadius γ hcirc b = Real.exp sL := by
    unfold coneScaleRadius
    rw [himg]
    exact ((Real.exp_monotone.map_csSup_of_continuousAt Real.continuous_exp.continuousAt hne hbdd)).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hR]; exact Real.exp_pos _
  · rw [hR, Real.log_exp]
    simpa [hf] using hfsL
  · intro r hr
    rw [hR] at hr
    have hrpos : 0 < r := (Real.exp_pos _).trans hr
    have hs : sL < Real.log r := by
      rw [← Real.exp_lt_exp, Real.exp_log hrpos]; exact hr
    have key : c < f (Real.log r) := by
      by_contra hle
      have hle := not_lt.mp hle
      have hle2 : Real.log r ≤ max (Real.log r) s₁ := le_max_left _ _
      have hhigh : c < f (max (Real.log r) s₁) := hs₁ _ (le_max_right _ _)
      obtain ⟨s, hsI, hsc⟩ := intermediate_value_Icc hle2 hfc.continuousOn ⟨hle, hhigh.le⟩
      have hsS : s ∈ S := hsc
      have : s ≤ sL := le_csSup hbdd hsS
      linarith [hsI.1]
    simpa [hf, Real.exp_log hrpos] using key
end MatedCRT.FirstPass.Derived
