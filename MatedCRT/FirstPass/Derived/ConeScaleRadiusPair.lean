import MatedCRT.FirstPass.Derived.ConeDataLift
import MatedCRT.FirstPass.Derived.ReferenceConeRadialCircleDerived
import MatedCRT.FirstPass.Derived.ConeRadialLevelLimits
import MatedCRT.Proofs.Sec1.EnvironmentScaling.Field

/-!
# The cone scale radius is read off the Brownian pair of the mating-of-trees coupling

For the environment `S` of the paper and a mating-of-trees coupling `V` tied to it (the pairings
of `h` with test functions are those of the quantum cone field `coneField X (A)` of `V`, with radial
process `A = coneRadial γ γ B B'`), the circle averages of `h` around the origin are almost surely
the radial process of the coupling at every radius:
`h_{e^{-t}}(0) = A_t` for all `t ∈ ℝ` (`MatedCRTEnv.IsValid.ae_hcirc_exp_eq_coneRadial`).
Consequently the cone scale radius `R_b = sup {r > 0 : h_r(0) + Q log r = γ⁻¹ log b}`
(eq:cone-scale-radius) is almost surely `exp` of the last level time of the radial process,
i.e. the scale `coneScaleOfPair γ b (B, B')` used to rescale the coupling
(`MatedCRTEnv.IsValid.ae_coneScaleRadius_eq_coneScaleOfPair`).

* `coneScaleRadius_eq_exp_lastLevel`: the deterministic identification, given that `R_b` is a
  positive point of the level set beyond which `h_r(0) + Q log r` stays above the level.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace MatedCRT

/-- **Deterministic identification of the cone scale radius.** If `h_{e^{-t}}(0) = w(t)` for all
`t`, and `R_b > 0` is a point of the level set `{r > 0 : h_r(0) + Q log r = γ⁻¹ log b}` with
`h_r(0) + Q log r > γ⁻¹ log b` for every `r > R_b`, then `R_b = exp L`, where
`L = sup {s : w(-s) + Q s = γ⁻¹ log b}` is the last level time of `w`. -/
theorem coneScaleRadius_eq_exp_lastLevel {γ b : ℝ} {hc : ℝ → ℂ → ℝ} {w : C(ℝ, ℝ)}
    (hw : ∀ t : ℝ, hc (Real.exp (-t)) 0 = w t) (hpos : 0 < coneScaleRadius γ hc b)
    (hmem : hc (coneScaleRadius γ hc b) 0 + _root_.HarmonicBalls.lqgQ γ * Real.log (coneScaleRadius γ hc b) =
      γ⁻¹ * Real.log b)
    (hgt : ∀ r : ℝ, coneScaleRadius γ hc b < r → γ⁻¹ * Real.log b < hc r 0 + _root_.HarmonicBalls.lqgQ γ * Real.log r) :
    coneScaleRadius γ hc b = Real.exp (MatedCRTHarmonic.ConeScaling.lastLevel
      (MatedCRTHarmonic.MatedCRT.lqgQ γ) (γ⁻¹ * Real.log b) w) := by
  have hQ : _root_.HarmonicBalls.lqgQ γ = MatedCRTHarmonic.MatedCRT.lqgQ γ := rfl
  have hw' : ∀ s : ℝ, w (-s) = hc (Real.exp s) 0 := fun s => by rw [← hw, neg_neg]
  have hG : IsGreatest {s : ℝ | w (-s) + MatedCRTHarmonic.MatedCRT.lqgQ γ * s = γ⁻¹ * Real.log b}
      (Real.log (coneScaleRadius γ hc b)) := by
    refine ⟨?_, fun s hs => ?_⟩
    · show w (-Real.log (coneScaleRadius γ hc b)) +
          MatedCRTHarmonic.MatedCRT.lqgQ γ * Real.log (coneScaleRadius γ hc b) = γ⁻¹ * Real.log b
      rw [hw', Real.exp_log hpos, ← hQ]
      exact hmem
    · have hs' : w (-s) + MatedCRTHarmonic.MatedCRT.lqgQ γ * s = γ⁻¹ * Real.log b := hs
      by_contra hlt
      have hlt' : Real.log (coneScaleRadius γ hc b) < s := lt_of_not_ge hlt
      have hr : coneScaleRadius γ hc b < Real.exp s := by
        rw [← Real.exp_log hpos]
        exact Real.exp_lt_exp.2 hlt'
      have h1 := hgt _ hr
      rw [Real.log_exp, ← hw', hQ] at h1
      linarith
  rw [MatedCRTHarmonic.ConeScaling.lastLevel, hG.csSup_eq, Real.exp_log hpos]

/-- **The circle averages of `h` around the origin are the radial process of the coupling.** For a
mating-of-trees coupling `V` whose quantum cone field has almost surely the pairings of `h`, almost
surely `h_{e^{-t}}(0) = A_t` for every `t ∈ ℝ`, where `A = coneRadial γ γ B B'`. -/
theorem MatedCRTEnv.IsValid.ae_hcirc_exp_eq_coneRadial {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    (hγ2 : γ < 2) {V : Ω → MatedCRTHarmonic.MatedCRT.CouplingData}
    (hC : MatedCRTHarmonic.MatedCRT.IsCouplingData γ S.P V)
    (htie : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (V ω).X
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V ω).B (V ω).B') φ) :
    ∀ᵐ ω ∂S.P, ∀ t : ℝ, S.hcirc ω (Real.exp (-t)) 0 =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V ω).B (V ω).B' t := by
  have := hS.isProbabilityMeasure
  have hCP := (show MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _
    from hC)
  have hfix : ∀ t : ℝ, ∀ᵐ ω ∂S.P, S.hcirc ω (Real.exp (-t)) 0 =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V ω).B (V ω).B' t := by
    intro t
    have h1 := Sec1.ae_distribution_circleAvg_eq hS
      (H := fun ω => MatedCRTHarmonic.MatedCRT.coneField (V ω).X
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V ω).B (V ω).B')) htie (Real.exp_pos (-t))
      (z := 0) (by rw [norm_zero]; exact (Real.exp_pos _).ne)
    have h2 := Sec1.ae_circleAvg_matedCRT_coneField_exp γ hCP.gff hCP.bm_B hCP.bm_B'
      hCP.indep_cone.2 t
    filter_upwards [h1, h2] with ω h1 h2
    exact h1.symm.trans h2
  have hQ : ∀ᵐ ω ∂S.P, ∀ q : ℚ, S.hcirc ω (Real.exp (-(q : ℝ))) 0 =
      MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V ω).B (V ω).B' q :=
    ae_all_iff.2 fun q => hfix q
  filter_upwards [hQ, hS.isQuantumCone.ae_continuousOn_circle,
    MatedCRTHarmonic.MatedCRT.IsCouplingData.ae_radGood hC hγ hγ2] with ω hq hcont hgood
  have hc1 : Continuous fun t : ℝ => S.hcirc ω (Real.exp (-t)) 0 := by
    have hf : Continuous fun t : ℝ => ((Real.exp (-t), (0 : ℂ)) : ℝ × ℂ) := by fun_prop
    exact hcont.comp_continuous hf fun t => ⟨Real.exp_pos _, Set.mem_univ _⟩
  have hc2 : Continuous (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V ω).B (V ω).B') :=
    MatedCRTHarmonic.ConeScaling.continuous_coneRadial_of_mem hgood
  have heq := Continuous.ext_on Rat.denseRange_cast hc1 hc2 (by
    rintro _ ⟨q, rfl⟩
    exact hq q)
  exact fun t => congrFun heq t

/-- **The cone scale radius is the scale of the Brownian pair.** For a mating-of-trees coupling `V`
whose quantum cone field has almost surely the pairings of `h`, almost surely
`R_b = coneScaleOfPair γ b (B, B')`, the exponential of the last level time of the radial process
`A = coneRadial γ γ B B'` at level `γ⁻¹ log b`. -/
theorem MatedCRTEnv.IsValid.ae_coneScaleRadius_eq_coneScaleOfPair {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ)
    (hγ2 : γ < 2) {V : Ω → MatedCRTHarmonic.MatedCRT.CouplingData}
    (hC : MatedCRTHarmonic.MatedCRT.IsCouplingData γ S.P V)
    (htie : ∀ᵐ ω ∂S.P, ∀ φ : LQGMetric.TestC,
      S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (V ω).X
        (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (V ω).B (V ω).B') φ) (b : ℝ) :
    ∀ᵐ ω ∂S.P, coneScaleRadius γ (S.hcirc ω) b = coneScaleOfPair γ b ((V ω).B, (V ω).B') := by
  have := hS.isProbabilityMeasure
  filter_upwards [hS.ae_hcirc_exp_eq_coneRadial hγ hγ2 hC htie,
    FirstPass.Derived.ae_coneScaleRadius_spec hγ hγ2 hS.isQuantumCone b,
    MatedCRTHarmonic.MatedCRT.IsCouplingData.ae_radGood hC hγ hγ2] with ω hrad hspec hgood
  refine coneScaleRadius_eq_exp_lastLevel
    (w := MatedCRTHarmonic.ConeScaling.radMap γ γ ((V ω).B, (V ω).B')) (fun t => ?_)
    hspec.1 hspec.2.1 hspec.2.2
  simp only [MatedCRTHarmonic.ConeScaling.radMap_apply, hgood, ↓reduceIte]
  exact hrad t

end MatedCRT
