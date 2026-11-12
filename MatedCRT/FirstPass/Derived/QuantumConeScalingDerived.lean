import MatedCRT.FirstPass.Derived.ConeRadialInvarianceAll
import MatedCRT.FirstPass.Derived.ConeScalingFinal
import MatedCRT.External.QuantumCone

/-!
# Scale invariance of the quantum cone (DMS14 Proposition 4.13(i))

The radial law of a `γ`-quantum cone is invariant under `radialRescale γ b` for every real `b`
(`map_radialRescale_quantumConeRadialLaw`); the radial process of the rescaled field is
`radialRescale γ b` of the radial process of the field almost surely (`radialProcess_rescaled_ae`).
Hence `hrad` of `quantumConeScaling_of_radialInvariance` holds, and the circle average process of the
rescaled cone has the law of the circle average process of the cone.

* `radialInvariance_of_isQuantumCone`: the radial process of the rescaled cone has the radial law of the cone.
* `quantumConeScalingInput_derived`: `QuantumConeScalingInput` as a theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped NNReal ENNReal BoundedContinuousFunction

namespace MatedCRT.FirstPass.Derived

/-- **The radial process of the rescaled cone has the law of the radial process of the cone.** -/
theorem radialInvariance_of_isQuantumCone {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (h : IsQuantumCone γ P hC hcirc) (b : ℝ) :
    P.map (fun ω => radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b)) =
      P.map (fun ω => radialProcess (hcirc ω)) := by
  obtain ⟨ν, hν, hlaw⟩ := h.radial_law
  have hmeasR : Measurable (fun ω => radialProcess (hcirc ω)) := by
    show Measurable fun ω => ((fun t : ℝ≥0 => hcirc ω (Real.exp (-(t : ℝ))) 0),
      (fun s : ℝ≥0 => hcirc ω (Real.exp (s : ℝ)) 0))
    refine Measurable.prodMk ?_ ?_
    · exact Measurable.of_eval (fun t => h.measurable_circle _ 0 (Real.exp_pos _))
    · exact Measurable.of_eval (fun s => h.measurable_circle _ 0 (Real.exp_pos _))
  calc P.map (fun ω => radialProcess (rescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b) b))
      = P.map (fun ω => radialRescale γ b (radialProcess (hcirc ω))) :=
        Measure.map_congr (radialProcess_rescaled_ae hγ0 hγ2 h b)
    _ = (P.map fun ω => radialProcess (hcirc ω)).map (radialRescale γ b) :=
        (Measure.map_map (measurable_radialRescale γ b) hmeasR).symm
    _ = (quantumConeRadialLaw γ ν).map (radialRescale γ b) := by rw [hlaw]
    _ = quantumConeRadialLaw γ ν := map_radialRescale_quantumConeRadialLaw hγ0 hγ2 hν b
    _ = P.map (fun ω => radialProcess (hcirc ω)) := hlaw.symm

/-- **`QuantumConeScalingInput` as a theorem** (DMS14 Proposition 4.13(i)): for every `b > 0` the circle
average process of `h(R_b ·) + Q log R_b - γ⁻¹ log b` has the law of the circle average process of the cone. -/
theorem quantumConeScalingInput_derived : MatedCRT.QuantumConeScalingInput := by
  intro γ hγ0 hγ2 Ω _ P hC hcirc hP h b _
  have := hP
  exact quantumConeScaling_of_radialInvariance hγ0 hγ2 h b
    (radialInvariance_of_isQuantumCone hγ0 hγ2 h b)

end MatedCRT.FirstPass.Derived
