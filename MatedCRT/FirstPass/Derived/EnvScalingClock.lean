import MatedCRT.Proofs.Sec1.EnvironmentScaling.AllStartsClock
import MatedCRT.FirstPass.LPBridge.UniversalMeasurability
import MatedCRT.FirstPass.S5i
import MatedCRT.FirstPass.Frozen.S1d

/-!
# The LQG clock of the rescaled quantum cone, for every starting point

For a valid environment `S` with cone parameter `γ ∈ (0, 2)` and `b > 0`, the rescaled circle average process
`h^b_r(z) = h_{R_b r}(R_b z) + Q log R_b - γ⁻¹ log b` (eq:quantum-cone-scaling) admits, almost surely, one clock which
is the LQG clock of planar Brownian motion for `h^b` from every starting point and a time change clock
(`RescaledConeClockStep`, Proofs/Sec1/EnvironmentScaling.lean). The clock cannot be transported pathwise from the clock
of `h`: the approximations `lqgClockApprox` are read along the dyadic scales `2^{-k}` only, and Brownian scaling turns
them into the scales `R_b 2^{-k}`. The route is through the law: the set of continuous circle processes admitting an
all-starts clock is analytic in the Polish space `C((0, ∞) × ℂ, ℝ)` (compact-open topology), hence universally
measurable; `h` lies in it almost surely and `h^b` has the law of `h` (Duplantier-Miller-Sheffield, Proposition
4.13(i)), so `h^b` lies in it almost surely (`MatedCRT.AllStarts.rescaledConeClockStep_of_inputs`).

Proved here, with no hypothesis beyond the quantum cone scaling input:
* `polishSpace_circleFns`: `C((0, ∞) × ℂ, ℝ)` is Polish (Mathlib: complete for a compactly coherent domain, metrizable
  and second countable for a locally compact, σ-compact, second countable domain);
* `rescaledConeClockStep_of_scaling`: `RescaledConeClockStep 𝒮` for every model `𝒮`, the universal measurability of
  analytic sets being supplied by `frozenUniversalMeasurabilityOfAnalytic_holds` (Lusin; Kechris, *Classical
  Descriptive Set Theory*, Theorem 21.10);
* `coneEnvironmentScalingUnderSLE_of_field_mating`: the environment scaling under the space-filling SLE closure
  properties from the quantum cone scaling input, Fact 2.2, and the two remaining representation steps (field and
  mating of trees).
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory

/-- The positive half-line is locally compact (an open subset of `ℝ`). -/
theorem locallyCompactSpace_Ioi_zero : LocallyCompactSpace (Set.Ioi (0 : ℝ)) :=
  isOpen_Ioi.locallyCompactSpace

/-- The space `C((0, ∞) × ℂ, ℝ)` of continuous circle processes, with the compact-open topology, is Polish. -/
theorem polishSpace_circleFns : PolishSpace MatedCRT.AllStarts.CircleFns := by
  have := locallyCompactSpace_Ioi_zero
  infer_instance

/-- **All-starts LQG clock of the rescaled quantum cone** (`RescaledConeClockStep`), for every model, from the quantum
cone scaling input (DMS14 Proposition 4.13(i)). -/
theorem rescaledConeClockStep_of_scaling (hscale : QuantumConeScalingInput) (𝒮 : SpaceFillingSLEModel) :
    RescaledConeClockStep 𝒮 := by
  have := polishSpace_circleFns
  exact MatedCRT.AllStarts.rescaledConeClockStep_of_inputs
    (prestonAnalyticUniversallyMeasurable_of_frozen frozenUniversalMeasurabilityOfAnalytic_holds) hscale 𝒮

/-- **Environment scaling under the space-filling SLE closure properties** (`ConeEnvironmentScalingUnderSLE`,
eq:scale-invariance-of-field-and-eta) from the quantum cone scaling input, Fact 2.2, and the field and mating-of-trees
representation steps; the clock step is `rescaledConeClockStep_of_scaling`. -/
theorem coneEnvironmentScalingUnderSLE_of_field_mating (𝒮 : SpaceFillingSLEModel)
    (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt) (hfield : RescaledConeFieldStep 𝒮)
    (hmating : RescaledMatingOfTreesStep 𝒮) : ConeEnvironmentScalingUnderSLE 𝒮 :=
  fun hSc hRe hMo => coneEnvironmentScalingStep_of_inputs 𝒮 hscale h22 hSc hRe hMo hfield
    (rescaledConeClockStep_of_scaling hscale 𝒮) hmating

end MatedCRT.FirstPass.Derived
