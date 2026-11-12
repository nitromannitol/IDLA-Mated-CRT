import MatedCRT.Proofs.Measurability.FieldCircle
import MatedCRT.Proofs.Measurability.LQGMeasureField
import MatedCRT.Proofs.Measurability.VagueMeasurable
import MatedCRT.Proofs.Infra.Setting

/-!
# The area measure of the quantum cone is a Borel function of the field

Code a field `h` by its pairings with all compactly supported smooth test functions,
`F(φ) = (h, φ)`, a point of the product space `FieldPairingCode = {φ // IsTestFunction univ φ} → ℝ`.
There is one Borel map `M : FieldPairingCode → Measure ℂ`, depending only on `γ`, such that for every
`γ`-quantum cone `h` with `γ`-LQG measure `μ_h`, almost surely `M((h, ·)) = μ_h`.

Construction. The circle average `h_{2^{-n}}(z)` is the limit of the pairings of `h` with the circular
bump functions `circBump k z 2^{-n}` at dyadic grid points (`ae_tendsto_circBump_of_isQuantumCone`), and the
continuity of `(r, z) ↦ h_r(z)` recovers it at every `z` from the grid (`FieldCircle.gridVersion_eq`). This gives a
jointly Borel function `fieldCodeDyadicCircle n : FieldPairingCode → ℂ → ℝ`, hence Borel approximating measures
`2^{-nγ²/2} e^{γ h_{2^{-n}}(z)} dz` of the code. Their vague limit, where it exists, is a Borel function of the code
(`VagueWholePlane.exists_measurable_vagueLimit`), and for the quantum cone it is `μ_h` by the definition of the
`γ`-LQG measure as the dyadic vague limit.

## Main results

* `MatedCRT.exists_measurable_fieldCode_lqgMeasure_of_isQuantumCone`: the Borel decoder for every quantum cone.
* `MatedCRT.exists_measurable_fieldCode_lqgMeasure`: the same decoder recovers the area measure of every valid
  environment.
-/

open MeasureTheory Filter Set
open HarmonicBalls
open scoped ENNReal Topology

namespace MatedCRT

/-- A distribution on `ℂ` is coded by its pairings with compactly supported smooth test functions. -/
abbrev FieldPairingCode := {φ : ℂ → ℝ // IsTestFunction univ φ} → ℝ

/-- The field code `φ ↦ (h, φ)` of an environment. -/
def fieldPairingCode {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) : FieldPairingCode :=
  fun φ => S.hC ω φ.1

/-- The field code of a quantum cone is a measurable random element of the code space. -/
theorem measurable_fieldPairingCode_of_isQuantumCone {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {γ : ℝ} (hcone : IsQuantumCone γ S.P S.hC S.hcirc) : Measurable (fieldPairingCode S) :=
  measurable_pi_iff.2 fun φ => hcone.measurable_pairing φ.1 φ.2

/-- The field code of a valid environment is measurable. -/
theorem MatedCRTEnv.IsValid.measurable_fieldPairingCode {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) : Measurable (fieldPairingCode S) :=
  measurable_fieldPairingCode_of_isQuantumCone hS.isQuantumCone

/-- The dyadic circle average `h_{2^{-n}}(z)` computed from a field code: the limit superior of the pairings
with the circular bump functions at the dyadic grid points, extended to all `z` by the grid limit. -/
noncomputable def fieldCodeDyadicCircle (n : ℕ) : FieldPairingCode → ℂ → ℝ :=
  FieldCircle.gridVersion fun w F =>
    limsup (fun k => F ⟨LQGMetric.CircleAvg.circBump k w ((2 : ℝ)⁻¹ ^ n),
      CirclePairing.isTestFunction_circBump k w ((2 : ℝ)⁻¹ ^ n)⟩) atTop

theorem measurable_fieldCodeDyadicCircle (n : ℕ) :
    Measurable (Function.uncurry (fieldCodeDyadicCircle n)) := by
  apply FieldCircle.measurable_gridVersion
  intro w
  exact Measurable.limsup fun k => measurable_pi_apply _

theorem fieldCodeDyadicCircle_fieldPairingCode {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (n : ℕ)
    (ω : Ω) : fieldCodeDyadicCircle n (fieldPairingCode S ω) = FieldCircle.dyadicCircleVersion S n ω :=
  rfl

/-- The dyadic circle averages of a quantum cone are recovered, almost surely at all scales `2^{-n}` and all
points at once, from its test pairings. -/
theorem ae_fieldCodeDyadicCircle_eq_of_isQuantumCone {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {γ : ℝ} (hcone : IsQuantumCone γ S.P S.hC S.hcirc) :
    ∀ᵐ ω ∂S.P, ∀ n : ℕ, ∀ z : ℂ,
      fieldCodeDyadicCircle n (fieldPairingCode S ω) z = S.hcirc ω ((2 : ℝ)⁻¹ ^ n) z := by
  have hgrid : ∀ᵐ ω ∂S.P, ∀ n m : ℕ, ∀ a b : ℤ,
      FieldCircle.circleField S ((2 : ℝ)⁻¹ ^ n) (FieldCircle.gridPt m a b) ω =
        S.hcirc ω ((2 : ℝ)⁻¹ ^ n) (FieldCircle.gridPt m a b) := by
    simp only [ae_all_iff]
    intro n m a b
    exact (CirclePairing.ae_tendsto_circBump_of_isQuantumCone hcone (by positivity)
      (FieldCircle.norm_gridPt_ne m n a b)).mono fun _ h => h.limsup_eq
  filter_upwards [hgrid, hcone.ae_continuousOn_circle] with ω hgridω hcont n z
  have hc : Continuous fun w => S.hcirc ω ((2 : ℝ)⁻¹ ^ n) w := by
    rw [← continuousOn_univ]
    exact hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      fun w _ => ⟨mem_Ioi.2 (by positivity), mem_univ w⟩
  rw [fieldCodeDyadicCircle_fieldPairingCode]
  exact FieldCircle.gridVersion_eq hc (fun m a b => hgridω n m a b) z

/-- **The LQG measure of a quantum cone is a Borel function of its test pairings.** There is a Borel map `M` from
field codes to measures on `ℂ`, depending only on `γ`, such that for every `γ`-quantum cone `h` with `γ`-LQG
measure `μ_h`, almost surely `M((h, ·)) = μ_h`. -/
theorem exists_measurable_fieldCode_lqgMeasure_of_isQuantumCone (γ : ℝ) :
    ∃ M : FieldPairingCode → Measure ℂ, Measurable M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {μ : Ω → Measure ℂ},
        IsQuantumCone γ S.P S.hC S.hcirc → IsLQGMeasure S.P γ S.hcirc μ →
        ∀ᵐ ω ∂S.P, M (fieldPairingCode S ω) = μ ω := by
  let density : ℕ → FieldPairingCode → ℂ → ℝ := fun n F z =>
    dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCodeDyadicCircle n F z)
  have hdensity (n : ℕ) : Measurable (Function.uncurry (density n)) :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_fieldCodeDyadicCircle n)))
  have hdensity_nonneg (n : ℕ) (F : FieldPairingCode) (z : ℂ) : 0 ≤ density n F z :=
    mul_nonneg (Real.rpow_nonneg (by unfold dyadicScale; positivity) _) (Real.exp_pos _).le
  let ν : ℕ → FieldPairingCode → Measure ℂ := fun n F =>
    (volume : Measure ℂ).withDensity fun z => ENNReal.ofReal (density n F z)
  have hν (n : ℕ) : Measurable (ν n) :=
    LQGMeasureField.measurable_withDensity_ofReal (hdensity n)
  have hint (n : ℕ) (f : ℂ → ℝ) (hf : Continuous f) (_ : HasCompactSupport f) :
      Measurable fun F => ∫ z, f z ∂(ν n F) :=
    LQGMeasureField.measurable_integral_withDensity_ofReal (hdensity n)
      (hdensity_nonneg n) hf.measurable
  obtain ⟨M, hM, hlim⟩ := VagueWholePlane.exists_measurable_vagueLimit ν hν hint
  refine ⟨M, hM, ?_⟩
  intro Ω _ S μ hcone hμ
  filter_upwards [ae_fieldCodeDyadicCircle_eq_of_isQuantumCone hcone, hμ,
    hcone.ae_continuousOn_circle] with ω hcircle hL hcont
  have hνeq (n : ℕ) : ν n (fieldPairingCode S ω) = lqgApprox γ (S.hcirc ω) (dyadicScale n) := by
    simp only [ν, density, hcircle]
    rfl
  refine hlim (fieldPairingCode S ω) (μ ω) (fun K hK => Eventually.of_forall fun n => ?_)
    ⟨?_, fun K hK _ => ?_, fun f hf hfc _ => ?_⟩
  · rw [hνeq]
    have hc : Continuous fun z => S.hcirc ω (dyadicScale n) z := by
      rw [← continuousOn_univ]
      exact hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        fun z _ => ⟨dyadicScale_pos n, mem_univ z⟩
    exact LQGMeasureField.withDensity_ofReal_lt_top
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))) hK
  · rw [compl_univ, measure_empty]
  · have := hL.isLocallyFiniteMeasure
    exact hK.measure_lt_top
  · simp_rw [hνeq]
    exact hL.tendsto_integral f hf hfc

/-- **The area measure of a valid environment is a Borel function of its field.** The universal decoder of
`exists_measurable_fieldCode_lqgMeasure_of_isQuantumCone` recovers `S.μ` almost surely. -/
theorem exists_measurable_fieldCode_lqgMeasure (γ : ℝ) :
    ∃ M : FieldPairingCode → Measure ℂ, Measurable M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {𝒮 : SpaceFillingSLEModel}, S.IsValid 𝒮 γ →
        ∀ᵐ ω ∂S.P, M (fieldPairingCode S ω) = S.μ ω := by
  obtain ⟨M, hM, hrec⟩ := exists_measurable_fieldCode_lqgMeasure_of_isQuantumCone γ
  exact ⟨M, hM, fun hS => hrec hS.isQuantumCone hS.isLQGMeasure⟩

end MatedCRT
