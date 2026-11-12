import MatedCRT.FirstPass.Derived.ConeCircleSmearFixed
import MatedCRT.Proofs.Sec1.EnvironmentScaling.ConeObservableIntegrability
import MatedCRT.FirstPass.S2y.ConeRadialCodes

/-!
# The radial part of the quantum cone is almost surely locally `L⁴`

For the circle average embedding of the `γ`-quantum cone (`IsQuantumCone`), almost surely the fourth power of the
radial part `s ↦ h_s(0)` (its jointly measurable version `radialVersion`) is integrable on every `(0, n]`.

Route. The law of the radial process is a probability measure, so `P` is a probability measure
(`IsQuantumCone.isProbabilityMeasure`). Almost surely the circle average process is continuous and the radial part has
the logarithmic majorant `|h_t(0)| ≤ C (1 + |log t|)` on `(0, 2]` (`ae_forall_radialLogMajorant_of_isQuantumCone`).
Near `0` this gives `|h_s(0)|⁴ ≤ 17⁴ C⁴ s^{-1/4}`, an integrable majorant on `(0, 1]`; on `[1, n]` the radial part is
continuous. Combined with `IsQuantumCone.circleSmear_ae_eq_of_radialL4` this gives the circle smear identity for the
quantum cone at every fixed radius `ε ∈ (0, 1]` (`IsQuantumCone.circleSmearIdentity`).
-/

open MeasureTheory ProbabilityTheory Filter Set Topology Real Metric HarmonicBalls MarkovProcess
open scoped Real ENNReal NNReal

namespace MatedCRT.LQGMeasure

/-- `1 + |log s| ≤ 17 s^{-1/16}` for `s ∈ (0, 1]`, from `log x ≤ 16 x^{1/16}` at `x = s⁻¹`. -/
lemma one_add_abs_log_le_rpow {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    1 + |Real.log s| ≤ 17 * s ^ (-(1 / 16) : ℝ) := by
  have hl : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  have h := Real.log_le_rpow_div (inv_nonneg.2 hs.le) (by norm_num : (0 : ℝ) < 1 / 16)
  rw [Real.log_inv, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le] at h
  have h1 : 1 ≤ s ^ (-(1 / 16) : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (by norm_num)
  rw [abs_of_nonpos hl]
  linarith

/-- `(1 + |log s|)⁴ ≤ 17⁴ s^{-1/4}` for `s ∈ (0, 1]`. -/
lemma one_add_abs_log_pow_four_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (1 + |Real.log s|) ^ 4 ≤ 17 ^ 4 * s ^ (-(1 / 4) : ℝ) := by
  have h := pow_le_pow_left₀ (by positivity) (one_add_abs_log_le_rpow hs hs1) 4
  have he : (s ^ (-(1 / 16) : ℝ)) ^ 4 = s ^ (-(1 / 4) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  rwa [mul_pow, he] at h

/-- The law of a `γ`-quantum cone is a probability measure: the radial process has the law
`quantumConeRadialLaw γ ν`, a product of two probability measures. -/
lemma IsQuantumCone.isProbabilityMeasure {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQ : IsQuantumCone γ P hC hcirc) :
    IsProbabilityMeasure P := by
  obtain ⟨ν, hν, hrad⟩ := hQ.radial_law
  have : IsProbabilityMeasure ν := hν.1
  have hR := measurable_radialProcess_circle hQ.measurable_circle
  have hS : Measurable fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s + γ * s :=
    Measurable.of_eval fun s => ((ContinuousMap.measurable_eval s).add_const _)
  have hT : Measurable fun w : ContinuousPath ℝ => fun s : ℝ≥0 => w s - γ * s :=
    Measurable.of_eval fun s => ((ContinuousMap.measurable_eval s).sub_const _)
  have : IsProbabilityMeasure ((brownianMotion 0).map fun w (s : ℝ≥0) => w s + γ * s) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (ν.map fun w (s : ℝ≥0) => w s - γ * s) :=
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 inferInstance
  have hL : IsProbabilityMeasure (P.map fun ω => radialProcess (hcirc ω)) := by
    rw [hrad]; unfold quantumConeRadialLaw; infer_instance
  exact (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).1 hL

/-- **The radial part of the quantum cone is almost surely locally `L⁴`.** For the circle average embedding of the
`γ`-quantum cone, almost surely `s ↦ |radialVersion hcirc ω s| ^ 4` is integrable on `(0, n]` for every `n : ℕ`. -/
theorem IsQuantumCone.ae_integrableOn_radialVersion_pow_four {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQ : IsQuantumCone γ P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      IntegrableOn (fun s => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) (Ioc 0 (n : ℝ)) := by
  have := IsQuantumCone.isProbabilityMeasure hQ
  filter_upwards [MatedCRT.Sec1.ae_forall_radialLogMajorant_of_isQuantumCone hQ, hQ.ae_continuousOn_circle]
    with ω hM hω n
  have hA : ContinuousOn (MatedCRT.CirclePairing.radialVersion hcirc ω) (Ioi 0) :=
    (MatedCRT.CirclePairing.continuousOn_radial hω).congr fun s hs => radialVersion_eq_of_cont hω hs
  have hF : ContinuousOn (fun s => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) (Ioi 0) :=
    (continuous_abs.comp_continuousOn hA).pow 4
  obtain ⟨C, hCb⟩ := hM 1
  -- near `0`: the logarithmic majorant
  have h0 : IntegrableOn (fun s => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) (Ioc 0 1) := by
    have hmaj : IntegrableOn (fun s : ℝ => C ^ 4 * (17 ^ 4 * s ^ (-(1 / 4) : ℝ))) (Ioc 0 1) := by
      have h1 : IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 4) : ℝ)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' (by norm_num)
      exact (((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h1).const_mul (17 ^ 4)).const_mul
        (C ^ 4)
    refine Integrable.mono' hmaj ((hF.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    have hb := hCb s hs.1 (by linarith [hs.2])
    rw [radialVersion_eq_of_cont hω hs.1, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc |hcirc ω s 0| ^ 4 ≤ (C * (1 + |Real.log s|)) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hb 4
      _ = C ^ 4 * (1 + |Real.log s|) ^ 4 := mul_pow _ _ _
      _ ≤ C ^ 4 * (17 ^ 4 * s ^ (-(1 / 4) : ℝ)) :=
        mul_le_mul_of_nonneg_left (one_add_abs_log_pow_four_le hs.1 hs.2) (by positivity)
  -- on `[1, n]`: continuity
  have h1 : IntegrableOn (fun s => |MatedCRT.CirclePairing.radialVersion hcirc ω s| ^ 4) (Icc 1 (n : ℝ)) :=
    (hF.mono fun s hs => lt_of_lt_of_le one_pos hs.1).integrableOn_Icc
  refine (h0.union h1).mono_set fun s hs => ?_
  by_cases h : s ≤ 1
  · exact Or.inl ⟨hs.1, h⟩
  · exact Or.inr ⟨(not_le.1 h).le, hs.2⟩

/-- **The circle smear identity for the quantum cone at a fixed radius.** For the circle average embedding of the
`γ`-quantum cone, a test function `φ` and `ε ∈ (0, 1]`, almost surely `∫ φ(z) h_ε(z) dz = (h, circleKernel φ ε)`. -/
theorem IsQuantumCone.circleSmearIdentity {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQ : IsQuantumCone γ P hC hcirc)
    {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    CircleSmearIdentity P hC hcirc φ ε :=
  IsQuantumCone.circleSmear_ae_eq_of_radialL4 hQ (IsQuantumCone.ae_integrableOn_radialVersion_pow_four hQ) hφ hε hε1

end MatedCRT.LQGMeasure
