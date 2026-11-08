import HarmonicBalls.Defs.LQG
import HarmonicBalls.Proofs.Sec5.LQGApproxDecoder
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-! # Measurability of the whole-plane LQG measure (B): port of `IsConeField.aemeasurable_lqgMeasure`

The cone statement `IsConeField.aemeasurable_lqgMeasure` (`MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/ConeMeasure.lean:30`)
uses from `IsQuantumCone` only three things: measurability in `ω` of the circle averages `h_r(z)` for `r > 0`, a.s.
continuity of `(r, z) ↦ h_r(z)` on `(0, ∞) × ℂ`, and the a.s. LQG limit. The whole-plane field `IsWholePlaneGFF` gives the
first two for `hcirc` (`IsWholePlaneGFF.measurable_circle`, `IsWholePlaneGFF.ae_continuousOn_circle`). The LQG measure of
`IsLQGMeasureOfField P γ γ hcirc μ` is the γ-LQG measure of the circle averages `fieldCircleAverage γ (hcirc ω)`
= `hcirc ω r z - γ · circleAverage (log ‖·‖) z r`. The shift is deterministic, so it is measurable in `ω`, and it is
continuous on `(0, ∞) × ℂ` by the Jensen-type formula of Mathlib,
`circleAverage (log ‖· - a‖) c R = log R + log⁺ (R⁻¹ ‖c - a‖)` (`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`).
No fact beyond `IsWholePlaneGFF` and `IsLQGMeasureOfField` is needed: (B) is a theorem, not a Step Prop.

The core is stated for any random circle-average family `hε` with these two properties (`aemeasurable_lqgMeasure_of_circleAverages`);
the cone proof is the special case `hε = hcirc`. -/

namespace MatedCRT

open MeasureTheory Filter Topology Set HarmonicBalls ProbabilityTheory
open scoped ENNReal

/-- The measurability core of an LQG measure: for a random family of circle averages `hε ω r z`, measurable in `ω` for
each radius `r > 0` and a.s. continuous on `(0, ∞) × ℂ`, the γ-LQG measure `μ` (`IsLQGMeasure P γ hε μ`) is a.e.
measurable. This is the proof of `IsConeField.aemeasurable_lqgMeasure` with the circle averages `hε` in place of `hcirc`. -/
theorem aemeasurable_lqgMeasure_of_circleAverages {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hε : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hmeas : ∀ (r : ℝ) (z : ℂ), 0 < r → Measurable fun ω => hε ω r z)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hε ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (hL : IsLQGMeasure P γ hε μ) : AEMeasurable μ P := by
  classical
  have hL' : ∀ᵐ ω ∂P, IsLQGLimit γ (hε ω) (μ ω) := hL
  have happrox (r : ℝ) (hr : 0 < r) : AEMeasurable (fun ω => lqgApprox γ (hε ω) r) P := by
    obtain ⟨F, hF, hFeq⟩ := exists_measurable_lqgApprox_decoder γ r
    have hp : Measurable (fun ω (z : ℂ) => hε ω r z) :=
      Measurable.of_eval fun z => hmeas r z hr
    refine (hF.comp hp).aemeasurable.congr ?_
    filter_upwards [hcont] with ω hω
    have hc : Continuous (fun z => hε ω r z) :=
      hω.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨hr, mem_univ z⟩)
    simpa only [Function.comp_apply, lqgApprox] using hFeq (fun z => hε ω r z) hc
  let η : ℕ → Ω → Measure ℂ := fun n => (happrox (dyadicScale n) (dyadicScale_pos n)).mk _
  have hη (n : ℕ) : Measurable (η n) := (happrox (dyadicScale n) (dyadicScale_pos n)).measurable_mk
  have hηeq : ∀ᵐ ω ∂P, ∀ n, η n ω = lqgApprox γ (hε ω) (dyadicScale n) := by
    apply ae_all_iff.mpr
    intro n
    exact (happrox (dyadicScale n) (dyadicScale_pos n)).ae_eq_mk.symm
  let A : Ω → Prop := fun ω => IsLQGLimit γ (hε ω) (μ ω) ∧
    ∀ n, η n ω = lqgApprox γ (hε ω) (dyadicScale n)
  have hgood : ∀ᵐ ω ∂P, A ω := hL'.and hηeq
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  let ν : Ω → Measure ℂ := fun ω => if ω ∈ N then 0 else μ ω
  have hA (ω : Ω) (hω : ω ∉ N) : A ω := by
    by_contra hn
    exact hω (hNsub hn)
  have hloc (ω : Ω) : IsLocallyFiniteMeasure (ν ω) := by
    by_cases hω : ω ∈ N
    · simp only [ν, hω, ite_true]
      infer_instance
    · simpa only [ν, hω, ite_false] using (hA ω hω).1.isLocallyFiniteMeasure
  have hopen (U : Set ℂ) (hU : IsOpen U) : Measurable (fun ω => ν ω U) := by
    obtain ⟨f, hf, hfc, hmass⟩ := exists_open_mass_test_functions hU
    let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
    let G : Ω → ℝ≥0∞ := fun ω => ⨆ i, Filter.liminf
      (fun n => ENNReal.ofReal (∫ z, f i z ∂(η n ω))) atTop
    have hG : Measurable G := by
      apply Measurable.iSup
      intro i
      apply Measurable.liminf
      intro n
      exact (((hf i).stronglyMeasurable.integral_kernel (κ := K)).measurable.comp (hη n)).ennreal_ofReal
    have heq : (fun ω => ν ω U) = (fun ω => if ω ∈ N then 0 else G ω) := by
      funext ω
      by_cases hω : ω ∈ N
      · simp only [ν, hω, ite_true, Measure.coe_zero, Pi.zero_apply]
      · have ha := hA ω hω
        simp only [ν, hω, ite_false]
        rw [hmass (μ ω) ha.1.isLocallyFiniteMeasure]
        congr 1
        funext i
        apply (Filter.Tendsto.liminf_eq _).symm
        apply (ENNReal.continuous_ofReal.tendsto _).comp
        simpa only [ha.2] using ha.1.tendsto_integral (f i) (hf i) (hfc i)
    rw [heq]
    exact Measurable.ite hNmeas measurable_const hG
  have hν := measurable_measure_of_isOpen hloc hopen
  apply hν.aemeasurable.congr
  have hae : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.mpr (by simpa using hNnull)
  filter_upwards [hae] with ω hω
  simp only [ν, hω, ite_false]

/-- **(B) The whole-plane LQG measure is a.e. measurable.** For the whole-plane field `h^ℂ` (`IsWholePlaneGFF P hC hcirc`)
and its γ-LQG measure `μ` of insertion `γ`, the γ-LQG measure `μ = μ_{h^ℂ - γ log|·|}` (`IsLQGMeasureOfField P γ γ hcirc μ`)
is a measurable function of `ω` up to a null set. Whole-plane analogue of `IsConeField.aemeasurable_lqgMeasure`. -/
theorem aemeasurable_wholePlaneLQGMeasure {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hL : IsLQGMeasureOfField P γ γ hcirc μ) : AEMeasurable μ P := by
  refine aemeasurable_lqgMeasure_of_circleAverages (hε := fun ω => fieldCircleAverage γ (hcirc ω)) ?_ ?_ hL
  · intro r z hr
    simp only [fieldCircleAverage]
    exact (hGFF.measurable_circle r z hr).sub measurable_const
  · -- continuity of `(r, z) ↦ log r + log⁺ (r⁻¹ |z|)` on `(0, ∞) × ℂ` (Mathlib's Jensen-type formula)
    have hlogR : ContinuousOn (fun p : ℝ × ℂ => Real.log p.1 + Real.posLog (p.1⁻¹ * ‖p.2‖))
        (Ioi 0 ×ˢ univ) :=
      (ContinuousOn.log continuous_fst.continuousOn (fun p hp => (Set.mem_Ioi.mp hp.1).ne')).add
        (Real.continuous_posLog.comp_continuousOn
          ((ContinuousOn.inv₀ continuous_fst.continuousOn (fun p hp => (Set.mem_Ioi.mp hp.1).ne')).mul
            (continuous_norm.comp continuous_snd).continuousOn))
    have hlog : ContinuousOn (fun p : ℝ × ℂ => Real.circleAverage (fun x => Real.log ‖x‖) p.2 p.1)
        (Ioi 0 ×ˢ univ) := by
      refine hlogR.congr fun p hp => ?_
      have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := p.2) (R := p.1)
        (Set.mem_Ioi.mp hp.1).ne'
      simpa only [sub_zero] using h
    filter_upwards [hGFF.ae_continuousOn_circle] with ω hω
    simp only [fieldCircleAverage]
    exact hω.sub (continuousOn_const.mul hlog)

end MatedCRT
