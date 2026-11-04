import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.PotentialTightness
import MatedCRT.Proofs.Measurability.EnvSigma

/-! Uniform bounds in probability for random continuous test functions. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

/-- A pointwise measurable random continuous function, bounded on an open
set for every outcome, has a uniform bound in probability. -/
theorem exists_testFunction_bound_in_probability {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (U : Set ℂ) (hU : IsOpen U)
    (f : Ω → ℂ → ℝ) (hfmeas : ∀ x, AEMeasurable (fun ω => f ω x) P)
    (hfcont : ∀ ω, ContinuousOn (f ω) U)
    (hfbound : ∀ ω, ∃ M : ℝ, ∀ x ∈ U, |f ω x| ≤ M)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ P {ω | ∃ x ∈ U, M < |f ω x|} < δ := by
  obtain ⟨t, htU, htc, hUt⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace U).exists_countable_dense_subset
  let : Countable t := htc.to_subtype
  let X : Ω → ℝ≥0∞ := fun ω => ⨆ x : t, ENNReal.ofReal |f ω x|
  have hXm : AEMeasurable X P := by
    apply AEMeasurable.iSup
    intro x
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hfmeas x).abs
  have hXfinite : ∀ ω, X ω < ⊤ := by
    intro ω
    obtain ⟨M, hM⟩ := hfbound ω
    have hle : X ω ≤ ENNReal.ofReal M := by
      apply iSup_le
      intro x
      exact ENNReal.ofReal_le_ofReal (hM x (htU x.property))
    exact hle.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨n, hn⟩ := exists_nat_measure_gt_lt P X hXm (Eventually.of_forall hXfinite) hδ
  refine ⟨(n : ℝ) + 1, by positivity, (measure_mono ?_).trans_lt hn⟩
  intro ω hω
  obtain ⟨x, hxU, hx⟩ := hω
  let V : Set ℂ := U ∩ (fun y => |f ω y|) ⁻¹' Ioi ((n : ℝ) + 1)
  have hV : IsOpen V := (continuous_abs.comp_continuousOn (hfcont ω)).isOpen_inter_preimage hU isOpen_Ioi
  have hxV : x ∈ V := ⟨hxU, hx⟩
  obtain ⟨y, hyV, hyt⟩ := mem_closure_iff.1 (hUt hxU) V hV hxV
  have hsmall : ENNReal.ofReal |f ω y| ≤ X ω := le_iSup (fun x : t => ENNReal.ofReal |f ω x|) ⟨y, hyt⟩
  have hlarge : (n : ℝ≥0∞) < ENNReal.ofReal |f ω y| := by
    have : (n : ℝ) < |f ω y| := lt_trans (by linarith) hyV.2
    simpa using ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity : (0 : ℝ) ≤ n)).2 this)
  exact hlarge.trans_le hsmall

/-- The hypotheses of Lemma 3.4 give uniform bounds in probability. -/
theorem MatedCRTEnv.IsValid.exists_testFunction_bound_in_probability
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (z : ℂ) (r : ℝ) (f : Ω → ℂ → ℝ)
    (hfmeas : ∀ x, Measurable[S.envSigma] fun ω => f ω x)
    (hfcont : ∀ ω, IsHolderContinuousOn (f ω) (ball z r))
    (hfbound : ∀ ω, ∃ M : ℝ, ∀ x ∈ ball z r, |f ω x| ≤ M)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ S.P {ω | ∃ x ∈ ball z r, M < |f ω x|} < δ := by
  let := hS.isProbabilityMeasure
  apply MatedCRT.exists_testFunction_bound_in_probability S.P (ball z r) isOpen_ball f
    (fun x => hS.aemeasurable_of_envSigma (hfmeas x)) ?_ hfbound hδ
  intro ω
  obtain ⟨C, χ, hχ, _, h⟩ := hfcont ω
  exact h.continuousOn hχ

end MatedCRT
