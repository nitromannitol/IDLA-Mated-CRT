import MatedCRT.FirstPass.Derived.RevuzRegularize

/-!
# The explicit formula for the Revuz measure

`MatedCRT.revuz W A` is defined through the rational-time regularization of `A`.  Here it is shown that

* the regularization of `A` along a path where `A` is continuous and nondecreasing is `A` itself
  (`regularize_eq_of_continuous_monotone`), so the occupation measure computed from the regularization is the
  occupation measure of `A` (`occupationMeasure_regularize_eq_of_path`);
* for a measurable occupation kernel, `revuz W A S` is the iterated integral
  `∫ dz ∫ W z (dω) ∫_{(0,1]} 1_S(ω_s) dA_s` (`revuz_apply`), and for a positive continuous additive functional the
  regularization can be removed (`revuz_apply_of_isPCAF`).

The measurability hypothesis `hk` on the occupation kernel is supplied by
`measurable_occupationMeasure_regularize` of the companion bridge.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess

/-- Between two nonnegative reals there is a nonnegative rational. -/
theorem exists_nnrat_btwn_nnreal {s t : ℝ≥0} (h : s < t) :
    ∃ q : ℚ≥0, s < (q : ℝ≥0) ∧ (q : ℝ≥0) < t := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (s : ℝ) < t from h)
  have hq0 : 0 ≤ q := by
    have : (0 : ℝ) ≤ s := s.coe_nonneg
    exact_mod_cast this.trans hq1.le
  exact ⟨⟨q, hq0⟩, by exact_mod_cast hq1, by exact_mod_cast hq2⟩

/-- Along a path where `A` is continuous and nondecreasing, the rational-time regularization of `A` is `A`. -/
theorem regularize_eq_of_continuous_monotone {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ω : ContinuousPath ℂ}
    (hc : Continuous fun t => A t ω) (hm : Monotone fun t => A t ω) (t : ℝ≥0) :
    regularize A t ω = A t ω := by
  have hne := nonempty_regularize_index t
  have hcond : ∀ p q : ℚ≥0, p ≤ q → A p ω ≤ A q ω := fun p q hpq => hm (by exact_mod_cast hpq)
  unfold regularize
  split_ifs
  refine le_antisymm ?_ (le_ciInf fun q => hm q.2.le)
  refine le_of_forall_gt_imp_ge_of_dense fun c hc' => ?_
  have hU : {s | A s ω < c} ∈ 𝓝 t := hc.continuousAt.eventually (gt_mem_nhds hc')
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (nhdsWithin_le_nhds hU)
  obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal (show t < u from hu)
  exact (ciInf_le (OrderBot.bddBelow _) (⟨q, hq1⟩ : {q : ℚ≥0 // t < (q : ℝ≥0)})).trans
    (hsub ⟨hq1, hq2⟩).le

/-- Along a path where `A` is continuous and nondecreasing, the occupation measure of the regularization is the
occupation measure of `A`. -/
theorem occupationMeasure_regularize_eq_of_path {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ω : ContinuousPath ℂ}
    (hc : Continuous fun t => A t ω) (hm : Monotone fun t => A t ω) :
    occupationMeasure (fun t => regularize A t ω) ω = occupationMeasure (fun t => A t ω) ω := by
  have h : (fun t => regularize A t ω) = fun t => A t ω :=
    funext (regularize_eq_of_continuous_monotone hc hm)
  rw [h]

/-- **The Revuz measure as an iterated integral**: for a measurable family of laws and a measurable occupation
kernel, `revuz W A S = ∫ dz ∫ W z (dω) (occupation measure of the regularized clock)(S)`. -/
theorem revuz_apply {W : ℂ → Measure (ContinuousPath ℂ)} (hW : Measurable W)
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hk : Measurable fun ω : ContinuousPath ℂ => occupationMeasure (fun t => regularize A t ω) ω)
    {S : Set ℂ} (hS : MeasurableSet S) :
    revuz W A S = ∫⁻ z, ∫⁻ ω, occupationMeasure (fun t => regularize A t ω) ω S ∂W z ∂volume := by
  unfold revuz
  have hm : Measurable fun z : ℂ => (W z).bind fun ω => occupationMeasure (fun t => regularize A t ω) ω :=
    (Measure.measurable_bind' hk).comp hW
  rw [Measure.bind_apply hS hm.aemeasurable]
  refine lintegral_congr fun z => ?_
  rw [Measure.bind_apply hS hk.aemeasurable]

/-- **The explicit Revuz formula for a PCAF**: `revuz W A S = ∫ dz ∫ W z (dω) ∫_{(0,1]} 1_S(ω_s) dA_s`, with the
Stieltjes measure of `A` itself. -/
theorem revuz_apply_of_isPCAF {W : ℂ → Measure (ContinuousPath ℂ)} (hW : Measurable W)
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A)
    (hk : Measurable fun ω : ContinuousPath ℂ => occupationMeasure (fun t => regularize A t ω) ω)
    {S : Set ℂ} (hS : MeasurableSet S) :
    revuz W A S = ∫⁻ z, ∫⁻ ω, occupationMeasure (fun t => A t ω) ω S ∂W z ∂volume := by
  rw [revuz_apply hW hk hS]
  refine lintegral_congr fun z => lintegral_congr_ae ?_
  filter_upwards [hA.path z] with ω hω
  rw [occupationMeasure_regularize_eq_of_path hω.2.1 hω.2.2]

end MatedCRT
