import MatedCRT.FirstPass.Derived.StieltjesOccupationUniformLimit
import MatedCRT.FirstPass.Derived.RevuzLintegral

/-!
# Occupation integrals converge in measure when the clocks converge uniformly in probability

If continuous nondecreasing clocks `A k` converge to a clock `G` uniformly on `[0, 1]` in probability, that is
`μ {∃ t ≤ 1, η ≤ |A k t - G t|} → 0` for every `η > 0`, then for every continuous `f : ℂ → ℝ` the occupation integrals
`X_k = ∫ f d(occupation measure of A k along b)` converge in `μ`-measure to the occupation integral `X` of `G`.

The proof is the subsequence criterion for convergence in measure: along a subsequence of every subsequence the
clocks converge uniformly almost surely (Borel–Cantelli), and then the occupation integrals converge for every such
path (`tendsto_integral_occupationMeasure_of_tendstoUniformlyOn`).
-/

open MeasureTheory MarkovProcess Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRT.FirstPass.Derived

/-- **Borel–Cantelli extraction.** If `μ (U k η) → 0` for every `η > 0` and `U k η` decreases as `η` decreases,
then along a subsequence of any subsequence, almost every point eventually avoids `U k η`, for every `η > 0`. -/
theorem exists_strictMono_ae_eventually_notMem {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {U : ℕ → ℝ → Set Ω} (hU : ∀ η : ℝ, 0 < η → Tendsto (fun k => μ (U k η)) atTop (𝓝 0))
    (hmono : ∀ k : ℕ, ∀ η η' : ℝ, 0 < η' → η' ≤ η → U k η ⊆ U k η')
    {ns : ℕ → ℕ} (hns : StrictMono ns) :
    ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
      ∀ᵐ b ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop, b ∉ U (ns (ns' i)) η := by
  have hev : ∀ i : ℕ, ∀ᶠ j in atTop, μ (U (ns j) (1 / ((i : ℝ) + 1))) ≤ (1 / 2 : ℝ≥0∞) ^ i := by
    intro i
    have h0 := (hU (1 / ((i : ℝ) + 1)) (by positivity)).comp hns.tendsto_atTop
    have hpos : (0 : ℝ≥0∞) < (1 / 2 : ℝ≥0∞) ^ i := ENNReal.pow_pos (by simp) i
    exact (h0.eventually (gt_mem_nhds hpos)).mono fun j hj => hj.le
  obtain ⟨ns', hns', hle⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨ns', hns', ?_⟩
  have hsum : ∑' i : ℕ, μ (U (ns (ns' i)) (1 / ((i : ℝ) + 1))) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_geometric]
    simp
  filter_upwards [ae_eventually_notMem hsum] with b hb η hη
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  filter_upwards [hb, eventually_ge_atTop N] with i hi hiN hmem
  refine hi (hmono _ _ _ (by positivity) ?_ hmem)
  have hNi : ((N : ℝ) + 1) ≤ (i : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hiN
  exact (one_div_le_one_div_of_le (by positivity) hNi).trans hN.le

/-- **Occupation integrals converge in measure** when the clocks converge uniformly on `[0, 1]` in probability:
`μ {∃ t ≤ 1, η ≤ |A k t - G t|} → 0` for every `η > 0`, the clocks being continuous and nondecreasing almost
surely, and `f` continuous. -/
theorem tendstoInMeasure_integral_occupationMeasure {μ : Measure (ContinuousPath ℂ)} [IsFiniteMeasure μ]
    {A : ℕ → ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {G : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ k, ∀ᵐ b ∂μ, Continuous (fun t => A k t b) ∧ Monotone (fun t => A k t b))
    (hG : ∀ᵐ b ∂μ, Continuous (fun t => G t b) ∧ Monotone (fun t => G t b))
    (hconv : ∀ η : ℝ, 0 < η → Tendsto
      (fun k => μ {b | ∃ t : ℝ≥0, t ≤ 1 ∧ η ≤ |(A k t b : ℝ) - (G t b : ℝ)|}) atTop (𝓝 0))
    {f : ℂ → ℝ} (hf : Continuous f)
    (hmeas : ∀ k, AEStronglyMeasurable
      (fun b => ∫ x, f x ∂occupationMeasure (fun t => A k t b) b) μ) :
    TendstoInMeasure μ (fun k b => ∫ x, f x ∂occupationMeasure (fun t => A k t b) b) atTop
      (fun b => ∫ x, f x ∂occupationMeasure (fun t => G t b) b) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := exists_strictMono_ae_eventually_notMem μ
    (U := fun k η => {b | ∃ t : ℝ≥0, t ≤ 1 ∧ η ≤ |(A k t b : ℝ) - (G t b : ℝ)|}) hconv
    (fun k η η' hη' hle b ⟨t, ht, h⟩ => ⟨t, ht, hle.trans h⟩) hns
  refine ⟨ns', hns', ?_⟩
  have hAall : ∀ᵐ b ∂μ, ∀ k, Continuous (fun t => A k t b) ∧ Monotone (fun t => A k t b) :=
    ae_all_iff.2 hA
  filter_upwards [hae, hAall, hG] with b hb hAb hGb
  refine tendsto_integral_occupationMeasure_of_tendstoUniformlyOn
    (a := fun i t => A (ns (ns' i)) t b) (a' := fun t => G t b)
    (fun i => (hAb _).2) (fun i => (hAb _).1) hGb.2 hGb.1 ?_ b hf
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [hb η hη] with i hi t ht
  have ht1 : t ≤ 1 := ht.2
  rw [Real.dist_eq, abs_sub_comm]
  by_contra hcon
  exact hi ⟨t, ht1, not_lt.1 hcon⟩

/-- **The occupation integral of a nonnegative continuous function against a PCAF is almost everywhere
measurable** in the path. -/
theorem aemeasurable_integral_occupationMeasure {W : ℂ → Measure (ContinuousPath ℂ)}
    {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} (hA : IsPCAF W A) (z : ℂ) {f : ℂ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) :
    AEMeasurable (fun b => ∫ x, f x ∂occupationMeasure (fun t => A t b) b) (W z) := by
  have hg : Measurable fun x => ENNReal.ofReal (f x) := ENNReal.measurable_ofReal.comp hf.measurable
  have hΦ : Measurable fun b : ContinuousPath ℂ =>
      ∫⁻ y, ENNReal.ofReal (f y) ∂occupationMeasure (fun u => regularize A u b) b :=
    (Measure.measurable_lintegral hg).comp (measurable_occupationMeasure_regularize hA.meas)
  refine hΦ.ennreal_toReal.aemeasurable.congr ?_
  filter_upwards [hA.path z] with b hb
  show ENNReal.toReal _ = _
  rw [occupationMeasure_regularize_eq_of_path hb.2.1 hb.2.2,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable]

end MatedCRT.FirstPass.Derived
