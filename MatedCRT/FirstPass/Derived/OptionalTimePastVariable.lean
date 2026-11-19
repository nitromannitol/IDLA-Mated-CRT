import MatedCRT.FirstPass.Derived.PlanarOptionalTimeStrongMarkovIntegral

/-!
# Variables of the past of an optional time

For an optional time `T` of the canonical filtration of planar Brownian paths, a variable `V` of the
path is a variable of the past `F_{T+}` when `{V ∈ B} ∩ {T < t} ∈ F_t` for every measurable `B` and every `t`
(Revuz–Yor (1999), Chapter I, Definition 4.13 and Chapter III, Definition 3.3; this is the form consumed by
`MatedCRT.OptionalTime.integral_pair_shift_optionalTime`).  The path read at an optional time `W ≤ T`,
and the family of such values over a countable family of optional times `W_i ≤ T`, are variables of the past
of `T`: on `{T < t}` all `W_i` are below `t`, where the path read at `min (W_i, t)` is `F_t`-measurable
because the coordinate process is progressively measurable.

* `measurable_untopD_min`: `ω ↦ (min (W ω, t)).untopD 0` is `F_t`-measurable for an optional time `W`.
* `measurableSet_eval_untopD_inter_lt`: `{ω_W ∈ B} ∩ {T < t} ∈ F_t` when `W ≤ T`.
* `measurableSet_pi_eval_untopD_inter_lt`: the same for the family `(ω_{W_i})_i`, with the product
  `σ`-algebra on the values.
-/

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.OptionalTime

/-- The time `min (W, t)` of an optional time `W`, read as a real number, is `F_t`-measurable. -/
theorem measurable_untopD_min {W : ContinuousPath ℂ → WithTop ℝ≥0}
    (hW : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] {ω | W ω < t})
    (t : ℝ≥0) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (fun ω => (min (W ω) (t : WithTop ℝ≥0)).untopD 0) := by
  refine measurable_of_Iio fun s => ?_
  have hset : (fun ω => (min (W ω) (t : WithTop ℝ≥0)).untopD 0) ⁻¹' Iio s =
      {ω | W ω < (s : WithTop ℝ≥0)} ∪ {_ω | t < s} := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_union, mem_ofPred_eq]
    rcases eq_or_ne (W ω) ⊤ with h | h
    · rw [h, min_eq_right le_top, WithTop.untopD_coe]
      exact ⟨Or.inr, fun h' => h'.resolve_left not_top_lt⟩
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h
      rw [← ha, ← WithTop.coe_min, WithTop.untopD_coe, WithTop.coe_lt_coe, min_lt_iff]
  rw [hset]
  by_cases hts : t < s
  · simp [hts]
  · have hst : s ≤ t := le_of_not_gt hts
    simp only [hts, ofPred_false, union_empty]
    exact (ContinuousPath.canonicalFiltration (alpha := ℂ)).mono hst _ (hW s)

theorem untopD_min_le (a : WithTop ℝ≥0) (t : ℝ≥0) :
    (min a (t : WithTop ℝ≥0)).untopD 0 ≤ t := by
  rcases eq_or_ne a ⊤ with h | h
  · rw [h, min_eq_right le_top, WithTop.untopD_coe]
  · obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 h
    rw [← hc, ← WithTop.coe_min, WithTop.untopD_coe]
    exact min_le_right _ _

/-- The path read at the time `min (W, t)` is `F_t`-measurable. -/
theorem measurable_eval_untopD_min {W : ContinuousPath ℂ → WithTop ℝ≥0}
    (hW : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] {ω | W ω < t})
    (t : ℝ≥0) :
    Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (fun ω : ContinuousPath ℂ => ω ((min (W ω) (t : WithTop ℝ≥0)).untopD 0)) := by
  have hg := measurable_untopD_min hW t
  have hpair : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t,
      (borel ℝ).prod (ContinuousPath.canonicalFiltration (alpha := ℂ) t)]
      (fun ω : ContinuousPath ℂ => ((((min (W ω) (t : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : ℝ), ω)) :=
    (measurable_coe_nnreal_real.comp hg).prodMk measurable_id
  have h := (ContinuousPath.measurable_clampedCoordinate (alpha := ℂ) t).comp hpair
  convert h using 1
  funext ω
  show ω _ = ω (min (Real.toNNReal _) t)
  rw [Real.toNNReal_coe, min_eq_left (untopD_min_le _ _)]

/-- **The path read at an optional time `W ≤ T` is a variable of the past of `T`.** -/
theorem measurableSet_eval_untopD_inter_lt {W T : ContinuousPath ℂ → WithTop ℝ≥0}
    (hW : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] {ω | W ω < t})
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] {ω | T ω < t})
    (hWT : ∀ ω, W ω ≤ T ω) {B : Set ℂ} (hB : MeasurableSet B) (t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      ((fun ω : ContinuousPath ℂ => ω ((W ω).untopD 0)) ⁻¹' B ∩ {ω | T ω < t}) := by
  have hset : (fun ω : ContinuousPath ℂ => ω ((W ω).untopD 0)) ⁻¹' B ∩ {ω | T ω < t} =
      (fun ω : ContinuousPath ℂ => ω ((min (W ω) (t : WithTop ℝ≥0)).untopD 0)) ⁻¹' B ∩
        {ω | T ω < t} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, and_congr_left_iff]
    intro hlt
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt ((hWT ω).trans_lt hlt))
    have hat : W ω < t := (hWT ω).trans_lt hlt
    rw [← ha] at hat ⊢
    rw [← WithTop.coe_min, min_eq_left (WithTop.coe_lt_coe.1 hat).le]
  rw [hset]
  exact ((measurable_eval_untopD_min hW t) hB).inter (hT t)

/-- **A countable-or-not family of paths read at optional times `W_i ≤ T`** is a variable of the past of
`T`, for the product `σ`-algebra on the values. -/
theorem measurableSet_pi_eval_untopD_inter_lt {ι : Type*} {W : ι → ContinuousPath ℂ → WithTop ℝ≥0}
    {T : ContinuousPath ℂ → WithTop ℝ≥0}
    (hW : ∀ i, ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] {ω | W i ω < t})
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] {ω | T ω < t})
    (hWT : ∀ i ω, W i ω ≤ T ω) {B : Set (ι → ℂ)} (hB : MeasurableSet B) (t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      ((fun ω (i : ι) => ω ((W i ω).untopD 0)) ⁻¹' B ∩ {ω | T ω < t}) := by
  let V : ContinuousPath ℂ → ι → ℂ := fun ω i => ω ((W i ω).untopD 0)
  let 𝒮 : MeasurableSpace (ι → ℂ) :=
    { MeasurableSet' := fun B => ∀ t : ℝ≥0,
        MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] (V ⁻¹' B ∩ {ω | T ω < t})
      measurableSet_empty := fun t => by simp
      measurableSet_compl := fun B hB t => by
        have h : V ⁻¹' Bᶜ ∩ {ω | T ω < t} = {ω | T ω < t} \ (V ⁻¹' B ∩ {ω | T ω < t}) := by
          ext ω; simp only [mem_inter_iff, mem_preimage, mem_compl_iff, Set.mem_sdiff, mem_ofPred_eq]; tauto
        rw [h]
        exact (hT t).diff (hB t)
      measurableSet_iUnion := fun f hf t => by
        have h : V ⁻¹' (⋃ n, f n) ∩ {ω | T ω < t} = ⋃ n, (V ⁻¹' f n ∩ {ω | T ω < t}) := by
          ext ω; simp only [mem_inter_iff, mem_preimage, mem_iUnion]; aesop
        rw [h]
        exact MeasurableSet.iUnion fun n => hf n t }
  have hle : (MeasurableSpace.pi : MeasurableSpace (ι → ℂ)) ≤ 𝒮 := by
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro B' hB' t'
    exact measurableSet_eval_untopD_inter_lt (hW i) hT (hWT i) hB' t'
  exact hle B hB t

end MatedCRT.OptionalTime
