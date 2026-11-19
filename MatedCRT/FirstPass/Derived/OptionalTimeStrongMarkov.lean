import MarkovProcess.Trajectory.StoppingLtTop
import MarkovProcess.Trajectory.StartingPointContinuity
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# The strong Markov property at optional times

Let `P` be a conservative Feller semigroup with a continuous modification, and `W x` the law of
its canonical continuous process started from `x`. Let `T` be an *optional time* of the canonical
filtration `(F⁰_t)`, that is `{T < t} ∈ F⁰_t` for every `t` (a stopping time of the
right-continuous filtration `F⁰_{t+}`), possibly infinite, and let `A` be an event of `F_{T+}`,
that is `A ∩ {T < t} ∈ F⁰_t` for every `t`. Then, on `A ∩ {T < ∞}`, the law of the path shifted
at `T` is the mixture of the laws `W (ω T)` (Revuz–Yor (1999), Theorem III.3.7 and its proof).

The proof: the times `T + ε`, `ε > 0`, are stopping times of `(F⁰_t)` and `A ∩ {T < ∞}` lies in
`F_{T+ε}`, so the strong Markov property at stopping times
(`continuousProcess_restrict_map_shift_stoppingTime_lt_top`) applies at `T + ε`. As `ε ↓ 0`, the
integral of a bounded continuous function of finitely many coordinates of the shifted path
converges on both sides, by path continuity and the Feller continuity of the finite-dimensional
expectations in the starting point (`continuous_integral_finsetEvaluation_continuousProcess`) and
dominated convergence. A finite measure on path space is determined by these integrals.

## Main results

* `measurableSet_inter_add_le`: `F_{T+}` events lie in the stopped `σ`-algebra of `T + ε`.
* `isStoppingTime_add`: `T + ε` is a stopping time.
* `measurable_untopD`: the finite part of an optional time is measurable.
* `continuousProcess_restrict_map_shift_optionalTime_lt_top`: the strong Markov property at `T`
  in restart form, for events of `F_{T+}`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MatedCRT.OptionalTime

section Times

variable {Ω : Type*}

/-- A time is finite exactly when it lies below some natural number. -/
theorem lt_top_iff_exists_nat_lt (τ : WithTop ℝ≥0) :
    τ < ⊤ ↔ ∃ n : ℕ, τ < ((n : ℝ≥0) : WithTop ℝ≥0) := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h.ne
    obtain ⟨n, hn⟩ := exists_nat_gt a
    exact ⟨n, ha ▸ WithTop.coe_lt_coe.2 hn⟩
  · rintro ⟨n, hn⟩
    exact hn.trans (WithTop.coe_lt_top _)

/-- For `0 < ε ≤ t`: `τ + ε ≤ t` iff `τ < t - ε + min ε (1 / (n + 1))` for every `n`. -/
theorem add_le_iff_forall_lt (τ : WithTop ℝ≥0) {ε t : ℝ≥0} (hε : 0 < ε) (hεt : ε ≤ t) :
    τ + (ε : WithTop ℝ≥0) ≤ t ↔
      ∀ n : ℕ, τ < ((t - ε + min ε (1 / ((n : ℝ≥0) + 1)) : ℝ≥0) : WithTop ℝ≥0) := by
  rcases eq_or_ne τ ⊤ with h | h
  · subst h
    constructor
    · intro h
      rw [WithTop.top_add] at h
      exact absurd h (WithTop.not_top_le_coe t)
    · intro h
      exact absurd (h 0) not_top_lt
  obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.1 h
  rw [← WithTop.coe_add, WithTop.coe_le_coe]
  simp only [WithTop.coe_lt_coe]
  rw [← le_tsub_iff_right hεt]
  constructor
  · intro ha n
    have hpos : 0 < min ε (1 / ((n : ℝ≥0) + 1)) := lt_min hε (by positivity)
    exact lt_of_le_of_lt ha (lt_add_of_pos_right _ hpos)
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hlt)
    have h1 : a < t - ε + 1 / ((n : ℝ≥0) + 1) :=
      (h n).trans_le (by gcongr; exact min_le_right _ _)
    have h2 : t - ε + 1 / ((n : ℝ≥0) + 1) < a :=
      calc t - ε + 1 / ((n : ℝ≥0) + 1) < t - ε + (a - (t - ε)) := by gcongr
        _ = a := add_tsub_cancel_of_le hlt.le
    exact lt_irrefl _ (h1.trans h2)

end Times

section Filtration

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]

/-- An event of `F_{T+}` (`S ∩ {T < t} ∈ F⁰_t` for all `t`) meets `{T + ε ≤ t}` in an
`F⁰_t`-event, for every `ε > 0`. -/
theorem measurableSet_inter_add_le {T : ContinuousPath α → WithTop ℝ≥0}
    {S : Set (ContinuousPath α)}
    (hS : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      (S ∩ {ω | T ω < t}))
    {ε : ℝ≥0} (hε : 0 < ε) (t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      (S ∩ {ω | T ω + (ε : WithTop ℝ≥0) ≤ t}) := by
  by_cases hεt : ε ≤ t
  · have hset : S ∩ {ω | T ω + (ε : WithTop ℝ≥0) ≤ t} =
        ⋂ n : ℕ, S ∩ {ω | T ω < ((t - ε + min ε (1 / ((n : ℝ≥0) + 1)) : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_inter_iff, mem_iInter]
      have key := add_le_iff_forall_lt (T ω) hε hεt
      exact ⟨fun h n => ⟨h.1, key.1 h.2 n⟩, fun h => ⟨(h 0).1, key.2 fun n => (h n).2⟩⟩
    rw [hset]
    refine MeasurableSet.iInter fun n => ?_
    have hle : t - ε + min ε (1 / ((n : ℝ≥0) + 1)) ≤ t := by
      calc t - ε + min ε (1 / ((n : ℝ≥0) + 1)) ≤ t - ε + ε := by gcongr; exact min_le_left _ _
        _ = t := tsub_add_cancel_of_le hεt
    exact (ContinuousPath.canonicalFiltration (alpha := α)).mono hle _ (hS _)
  · have hempty : S ∩ {ω | T ω + (ε : WithTop ℝ≥0) ≤ t} = ∅ := by
      refine eq_empty_of_forall_notMem fun ω hω => hεt ?_
      have h2 : T ω + (ε : WithTop ℝ≥0) ≤ t := hω.2
      rcases eq_or_ne (T ω) ⊤ with h | h
      · rw [h, WithTop.top_add] at h2
        exact absurd h2 (WithTop.not_top_le_coe t)
      · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h
        rw [← ha, ← WithTop.coe_add, WithTop.coe_le_coe] at h2
        exact le_add_self.trans h2
    rw [hempty]
    exact @MeasurableSet.empty _ (ContinuousPath.canonicalFiltration (alpha := α) t)

/-- The translate `T + ε` (`ε > 0`) of an optional time is a stopping time. -/
theorem isStoppingTime_add {T : ContinuousPath α → WithTop ℝ≥0}
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      {ω | T ω < t})
    {ε : ℝ≥0} (hε : 0 < ε) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := α))
      (fun ω => T ω + (ε : WithTop ℝ≥0)) := by
  intro t
  have h := measurableSet_inter_add_le (S := univ) (T := T)
    (fun t => by rw [univ_inter]; exact hT t) hε t
  rwa [univ_inter] at h

/-- The part of an `F_{T+}` event on which `T` is finite is `F⁰_∞`-measurable. -/
theorem measurableSet_inter_lt_top {T : ContinuousPath α → WithTop ℝ≥0}
    {S : Set (ContinuousPath α)}
    (hS : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      (S ∩ {ω | T ω < t})) :
    MeasurableSet[⨆ t, ContinuousPath.canonicalFiltration (alpha := α) t]
      (S ∩ {ω | T ω < ⊤}) := by
  have hset : S ∩ {ω | T ω < ⊤} = ⋃ n : ℕ, S ∩ {ω | T ω < ((n : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_inter_iff, mem_iUnion]
    have key := lt_top_iff_exists_nat_lt (T ω)
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := key.1 h2
      exact ⟨n, h1, hn⟩
    · rintro ⟨n, h1, h2⟩
      exact ⟨h1, key.2 ⟨n, h2⟩⟩
  rw [hset]
  exact MeasurableSet.iUnion fun n =>
    le_iSup (fun t => ContinuousPath.canonicalFiltration (alpha := α) t) (n : ℝ≥0) _ (hS _)

/-- An `F_{T+}` event, restricted to `{T < ∞}`, is an event of the stopped `σ`-algebra of the
stopping time `T + ε`. -/
theorem measurableSet_stopped_add {T : ContinuousPath α → WithTop ℝ≥0}
    {A : Set (ContinuousPath α)}
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      {ω | T ω < t})
    (hA : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      (A ∩ {ω | T ω < t}))
    {ε : ℝ≥0} (hε : 0 < ε) :
    MeasurableSet[(isStoppingTime_add hT hε).measurableSpace] (A ∩ {ω | T ω < ⊤}) := by
  refine ⟨measurableSet_inter_lt_top hA, fun t => ?_⟩
  convert measurableSet_inter_add_le hA hε t using 1
  ext ω
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    have h3' : T ω + (ε : WithTop ℝ≥0) ≤ t := h3
    exact ⟨⟨h1, lt_of_le_of_lt (le_self_add.trans h3') (WithTop.coe_lt_top _)⟩, h3⟩

/-- The finite part `(T ω).untopD 0` of an optional time is measurable. -/
theorem measurable_untopD {T : ContinuousPath α → WithTop ℝ≥0}
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      {ω | T ω < t}) :
    Measurable fun ω => (T ω).untopD 0 := by
  have hlt : ∀ t : ℝ≥0, MeasurableSet {ω | T ω < t} := fun t =>
    (ContinuousPath.canonicalFiltration (alpha := α)).le t _ (hT t)
  have htop : MeasurableSet {ω | T ω < ⊤} := by
    have h := measurableSet_inter_lt_top (S := univ) (T := T)
      (fun t => by rw [univ_inter]; exact hT t)
    rw [univ_inter] at h
    exact (iSup_le fun t => (ContinuousPath.canonicalFiltration (alpha := α)).le t) _ h
  refine measurable_of_Iio fun t => ?_
  have hset : (fun ω => (T ω).untopD 0) ⁻¹' Iio t =
      {ω | T ω < t} ∪ ({ω | T ω < ⊤}ᶜ ∩ {_ω | 0 < t}) := by
    ext ω
    rcases eq_or_ne (T ω) ⊤ with h | h
    · simp [h, show ((⊤ : WithTop ℝ≥0)).untopD 0 = 0 from rfl]
      exact fun h' => absurd h' not_top_lt
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h
      simp [← ha]
      exact ⟨fun h' => Or.inl (WithTop.coe_lt_coe.2 h'),
        fun h' => h'.elim WithTop.coe_lt_coe.1 fun h'' => absurd (WithTop.coe_lt_top a) h''.1⟩
  rw [hset]
  exact (hlt t).union (htop.compl.inter (MeasurableSet.const _))

/-- The state `ω ((T ω).untopD 0)` at an optional time is measurable. -/
theorem measurable_eval_untopD [SecondCountableTopology α] {T : ContinuousPath α → WithTop ℝ≥0}
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      {ω | T ω < t}) :
    Measurable fun ω : ContinuousPath α => ω ((T ω).untopD 0) := by
  have hc : Continuous fun p : ContinuousPath α × ℝ≥0 => p.1 p.2 := continuous_eval
  exact hc.measurable.comp (measurable_id.prodMk (measurable_untopD hT))

end Filtration

section Path

variable {α : Type*} [MetricSpace α] [CompleteSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [Nonempty α] [LocallyCompactSpace α]

/-- **Strong Markov property at an optional time, in restart form.** Let `T` be an optional time
of the canonical filtration (`{T < t} ∈ F⁰_t` for every `t`), possibly infinite, and `A` an event
of `F_{T+}` (`A ∩ {T < t} ∈ F⁰_t` for every `t`). On `A ∩ {T < ∞}`, the law of the path shifted at
`T` is the mixture of the laws of the process started from the state at `T`. -/
theorem continuousProcess_restrict_map_shift_optionalTime_lt_top
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (x : α)
    (T : ContinuousPath α → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      {ω | T ω < t})
    (A : Set (ContinuousPath α))
    (hA : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t]
      (A ∩ {ω | T ω < t})) :
    ((SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP x).restrict (A ∩ {ω | T ω < ⊤})).map
        (fun ω ↦ ContinuousPath.shift ((T ω).untopD 0) ω) =
      Kernel.comap (SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP)
          (fun ω ↦ ω ((T ω).untopD 0)) (measurable_eval_untopD hT) ∘ₘ
        ((SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP x).restrict (A ∩ {ω | T ω < ⊤})) := by
  set W := SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP with hW
  set S := A ∩ {ω | T ω < ⊤} with hS
  set μ := (W x).restrict S with hμ
  have hSm : MeasurableSet S :=
    (iSup_le fun t => (ContinuousPath.canonicalFiltration (alpha := α)).le t) _
      (measurableSet_inter_lt_top hA)
  -- the stopping times `T + εₙ`, `εₙ = 1 / (n + 1)`
  set ε : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1) with hε_def
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hε_def] using h0
  have hτ : ∀ n, IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := α))
      (fun ω => T ω + (ε n : WithTop ℝ≥0)) := fun n => isStoppingTime_add hT (hεpos n)
  have hσS : ∀ n, ∀ ω ∈ S, (T ω + (ε n : WithTop ℝ≥0)).untopD 0 = (T ω).untopD 0 + ε n := by
    intro n ω hω
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (show T ω < ⊤ from hω.2).ne
    rw [← ha, ← WithTop.coe_add]
    rfl
  have hlimσ : ∀ ω ∈ S, Tendsto (fun n => (T ω + (ε n : WithTop ℝ≥0)).untopD 0) atTop
      (𝓝 ((T ω).untopD 0)) := by
    intro ω hω
    have h : Tendsto (fun n => (T ω).untopD 0 + ε n) atTop (𝓝 ((T ω).untopD 0 + 0)) :=
      tendsto_const_nhds.add hεlim
    rw [add_zero] at h
    exact h.congr fun n => (hσS n ω hω).symm
  have hR : ∀ n, μ.map (fun ω => ContinuousPath.shift ((T ω + (ε n : WithTop ℝ≥0)).untopD 0) ω) =
      Kernel.comap W (fun ω => ω ((T ω + (ε n : WithTop ℝ≥0)).untopD 0))
        (ContinuousPath.measurable_eval_untopD_stoppingTime _ (hτ n)) ∘ₘ μ := by
    intro n
    have h := hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top P hP hK x _ (hτ n) S
      (measurableSet_stopped_add hT hA (hεpos n))
    have hSS : S ∩ {ω | T ω + (ε n : WithTop ℝ≥0) < ⊤} = S := by
      refine inter_eq_left.2 fun ω hω => ?_
      exact WithTop.add_lt_top.2 ⟨hω.2, WithTop.coe_lt_top _⟩
    beta_reduce at h
    rw [hSS] at h
    exact h
  -- integrals of bounded continuous functions of finitely many coordinates
  have hW_int : ∀ (J : Finset ℝ≥0) (f : (J → α) →ᵇ ℝ) (Y : ContinuousPath α → α)
      (hY : Measurable Y),
      ∫ η, f (ContinuousPath.finsetEvaluation J η) ∂(Kernel.comap W Y hY ∘ₘ μ) =
        ∫ ω, (∫ η, f (ContinuousPath.finsetEvaluation J η) ∂(W (Y ω))) ∂μ := by
    intro J f Y hY
    rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp]
    · simp only [Kernel.const_apply, Kernel.comap_apply]
    · exact Integrable.of_bound
        ((f.continuous.comp (ContinuousPath.continuous_finiteEvaluation _)).aestronglyMeasurable)
        ‖f‖ (ae_of_all _ fun η => f.norm_coe_le_norm _)
  have hmap_int : ∀ (J : Finset ℝ≥0) (f : (J → α) →ᵇ ℝ)
      (Φ : ContinuousPath α → ContinuousPath α) (hΦ : Measurable Φ),
      ∫ η, f (ContinuousPath.finsetEvaluation J η) ∂(μ.map Φ) =
        ∫ ω, f (ContinuousPath.finsetEvaluation J (Φ ω)) ∂μ := by
    intro J f Φ hΦ
    exact integral_map hΦ.aemeasurable
      (f.continuous.comp (ContinuousPath.continuous_finiteEvaluation _)).aestronglyMeasurable
  have hkey : ∀ (J : Finset ℝ≥0) (f : (J → α) →ᵇ ℝ),
      ∫ ω, f (ContinuousPath.finsetEvaluation J
          (ContinuousPath.shift ((T ω).untopD 0) ω)) ∂μ =
        ∫ ω, (∫ η, f (ContinuousPath.finsetEvaluation J η) ∂(W (ω ((T ω).untopD 0)))) ∂μ := by
    intro J f
    set u : α → ℝ := fun y => ∫ η, f (ContinuousPath.finsetEvaluation J η) ∂(W y) with hu_def
    have hu : Continuous u :=
      hFeller.continuous_integral_finsetEvaluation_continuousProcess P hP hK J f
    have hFc : Continuous fun η : ContinuousPath α => f (ContinuousPath.finsetEvaluation J η) :=
      f.continuous.comp (ContinuousPath.continuous_finiteEvaluation _)
    have hu_bd : ∀ y, ‖u y‖ ≤ ‖f‖ := fun y => by
      simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
        norm_integral_le_of_norm_le_const (μ := W y)
          (ae_of_all _ fun η => f.norm_coe_le_norm (ContinuousPath.finsetEvaluation J η))
    have hn : ∀ n, ∫ ω, f (ContinuousPath.finsetEvaluation J
          (ContinuousPath.shift ((T ω + (ε n : WithTop ℝ≥0)).untopD 0) ω)) ∂μ =
        ∫ ω, u (ω ((T ω + (ε n : WithTop ℝ≥0)).untopD 0)) ∂μ := by
      intro n
      have hΦ : Measurable fun ω =>
          ContinuousPath.shift ((T ω + (ε n : WithTop ℝ≥0)).untopD 0) ω :=
        ContinuousPath.measurable_shift_untopD_stoppingTime _ (hτ n)
      have h := congrArg (fun m => ∫ η, f (ContinuousPath.finsetEvaluation J η) ∂m) (hR n)
      rw [hmap_int J f _ hΦ, hW_int] at h
      exact h
    have hL : Tendsto (fun n => ∫ ω, f (ContinuousPath.finsetEvaluation J
          (ContinuousPath.shift ((T ω + (ε n : WithTop ℝ≥0)).untopD 0) ω)) ∂μ) atTop
        (𝓝 (∫ ω, f (ContinuousPath.finsetEvaluation J
          (ContinuousPath.shift ((T ω).untopD 0) ω)) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) (fun n => ?_)
        (integrable_const _) (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _) ?_
      · exact (hFc.measurable.comp
          (ContinuousPath.measurable_shift_untopD_stoppingTime _ (hτ n))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem hSm] with ω hω
        have hc : Continuous fun t : ℝ≥0 =>
            f (ContinuousPath.finsetEvaluation J (ContinuousPath.shift t ω)) :=
          hFc.comp (ContinuousPath.continuous_shift.comp (continuous_id.prodMk continuous_const))
        exact (hc.tendsto _).comp (hlimσ ω hω)
    have hRlim : Tendsto (fun n => ∫ ω, u (ω ((T ω + (ε n : WithTop ℝ≥0)).untopD 0)) ∂μ) atTop
        (𝓝 (∫ ω, u (ω ((T ω).untopD 0)) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) (fun n => ?_)
        (integrable_const _) (fun n => ae_of_all _ fun ω => hu_bd _) ?_
      · exact (hu.measurable.comp
          (ContinuousPath.measurable_eval_untopD_stoppingTime _ (hτ n))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem hSm] with ω hω
        exact ((hu.comp ω.continuous).tendsto _).comp (hlimσ ω hω)
    exact tendsto_nhds_unique (hL.congr hn) hRlim
  -- identification through the finite-dimensional marginals
  have hevm : ∀ J : Finset ℝ≥0, Measurable (ContinuousPath.finsetEvaluation (alpha := α) J) :=
    fun J => (ContinuousPath.continuous_finiteEvaluation _).measurable
  have hΦs : Measurable fun ω => ContinuousPath.shift ((T ω).untopD 0) ω :=
    ContinuousPath.measurable_shift_of_measurable _ (measurable_untopD hT)
  have hfd : ∀ J : Finset ℝ≥0,
      (μ.map fun ω => ContinuousPath.shift ((T ω).untopD 0) ω).map
          (ContinuousPath.finsetEvaluation J) =
        (Kernel.comap W (fun ω => ω ((T ω).untopD 0)) (measurable_eval_untopD hT) ∘ₘ μ).map
          (ContinuousPath.finsetEvaluation J) := by
    intro J
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map (hevm J).aemeasurable
        f.continuous.aestronglyMeasurable,
      integral_map (hevm J).aemeasurable
        f.continuous.aestronglyMeasurable, hmap_int J f _ hΦs, hW_int]
    exact hkey J f
  have hker := MarkovProcess.Kernel.eq_of_map_denseFiniteEvaluation_eq
    (Kernel.const Unit (μ.map fun ω => ContinuousPath.shift ((T ω).untopD 0) ω))
    (Kernel.const Unit
      (Kernel.comap W (fun ω => ω ((T ω).untopD 0)) (measurable_eval_untopD hT) ∘ₘ μ))
    (fun I => by
      ext u : 1
      rw [Kernel.map_apply _ (hevm _),
        Kernel.map_apply _ (hevm _),
        Kernel.const_apply, Kernel.const_apply]
      exact hfd _)
  have h := congrArg (fun κ => κ ()) hker
  simp only [Kernel.const_apply] at h
  exact h

end Path

end MatedCRT.OptionalTime
