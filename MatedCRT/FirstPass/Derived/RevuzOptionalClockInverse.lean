import MatedCRT.FirstPass.Derived.RevuzOptionalAdditivity

/-!
# The right inverse of a PCAF clock as an optional time, and its additivity

Let `A` be a positive continuous additive functional of planar Brownian motion with a good clock
(`IsPCAF`, `GoodClock`), and let `τ_r = inf {t | r < A_t}` be the right inverse of the clock
(`clockInverse`). The raw functional `A_q` is only adapted up to null sets, so `τ_r` itself need
not be an optional time of the canonical filtration; it agrees almost surely with one
(Revuz–Yor (1999), Chapter X, Section 1 and Proposition V.1.1; Fukushima–Oshima–Takeda (2011),
Section A.3). From `F⁰_q`-measurable versions `g_q` of `A_q` at the rational times `q`, the
rational inverse clock `inf {q ∈ ℚ≥0 | r < g_q}` satisfies
`{inf {q | r < g_q} < t} = ⋃_{q < t} {r < g_q} ∈ F⁰_t`, and it equals `τ_r` along every path where
`g_q = A_q` for all rational `q` and the clock is nondecreasing and exceeds `r`.

Combined with the additivity of the clock at optional times, this gives the additivity of the
time change: almost surely, for every `v`, `τ_{r+v} = τ_r + τ_v ∘ θ_{τ_r}`, where the clock read on
the shifted path is the rational-time regularization `Ā` of `A` (the raw clock is regular along
`θ_{τ_r} ω` only on an event that need not be measurable).

## Main results

* `pathFiltration_le_canonicalFiltration`: `F⁰_t` lies in the canonical filtration at time `t`.
* `rationalClockInverse`: the rational inverse clock `inf {q ∈ ℚ≥0 | r < g_q}`.
* `measurableSet_rationalClockInverse_lt`: it is an optional time for `F⁰_q`-measurable `g_q`.
* `rationalClockInverse_eq_clockInverse`: deterministic identification with `τ_r`.
* `ae_rationalClockInverse_eq_clockInverse`: almost surely, the identification for every level.
* `exists_optionalTime_ae_eq_clockInverse`: an optional version of the whole family `(τ_r)_r`.
* `apply_clockInverse_eq`: `A_{τ_r} = r` for a continuous nondecreasing clock from `0`.
* `ae_clockInverse_add_eq_shift`: `τ_{r+v} = τ_r + τ_v^{Ā} ∘ θ_{τ_r}` almost surely, for every `v`.
* `ae_eval_clockInverse_add_eq_shift`: the same for the time-changed path `B_{τ_{r+v}}`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT

/-- The natural `σ`-field `F⁰_t` of the planar path is contained in the canonical filtration at
time `t`. -/
theorem pathFiltration_le_canonicalFiltration (t : ℝ≥0) :
    pathFiltration t ≤ ContinuousPath.canonicalFiltration (alpha := ℂ) t := by
  show _ ≤ ⨆ s : Set.Iic t,
    MeasurableSpace.comap (ContinuousPath.coordinateProcess (alpha := ℂ) s) inferInstance
  exact iSup₂_le fun s hs => le_iSup_of_le (⟨s, hs⟩ : Set.Iic t) le_rfl

/-- The rational inverse clock: for functionals `g q` read at the rational times `q`,
`inf {q ∈ ℚ≥0 | r < g_q ω}` in `[0, ∞]`. -/
noncomputable def rationalClockInverse (g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0) (r : ℝ≥0)
    (ω : ContinuousPath ℂ) : WithTop ℝ≥0 :=
  ⨅ (q : ℚ≥0) (_ : r < g q ω), ((q : ℝ≥0) : WithTop ℝ≥0)

theorem rationalClockInverse_lt_iff {g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0} {r : ℝ≥0}
    {ω : ContinuousPath ℂ} {t : WithTop ℝ≥0} :
    rationalClockInverse g r ω < t ↔ ∃ q : ℚ≥0, r < g q ω ∧ ((q : ℝ≥0) : WithTop ℝ≥0) < t := by
  simp only [rationalClockInverse, iInf_lt_iff, exists_prop]

/-- **The rational inverse clock is an optional time.** If every `g_q` is `F⁰_q`-measurable, then
`{inf {q | r < g_q} < t} = ⋃_{q < t} {r < g_q}` lies in the canonical filtration at time `t`. -/
theorem measurableSet_rationalClockInverse_lt {g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hg : ∀ q : ℚ≥0, Measurable[pathFiltration q] (g q)) (r t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | rationalClockInverse g r ω < t} := by
  have hset : {ω | rationalClockInverse g r ω < t} =
      ⋃ (q : ℚ≥0) (_ : (q : ℝ≥0) < t), {ω | r < g q ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, rationalClockInverse_lt_iff,
      WithTop.coe_lt_coe, exists_prop]
    exact exists_congr fun q => and_comm
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  have hm : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t] (g q) :=
    (hg q).mono ((pathFiltration_le_canonicalFiltration q).trans
      ((ContinuousPath.canonicalFiltration (alpha := ℂ)).mono hq.le)) le_rfl
  exact hm measurableSet_Ioi

/-- **Identification of the rational inverse clock.** Along a path where `g_q = A_q` at every
rational time, the clock is nondecreasing and exceeds `r`, the rational inverse clock at level `r`
is the right inverse `τ_r = inf {t | r < A_t}`. -/
theorem rationalClockInverse_eq_clockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0} {r : ℝ≥0} {ω : ContinuousPath ℂ}
    (hg : ∀ q : ℚ≥0, g q ω = A q ω) (hm : Monotone fun t => A t ω) (hne : ∃ t, r < A t ω) :
    rationalClockInverse g r ω = (clockInverse A r ω : WithTop ℝ≥0) := by
  unfold clockInverse
  have hUne : ({t | r < A t ω} : Set ℝ≥0).Nonempty := hne
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    induction c with
    | top => exact le_top
    | coe c =>
      rw [WithTop.coe_lt_coe] at hc
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal hc
      obtain ⟨u, hu, huq⟩ := exists_lt_of_csInf_lt hUne hq1
      have hq : r < g q ω := by
        rw [hg q]
        exact lt_of_lt_of_le hu (hm huq.le)
      exact (iInf₂_le q hq).trans (WithTop.coe_le_coe.2 hq2.le)
  · refine le_iInf₂ fun q hq => ?_
    rw [hg q] at hq
    exact WithTop.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) hq)

/-- Versions of a PCAF at the rational times, measurable for the natural `σ`-fields. -/
theorem exists_rational_versions {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (z : ℂ) :
    ∃ g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0, (∀ q : ℚ≥0, Measurable[pathFiltration q] (g q)) ∧
      ∀ q : ℚ≥0, A q =ᵐ[planarLaw z] g q :=
  ⟨fun q => (hA.adapted z q).choose, fun q => (hA.adapted z q).choose_spec.1,
    fun q => (hA.adapted z q).choose_spec.2⟩

/-- **The rational inverse clock is a version of `τ`.** For a PCAF with a good clock and versions
`g_q` of `A_q` under `P_z`, almost surely the rational inverse clock equals `τ_r` for every `r`. -/
theorem ae_rationalClockInverse_eq_clockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ)
    {g : ℚ≥0 → ContinuousPath ℂ → ℝ≥0} (hg : ∀ q : ℚ≥0, A q =ᵐ[planarLaw z] g q) :
    ∀ᵐ ω ∂planarLaw z, ∀ r : ℝ≥0,
      rationalClockInverse g r ω = (clockInverse A r ω : WithTop ℝ≥0) := by
  have hall : ∀ᵐ ω ∂planarLaw z, ∀ q : ℚ≥0, g q ω = A q ω := by
    rw [ae_all_iff]
    intro q
    filter_upwards [hg q] with ω h using h.symm
  filter_upwards [hall, hA.path z, hG z] with ω hq hp hgood r
  exact rationalClockInverse_eq_clockInverse hq hp.2.2 (hgood.2.eventually_gt_atTop r).exists

/-- **An optional version of the inverse clock.** For a PCAF with a good clock and a starting
point `z`, there is a family `T_r` of optional times of the canonical filtration with
`T_r = τ_r` for every `r`, `P_z`-almost surely. -/
theorem exists_optionalTime_ae_eq_clockInverse {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) :
    ∃ T : ℝ≥0 → ContinuousPath ℂ → WithTop ℝ≥0,
      (∀ r t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
        {ω | T r ω < t}) ∧
      ∀ᵐ ω ∂planarLaw z, ∀ r : ℝ≥0, T r ω = (clockInverse A r ω : WithTop ℝ≥0) := by
  obtain ⟨g, hgm, hgae⟩ := exists_rational_versions hA z
  exact ⟨rationalClockInverse g, measurableSet_rationalClockInverse_lt hgm,
    ae_rationalClockInverse_eq_clockInverse hA hG z hgae⟩

/-- **The clock at its right inverse.** For a continuous nondecreasing clock from `0` that exceeds
the level `r`, `A_{τ_r} = r`. -/
theorem apply_clockInverse_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {r : ℝ≥0}
    {ω : ContinuousPath ℂ} (h0 : A 0 ω = 0) (hc : Continuous fun t => A t ω)
    (hm : Monotone fun t => A t ω) (hne : ∃ t, r < A t ω) :
    A (clockInverse A r ω) ω = r := by
  unfold clockInverse
  have hUne : ({t | r < A t ω} : Set ℝ≥0).Nonempty := hne
  apply le_antisymm
  · refine not_lt.1 fun hlt => ?_
    have hpos : 0 < sInf {t | r < A t ω} := by
      refine pos_iff_ne_zero.2 fun h => ?_
      rw [h, h0] at hlt
      exact absurd hlt (by simp)
    have hopen : {t | r < A t ω} ∈ 𝓝 (sInf {t | r < A t ω}) :=
      (isOpen_lt continuous_const hc).mem_nhds hlt
    obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hopen ⟨0, hpos⟩
    obtain ⟨t, ht1, ht2⟩ := exists_between hl
    have ht : r < A t ω := hsub ⟨ht1, ht2.le⟩
    exact absurd ht2 (not_lt.2 (csInf_le (OrderBot.bddBelow {t | r < A t ω})
      (show t ∈ {t | r < A t ω} from ht)))
  · have hev : ∀ᶠ t in 𝓝[>] (sInf {t | r < A t ω}), r ≤ A t ω := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      obtain ⟨u, hu, hut⟩ := exists_lt_of_csInf_lt hUne ht
      exact hu.le.trans (hm hut.le)
    exact ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- **Additivity of the inverse clock at `τ_r`** (Revuz–Yor (1999), Proposition V.1.1 for the
time change of a PCAF). For a PCAF of planar Brownian motion with a good clock, every start `z`
and level `r`, almost surely, for every `v`,
`τ_{r+v} = τ_r + τ_v^{Ā} ∘ θ_{τ_r}`, where `Ā` is the rational-time regularization of `A`. -/
theorem ae_clockInverse_add_eq_shift {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) (r : ℝ≥0) :
    ∀ᵐ ω ∂planarLaw z, ∀ v : ℝ≥0,
      clockInverse A (r + v) ω = clockInverse A r ω +
        clockInverse (regularize A) v (ContinuousPath.shift (clockInverse A r ω) ω) := by
  obtain ⟨g, hgm, hgae⟩ := exists_rational_versions hA z
  filter_upwards [hA.path z, hG z, ae_rationalClockInverse_eq_clockInverse hA hG z hgae,
    ae_add_regularize_shift_optionalTime hA z (rationalClockInverse g r)
      (measurableSet_rationalClockInverse_lt hgm r)] with ω hp hgood hTeq hadd v
  have hTr := hTeq r
  have hfin : rationalClockInverse g r ω < ⊤ := by
    rw [hTr]
    exact WithTop.coe_lt_top _
  have hshift := hadd hfin
  rw [hTr, WithTop.untopD_coe] at hshift
  have hAτ : A (clockInverse A r ω) ω = r :=
    apply_clockInverse_eq hp.1 hp.2.1 hp.2.2 (hgood.2.eventually_gt_atTop r).exists
  have key := clockInverse_add_eq_of_shift hp.2.2 hshift
    (hgood.2.eventually_gt_atTop (A (clockInverse A r ω) ω + v)).exists
  rwa [hAτ] at key

/-- **The time-changed path after `τ_r`.** Almost surely, for every `v`,
`B_{τ_{r+v}} = (θ_{τ_r} B)_{τ_v^{Ā} ∘ θ_{τ_r}}`. -/
theorem ae_eval_clockInverse_add_eq_shift {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsPCAF planarLaw A) (hG : GoodClock planarLaw A) (z : ℂ) (r : ℝ≥0) :
    ∀ᵐ ω ∂planarLaw z, ∀ v : ℝ≥0,
      ω (clockInverse A (r + v) ω) =
        ContinuousPath.shift (clockInverse A r ω) ω
          (clockInverse (regularize A) v (ContinuousPath.shift (clockInverse A r ω) ω)) := by
  filter_upwards [ae_clockInverse_add_eq_shift hA hG z r] with ω h v
  rw [h v, ContinuousPath.shift_apply]

end MatedCRT
