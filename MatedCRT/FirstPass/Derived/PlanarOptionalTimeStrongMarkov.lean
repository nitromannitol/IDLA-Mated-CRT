import MatedCRT.FirstPass.Derived.OptionalTimeStrongMarkov
import MatedCRT.FirstPass.Derived.PlanarBrownianPointPolar
import MatedCRT.External.RevuzTimeChange

/-!
# The strong Markov property of planar Brownian motion at optional times

Let `T` be an optional time of the canonical filtration of the planar path (`{T < t} ∈ F⁰_t`
for every `t`), possibly infinite. This file specializes the strong Markov property at optional
times (`continuousProcess_restrict_map_shift_optionalTime_lt_top`) to the planar Brownian laws
`planarLaw z` and derives the two forms used for additive functionals (Revuz–Yor (1999),
Theorem III.3.7; Fukushima–Oshima–Takeda (2011), Section A.2):

* the *transfer of full events*: an event of probability one under every starting point holds
  for the path shifted at `T`, almost surely on `{T < ∞}`;
* the *parameter form*: for a variable `V` of `F_{T+}` and a measurable `H ≥ 0`,
  `E_z[H(V, θ_T ω); T < ∞] = E_z[∫ H(V, ω') dP_{B_T}(ω'); T < ∞]`.

## Main results

* `planarLaw_restrict_map_shift_optionalTime`: the restart form for planar Brownian motion.
* `planarLaw_inter_shift_preimage_optionalTime`: its set form.
* `ae_shift_mem_of_forall_planarLaw_eq_one`: transfer of full events.
* `measurableSet_untopD_preimage_inter_lt`: the time `T` itself is `F_{T+}`-measurable.
* `lintegral_planarLaw_shift_optionalTime_param`: the parameter form for `F_{T+}` variables.
* `lintegral_planarLaw_shift_optionalTime_time`: the parameter form with `V = T`.
-/

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.OptionalTime

open _root_.HarmonicBalls

instance isProbabilityMeasure_planarLaw (z : ℂ) : IsProbabilityMeasure (planarLaw z) := by
  unfold planarLaw
  infer_instance

/-- **Strong Markov property of planar Brownian motion at an optional time, restart form.** -/
theorem planarLaw_restrict_map_shift_optionalTime (z : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    (A : Set (ContinuousPath ℂ))
    (hA : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (A ∩ {ω | T ω < t})) :
    ((planarLaw z).restrict (A ∩ {ω | T ω < ⊤})).map
        (fun ω ↦ ContinuousPath.shift ((T ω).untopD 0) ω) =
      Kernel.comap planarBrownianMotion (fun ω ↦ ω ((T ω).untopD 0))
          (measurable_eval_untopD hT) ∘ₘ
        ((planarLaw z).restrict (A ∩ {ω | T ω < ⊤})) := by
  have h := continuousProcess_restrict_map_shift_optionalTime_lt_top planarHeatSemigroup
    isConservative_planarHeatSemigroup isFellerKernelSemigroup_planarHeatSemigroup
    kolmogorovRegular_planarHeatSemigroup z T hT A hA
  rw [← planarBrownianMotion_eq_continuousProcess] at h
  exact h

/-- **Strong Markov property at an optional time, set form.** For an event `A` of `F_{T+}` and a
measurable path event `G`, `P_z(A, T < ∞, θ_T ω ∈ G) = E_z[P_{B_T}(G); A, T < ∞]`. -/
theorem planarLaw_inter_shift_preimage_optionalTime (z : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    (A : Set (ContinuousPath ℂ))
    (hA : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (A ∩ {ω | T ω < t}))
    {G : Set (ContinuousPath ℂ)} (hG : MeasurableSet G) :
    planarLaw z (A ∩ {ω | T ω < ⊤} ∩
        (fun ω ↦ ContinuousPath.shift ((T ω).untopD 0) ω) ⁻¹' G) =
      ∫⁻ ω in A ∩ {ω | T ω < ⊤}, planarLaw (ω ((T ω).untopD 0)) G ∂planarLaw z := by
  have hshift : Measurable (fun ω : ContinuousPath ℂ ↦ ContinuousPath.shift ((T ω).untopD 0) ω) :=
    ContinuousPath.measurable_shift_of_measurable _ (measurable_untopD hT)
  have h := congrArg (fun m : Measure (ContinuousPath ℂ) => m G)
    (planarLaw_restrict_map_shift_optionalTime z T hT A hA)
  rw [Measure.map_apply hshift hG, Measure.restrict_apply (hshift hG),
    Measure.bind_apply hG (Kernel.aemeasurable _)] at h
  simp only [Kernel.comap_apply] at h
  rw [inter_comm]
  exact h

/-- **Transfer of full events through an optional time.** If a measurable path event `G` has
probability one for planar Brownian motion from every starting point, then almost surely, on
`{T < ∞}`, the path shifted at `T` lies in `G`. -/
theorem ae_shift_mem_of_forall_planarLaw_eq_one (z : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    {G : Set (ContinuousPath ℂ)} (hG : MeasurableSet G) (h1 : ∀ y, planarLaw y G = 1) :
    ∀ᵐ ω ∂planarLaw z, T ω < ⊤ → ContinuousPath.shift ((T ω).untopD 0) ω ∈ G := by
  have hA : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      (univ ∩ {ω | T ω < t}) := fun t => by rw [univ_inter]; exact hT t
  have h := planarLaw_inter_shift_preimage_optionalTime z T hT univ hA hG.compl
  have h0 : ∀ y, planarLaw y Gᶜ = 0 := fun y => (prob_compl_eq_zero_iff hG).2 (h1 y)
  simp only [h0, lintegral_zero] at h
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h
  have hω' : ¬(T ω < ⊤ → ContinuousPath.shift ((T ω).untopD 0) ω ∈ G) := hω
  rw [not_imp] at hω'
  exact ⟨⟨mem_univ _, hω'.1⟩, hω'.2⟩

/-- **The time `T` is `F_{T+}`-measurable**: for every Borel set `B` of times and every `t`,
`{T ∈ B} ∩ {T < t} ∈ F⁰_t` (on `{T < t}`, `T` is finite). -/
theorem measurableSet_untopD_preimage_inter_lt
    {T : ContinuousPath ℂ → WithTop ℝ≥0}
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    {B : Set ℝ≥0} (hB : MeasurableSet B) (t : ℝ≥0) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      ((fun ω => (T ω).untopD 0) ⁻¹' B ∩ {ω | T ω < t}) := by
  set g : ContinuousPath ℂ → ℝ≥0 := fun ω => (min (T ω) (t : WithTop ℝ≥0)).untopD 0 with hg
  have hgm : Measurable[ContinuousPath.canonicalFiltration (alpha := ℂ) t] g := by
    refine measurable_of_Iio fun s => ?_
    have hset : g ⁻¹' Iio s = {ω | T ω < (s : WithTop ℝ≥0)} ∪ {_ω | t < s} := by
      ext ω
      simp only [hg, mem_preimage, mem_Iio, mem_union, mem_ofPred_eq]
      rcases eq_or_ne (T ω) ⊤ with h | h
      · rw [h, min_eq_right le_top, WithTop.untopD_coe]
        exact ⟨Or.inr, fun h' => h'.resolve_left not_top_lt⟩
      · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h
        rw [← ha, ← WithTop.coe_min, WithTop.untopD_coe, WithTop.coe_lt_coe, min_lt_iff]
    rw [hset]
    by_cases hts : t < s
    · simp [hts]
    · have hst : s ≤ t := le_of_not_gt hts
      simp only [hts, ofPred_false, union_empty]
      exact (ContinuousPath.canonicalFiltration (alpha := ℂ)).mono hst _ (hT s)
  have hset : (fun ω => (T ω).untopD 0) ⁻¹' B ∩ {ω | T ω < t} = g ⁻¹' B ∩ {ω | T ω < t} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, and_congr_left_iff]
    intro hlt
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    show (T ω).untopD 0 ∈ B ↔ (min (T ω) (t : WithTop ℝ≥0)).untopD 0 ∈ B
    rw [← ha] at hlt ⊢
    rw [← WithTop.coe_min, min_eq_left (WithTop.coe_lt_coe.1 hlt).le]
  rw [hset]
  exact (hgm hB).inter (hT t)

/-- **Strong Markov property at an optional time, parameter form.** Let `V` be a measurable
variable of `F_{T+}` (`{V ∈ B} ∩ {T < t} ∈ F⁰_t` for every measurable `B` and every `t`) and
`H ≥ 0` measurable on pairs. Then
`E_z[H(V, θ_T ω); T < ∞] = E_z[∫ H(V, ω') dP_{B_T}(ω'); T < ∞]`. -/
theorem lintegral_planarLaw_shift_optionalTime_param {β : Type*} [MeasurableSpace β] (z : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    (V : ContinuousPath ℂ → β) (hVm : Measurable V)
    (hV : ∀ B : Set β, MeasurableSet B → ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t] (V ⁻¹' B ∩ {ω | T ω < t}))
    {H : β × ContinuousPath ℂ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ (ω : ContinuousPath ℂ) in {ω | T ω < ⊤},
        H (V ω, ContinuousPath.shift ((T ω).untopD 0) ω) ∂planarLaw z =
      ∫⁻ (ω : ContinuousPath ℂ) in {ω | T ω < ⊤}, ∫⁻ ω', H (V ω, ω') ∂planarLaw (ω ((T ω).untopD 0))
        ∂planarLaw z := by
  set μ := (planarLaw z).restrict {ω | T ω < ⊤} with hμ
  set s : ContinuousPath ℂ → ContinuousPath ℂ :=
    fun ω ↦ ContinuousPath.shift ((T ω).untopD 0) ω with hs
  have hsm : Measurable s := ContinuousPath.measurable_shift_of_measurable _ (measurable_untopD hT)
  have hpm : Measurable fun ω => (V ω, s ω) := hVm.prodMk hsm
  set κ₀ := Kernel.comap planarBrownianMotion (fun ω : ContinuousPath ℂ ↦ ω ((T ω).untopD 0))
    (measurable_eval_untopD hT) with hκ₀
  set κ := Kernel.deterministic V hVm ×ₖ κ₀ with hκ
  have hκapp : ∀ ω, κ ω = (planarLaw (ω ((T ω).untopD 0))).map (Prod.mk (V ω)) := by
    intro ω
    rw [hκ, Kernel.prod_apply, Kernel.deterministic_apply, Measure.dirac_prod, hκ₀,
      Kernel.comap_apply]
    rfl
  have hsub : ∀ B : Set β, MeasurableSet B → ∀ t : ℝ≥0,
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
        (V ⁻¹' B ∩ {ω | T ω < t}) := hV
  have heq : μ.map (fun ω => (V ω, s ω)) = κ ∘ₘ μ := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨B, hB, G, hG, rfl⟩
      replace hB : MeasurableSet B := hB
      replace hG : MeasurableSet G := hG
      have h1 : ∀ ω, κ ω (B ×ˢ G) =
          (V ⁻¹' B).indicator (fun ω => planarLaw (ω ((T ω).untopD 0)) G) ω := by
        intro ω
        rw [hκ, Kernel.prod_apply, Measure.prod_prod, Kernel.deterministic_apply, hκ₀,
          Kernel.comap_apply, Measure.dirac_apply' _ hB]
        by_cases h : V ω ∈ B <;> simp [h, planarLaw]
      rw [Measure.map_apply hpm (hB.prod hG), Measure.bind_apply (hB.prod hG)
        (Kernel.aemeasurable _)]
      simp_rw [h1]
      rw [lintegral_indicator (hVm hB), hμ, Measure.restrict_restrict (hVm hB),
        Measure.restrict_apply (hpm (hB.prod hG)),
        ← planarLaw_inter_shift_preimage_optionalTime z T hT _ (hsub B hB) hG]
      congr 1
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq, hs]
      tauto
    · rw [Measure.map_apply hpm MeasurableSet.univ,
        Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
      simp [measure_univ]
  rw [← lintegral_map hH hpm, heq, Measure.lintegral_bind (Kernel.aemeasurable _) hH.aemeasurable]
  refine lintegral_congr fun ω => ?_
  rw [hκapp, lintegral_map hH measurable_prodMk_left]

/-- **Strong Markov property at an optional time, parameter form with `V = T`.** -/
theorem lintegral_planarLaw_shift_optionalTime_time (z : ℂ)
    (T : ContinuousPath ℂ → WithTop ℝ≥0)
    (hT : ∀ t : ℝ≥0, MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω | T ω < t})
    {H : ℝ≥0 × ContinuousPath ℂ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ (ω : ContinuousPath ℂ) in {ω | T ω < ⊤},
        H ((T ω).untopD 0, ContinuousPath.shift ((T ω).untopD 0) ω) ∂planarLaw z =
      ∫⁻ (ω : ContinuousPath ℂ) in {ω | T ω < ⊤}, ∫⁻ ω', H ((T ω).untopD 0, ω') ∂planarLaw (ω ((T ω).untopD 0))
        ∂planarLaw z :=
  lintegral_planarLaw_shift_optionalTime_param z T hT _ (measurable_untopD hT)
    (fun _ hB t => measurableSet_untopD_preimage_inter_lt hT hB t) hH

end MatedCRT.OptionalTime
