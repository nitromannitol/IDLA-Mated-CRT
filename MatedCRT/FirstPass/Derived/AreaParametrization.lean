import MatedCRT.Defs.Setting

/-!
# Measurable reconstruction of an area-parametrized curve

A space-filling curve `η` parametrized by the area of a locally finite measure `μ` is the Lebesgue-area
representative `c` composed with the inverse of the clock `u ↦ ±μ(c([0,u]))`. This file proves that the
reconstruction `(μ, c) ↦ η` is a Borel measurable function of the pair (measure, continuous path) and that it
returns `η` on every area-parametrized curve (`areaParam_eq`).
-/

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Filter Topology Metric ProbabilityTheory
open scoped ENNReal

/-- The set of `(c, x)` with `x` in the closed `δ`-thickening of `c([a,b])` is closed. -/
theorem isClosed_cthickening_image (a b δ : ℝ) (hδ : 0 ≤ δ) :
    IsClosed {q : C(ℝ, ℂ) × ℂ | q.2 ∈ cthickening δ (q.1 '' Icc a b)} := by
  have hset : {q : C(ℝ, ℂ) × ℂ | q.2 ∈ cthickening δ (q.1 '' Icc a b)} =
      Prod.snd '' {r : Icc a b × (C(ℝ, ℂ) × ℂ) | dist r.2.2 (r.2.1 r.1) ≤ δ} := by
    ext ⟨c, x⟩
    constructor
    · intro h
      change x ∈ cthickening δ (c '' Icc a b) at h
      rw [(isCompact_Icc.image c.continuous).cthickening_eq_biUnion_closedBall hδ] at h
      simp only [mem_iUnion, mem_closedBall, exists_prop] at h
      obtain ⟨y, ⟨s, hs, rfl⟩, hy⟩ := h
      exact ⟨(⟨s, hs⟩, (c, x)), hy, rfl⟩
    · rintro ⟨⟨⟨s, hs⟩, c', x'⟩, hd, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      change x' ∈ cthickening δ (c' '' Icc a b)
      rw [(isCompact_Icc.image c'.continuous).cthickening_eq_biUnion_closedBall hδ]
      simp only [mem_iUnion, mem_closedBall, exists_prop]
      exact ⟨c' s, ⟨s, hs, rfl⟩, hd⟩
  rw [hset]
  refine (isClosedMap_snd_of_compactSpace _) ?_
  exact isClosed_le (by fun_prop) continuous_const

/-- Truncation of a measure to the closed ball of radius `n`, set to `0` when that mass is infinite; always a
finite measure, and equal to `μ.restrict (closedBall 0 n)` for a locally finite `μ`. -/
noncomputable def truncMeasure (n : ℕ) (μ : Measure ℂ) : Measure ℂ :=
  open scoped Classical in
  if μ (closedBall (0 : ℂ) n) < ∞ then μ.restrict (closedBall (0 : ℂ) n) else 0

theorem measurable_truncMeasure (n : ℕ) : Measurable (truncMeasure n) := by
  classical
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have h : (fun μ : Measure ℂ => truncMeasure n μ s) =
      fun μ : Measure ℂ => if μ (closedBall (0 : ℂ) n) < ∞ then μ (s ∩ closedBall (0 : ℂ) n) else 0 := by
    funext μ
    unfold truncMeasure
    split_ifs with h1
    · rw [Measure.restrict_apply hs]
    · simp
  rw [h]
  refine Measurable.ite ?_ (Measure.measurable_coe (hs.inter measurableSet_closedBall)) measurable_const
  exact measurableSet_lt (Measure.measurable_coe measurableSet_closedBall) measurable_const

theorem isFiniteMeasure_truncMeasure (n : ℕ) (μ : Measure ℂ) : IsFiniteMeasure (truncMeasure n μ) := by
  classical
  unfold truncMeasure
  split_ifs with h
  · exact ⟨by rw [Measure.restrict_apply_univ]; exact h⟩
  · infer_instance

theorem truncMeasure_eq (n : ℕ) (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] :
    truncMeasure n μ = μ.restrict (closedBall (0 : ℂ) n) := by
  classical
  unfold truncMeasure
  simp [measure_closedBall_lt_top]

theorem measurable_truncMass (n : ℕ) (a b δ : ℝ) (hδ : 0 ≤ δ) :
    Measurable fun p : Measure ℂ × C(ℝ, ℂ) => truncMeasure n p.1 (cthickening δ (p.2 '' Icc a b)) := by
  let κ : Kernel (Measure ℂ × C(ℝ, ℂ)) ℂ :=
    ⟨fun p => truncMeasure n p.1, (measurable_truncMeasure n).comp measurable_fst⟩
  have hfin : ∀ p, IsFiniteMeasure (κ p) := fun p => isFiniteMeasure_truncMeasure n p.1
  have hC : MeasurableSet {q : C(ℝ, ℂ) × ℂ | q.2 ∈ cthickening δ (q.1 '' Icc a b)} :=
    (isClosed_cthickening_image a b δ hδ).measurableSet
  have hg : Measurable fun z : (Measure ℂ × C(ℝ, ℂ)) × ℂ => (z.1.2, z.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hS : MeasurableSet {z : (Measure ℂ × C(ℝ, ℂ)) × ℂ | z.2 ∈ cthickening δ (z.1.2 '' Icc a b)} :=
    hg hC
  exact Kernel.measurable_kernel_prodMk_left_of_finite hS hfin

/-- A Borel measurable surrogate for `μ (c '' Icc a b)`, equal to it for locally finite `μ`
(`imageMass_eq`): the infimum over `k` of the mass of the closed `1/(k+1)`-thickening. -/
noncomputable def imageMass (μ : Measure ℂ) (c : C(ℝ, ℂ)) (a b : ℝ) : ℝ≥0∞ :=
  ⨅ k : ℕ, ⨆ n : ℕ, truncMeasure n μ (cthickening (1 / ((k : ℝ) + 1)) (c '' Icc a b))

theorem measurable_imageMass (a b : ℝ) :
    Measurable fun p : Measure ℂ × C(ℝ, ℂ) => imageMass p.1 p.2 a b := by
  refine Measurable.iInf fun k => Measurable.iSup fun n => ?_
  exact measurable_truncMass n a b _ (by positivity)

theorem imageMass_eq (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (c : C(ℝ, ℂ)) (a b : ℝ) :
    imageMass μ c a b = μ (c '' Icc a b) := by
  have hK : IsCompact (c '' Icc a b) := isCompact_Icc.image c.continuous
  have hsup : ∀ r : ℝ, ⨆ n : ℕ, truncMeasure n μ (cthickening r (c '' Icc a b)) =
      μ (cthickening r (c '' Icc a b)) := by
    intro r
    have hcl : MeasurableSet (cthickening r (c '' Icc a b)) := isClosed_cthickening.measurableSet
    simp_rw [truncMeasure_eq, Measure.restrict_apply hcl]
    have hmo : Monotone fun n : ℕ => cthickening r (c '' Icc a b) ∩ closedBall (0 : ℂ) n := by
      intro i j hij
      exact inter_subset_inter_right _ (closedBall_subset_closedBall (by exact_mod_cast hij))
    rw [← hmo.measure_iUnion, ← inter_iUnion, iUnion_closedBall_nat, inter_univ]
  unfold imageMass
  simp_rw [hsup]
  have hmono : Antitone fun k : ℕ => μ (cthickening (1 / ((k : ℝ) + 1)) (c '' Icc a b)) := by
    intro i j hij
    apply measure_mono
    apply cthickening_mono
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have h1 := (tendsto_measure_cthickening_of_isCompact (μ := μ) hK).comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_nhds_unique (tendsto_atTop_iInf hmono) h1

/-- `t ≤ clock μ c u`, for the signed clock `u ↦ μ(c [0,u])` (`u ≥ 0`), `u ↦ -μ(c [u,0])` (`u < 0`) of the
path `c` under the measure `μ`. -/
def ClockLE (μ : Measure ℂ) (c : C(ℝ, ℂ)) (t u : ℝ) : Prop :=
  (0 ≤ u → ENNReal.ofReal t ≤ imageMass μ c 0 u) ∧
  (u < 0 → t ≤ 0 ∧ imageMass μ c u 0 ≤ ENNReal.ofReal (-t))

theorem measurableSet_clockLE (t u : ℝ) :
    MeasurableSet {p : Measure ℂ × C(ℝ, ℂ) | ClockLE p.1 p.2 t u} := by
  by_cases hu : 0 ≤ u
  · have h : {p : Measure ℂ × C(ℝ, ℂ) | ClockLE p.1 p.2 t u} =
        {p | ENNReal.ofReal t ≤ imageMass p.1 p.2 0 u} := by
      ext p
      simp [ClockLE, hu, not_lt.2 hu]
    rw [h]
    exact measurableSet_le measurable_const (measurable_imageMass 0 u)
  · have hu' : u < 0 := not_le.1 hu
    have h : {p : Measure ℂ × C(ℝ, ℂ) | ClockLE p.1 p.2 t u} =
        {_p : Measure ℂ × C(ℝ, ℂ) | t ≤ 0} ∩ {p | imageMass p.1 p.2 u 0 ≤ ENNReal.ofReal (-t)} := by
      ext p
      simp [ClockLE, hu, hu']
    rw [h]
    exact (MeasurableSet.const _).inter (measurableSet_le (measurable_imageMass u 0) measurable_const)

/-- The area-parametrization time `u` with `clock u = t`, defined as the infimum over rational `q` with
`t ≤ clock q` (`0` when this infimum is infinite). -/
noncomputable def areaParamTime (μ : Measure ℂ) (c : C(ℝ, ℂ)) (t : ℝ) : ℝ :=
  open scoped Classical in
  (⨅ q : ℚ, if ClockLE μ c t q then (((q : ℝ)) : EReal) else ⊤).toReal

/-- The curve `t ↦ c (φ_{μ,c}(t))` obtained from the Lebesgue representative `c` and the measure `μ` by the
area parametrization. -/
noncomputable def areaParam (μ : Measure ℂ) (c : C(ℝ, ℂ)) (t : ℝ) : ℂ :=
  c (areaParamTime μ c t)

theorem measurable_areaParamTime (t : ℝ) :
    Measurable fun p : Measure ℂ × C(ℝ, ℂ) => areaParamTime p.1 p.2 t := by
  classical
  unfold areaParamTime
  refine measurable_ereal_toReal.comp ?_
  refine Measurable.iInf fun q => ?_
  exact Measurable.ite (measurableSet_clockLE t q) measurable_const measurable_const

theorem measurable_areaParam (t : ℝ) :
    Measurable fun p : Measure ℂ × C(ℝ, ℂ) => areaParam p.1 p.2 t := by
  have hev : Continuous fun q : C(ℝ, ℂ) × ℝ => q.1 q.2 := continuous_eval
  exact hev.measurable.comp (measurable_snd.prodMk (measurable_areaParamTime t))

theorem iInf_rat_ite_ereal (a : ℝ) :
    (⨅ q : ℚ, open scoped Classical in if a ≤ (q : ℝ) then (((q : ℝ)) : EReal) else ⊤) = (a : EReal) := by
  classical
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun x hx => ?_
    induction x using EReal.rec with
    | bot => exact absurd hx (not_lt_of_ge bot_le)
    | top =>
      obtain ⟨q, hq⟩ := exists_rat_gt a
      exact (iInf_le _ q).trans (by simp [hq.le])
    | coe r =>
      have hr : a < r := EReal.coe_lt_coe_iff.1 hx
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr
      refine (iInf_le _ q).trans ?_
      simp only [hq1.le, ite_true]
      exact EReal.coe_le_coe_iff.2 hq2.le
  · refine le_iInf fun q => ?_
    by_cases h : a ≤ (q : ℝ)
    · simp only [h, ite_true]
      exact EReal.coe_le_coe_iff.2 h
    · simp [h]

theorem areaParamTime_eq_of_clock {μ : Measure ℂ} {c : C(ℝ, ℂ)} {t : ℝ} (φ : ℝ ≃o ℝ)
    (hclock : ∀ u : ℝ, ClockLE μ c t u ↔ φ t ≤ u) : areaParamTime μ c t = φ t := by
  classical
  unfold areaParamTime
  have h : (fun q : ℚ => if ClockLE μ c t q then (((q : ℝ)) : EReal) else ⊤) =
      fun q : ℚ => if φ t ≤ (q : ℝ) then (((q : ℝ)) : EReal) else ⊤ := by
    funext q
    simp only [hclock]
  simp_rw [iInf, h]
  have h2 := iInf_rat_ite_ereal (φ t)
  simp only [iInf] at h2
  rw [h2]
  rfl

/-- A curve parametrized by the area of a locally finite measure has no mass on a point. -/
theorem measure_image_Icc_self_eq_zero {μ : Measure ℂ} {η : ℝ → ℂ} (hη : IsAreaParametrized μ η) (a : ℝ) :
    μ (η '' Icc a a) = 0 := by
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa using this
  refine le_antisymm (ge_of_tendsto' hlim fun n => ?_) bot_le
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  calc μ (η '' Icc a a) ≤ μ (η '' Icc a (a + 1 / ((n : ℝ) + 1))) :=
        measure_mono (image_mono (Icc_subset_Icc_right (by linarith)))
    _ = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
        rw [hη.2.2.2 a _ (by linarith)]
        congr 1
        ring

/-- **The area parametrization is a measurable function of the pair (measure, Lebesgue representative).**
If `η` is parametrized by the area of the locally finite measure `μ`, and `η = c ∘ φ` for a continuous path `c`
and an order isomorphism `φ` of `ℝ` fixing `0`, then `η t = areaParam μ c t` for every `t`. -/
theorem areaParam_eq {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {η : ℝ → ℂ} {c : C(ℝ, ℂ)}
    (hη : IsAreaParametrized μ η) (φ : ℝ ≃o ℝ) (hφ0 : φ 0 = 0) (hηc : ∀ t, η t = c (φ t)) (t : ℝ) :
    areaParam μ c t = η t := by
  have hcomp : η = c ∘ φ := funext hηc
  have himg : ∀ a b : ℝ, η '' Icc a b = c '' Icc (φ a) (φ b) := by
    intro a b
    rw [hcomp, image_comp, OrderIso.image_Icc]
  have hmass : ∀ a b : ℝ, a ≤ b → μ (c '' Icc (φ a) (φ b)) = ENNReal.ofReal (b - a) := by
    intro a b hab
    rw [← himg]
    rcases hab.eq_or_lt with rfl | hlt
    · rw [measure_image_Icc_self_eq_zero hη, sub_self, ENNReal.ofReal_zero]
    · exact hη.2.2.2 a b hlt
  have hs0 : φ.symm 0 = 0 := by
    rw [OrderIso.symm_apply_eq]
    exact hφ0.symm
  have key : ∀ u : ℝ, ClockLE μ c t u ↔ φ t ≤ u := by
    intro u
    rw [← φ.le_symm_apply]
    unfold ClockLE
    have hu' : φ (φ.symm u) = u := φ.apply_symm_apply u
    by_cases hu : 0 ≤ u
    · have hs : 0 ≤ φ.symm u := by simpa [hs0] using φ.symm.monotone hu
      have hm : imageMass μ c 0 u = ENNReal.ofReal (φ.symm u) := by
        rw [imageMass_eq]
        have := hmass 0 (φ.symm u) hs
        rwa [hφ0, hu', sub_zero] at this
      constructor
      · intro h
        have h1 := h.1 hu
        rw [hm] at h1
        exact (ENNReal.ofReal_le_ofReal_iff hs).1 h1
      · intro h
        exact ⟨fun _ => by rw [hm]; exact ENNReal.ofReal_le_ofReal h, fun hlt => absurd hlt (not_lt.2 hu)⟩
    · have hlt : u < 0 := not_le.1 hu
      have hs : φ.symm u < 0 := by
        have := φ.symm.strictMono hlt
        rwa [hs0] at this
      have hm : imageMass μ c u 0 = ENNReal.ofReal (-φ.symm u) := by
        rw [imageMass_eq]
        have := hmass (φ.symm u) 0 hs.le
        rwa [hφ0, hu', zero_sub] at this
      constructor
      · intro h
        obtain ⟨ht, h2⟩ := h.2 hlt
        rw [hm] at h2
        have := (ENNReal.ofReal_le_ofReal_iff (neg_nonneg.2 ht)).1 h2
        linarith
      · intro h
        exact ⟨fun h0 => absurd h0 hu, fun _ => ⟨by linarith, by
          rw [hm]; exact ENNReal.ofReal_le_ofReal (by linarith)⟩⟩
  unfold areaParam
  rw [areaParamTime_eq_of_clock φ key, hηc]

end MatedCRT.FirstPass.Derived
