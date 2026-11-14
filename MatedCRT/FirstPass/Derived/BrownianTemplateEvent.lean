import MatedCRT.FirstPass.Derived.BrownianTubeTemplate

/-!
# The template tube at an exit time

Steps (A4) and (A5) of the Brownian disconnection estimate behind the invariance principle of
Gwynne-Miller-Sheffield (Lemma 3.14 (a)).

For a radius `r`, the event `exitTemplateTube r` asks that, after its exit time `τ_r` from the
open disc of radius `r` about `0`, the path follows the polar template moved to radius `r` and to
the angle of its exit point, within distance `r / 2000`, for a time `r²`.

* (A4) `exitTemplateTube_subset_templatePieceEvent`: for `r ≤ 1/4` this event lies in the
  template-piece event `templatePieceEvent r`: a piece of the path, linearly normalized to the
  unit interval, has Fréchet distance less than `r / 2000` from the moved template, and the path
  stays in the disc of radius `1/2` until the piece ends.
* (A5) `measurableSet_exitTemplateTube`: the event is measurable for the stopped σ-algebra at the
  exit time of every disc of radius `R ≥ 11r/10 + r/2000`, because on it the larger disc is left
  only after `τ_r + r²`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric MarkovProcess
open scoped ENNReal NNReal
open MatedCRTHarmonic.CellularEmbedding

namespace MatedCRT

/-- Linear time on `[a, b]`, read from the unit interval. -/
noncomputable def segmentTime (a b : ℝ≥0) (s : unitInterval) : ℝ≥0 :=
  a + Real.toNNReal s * (b - a)

/-- **Template-piece event at scale `r`.** Some piece `f|[a,b]` of the path, linearly normalized
to the unit interval, follows the polar template moved to radius `r` and some angle `ϑ` up to an
increasing reparametrization `φ` of the unit interval, within distance `r / 2000` (Fréchet distance
less than `r / 2000`), and the path stays in the disc of radius `1/2` up to time `b`. -/
def templatePieceEvent (r : ℝ) : Set (ContinuousPath ℂ) :=
  {f | ∃ ϑ : ℝ, ∃ a b : ℝ≥0, a < b ∧ (∀ t ≤ b, ‖f t‖ < 1 / 2) ∧
    ∃ φ : MatedCRTHarmonic.Topology.IncreasingParametrization, ∀ s : unitInterval,
      ‖f (segmentTime a b s) - movedTemplate 0 r ϑ (φ s)‖ < r / 2000}

/-- The template tube from the start point: for a time `r²` the path stays within `r / 2000` of
the polar template moved to radius `r` and to the angle of its start point. -/
def templateTube (r : ℝ≥0) : Set (ContinuousPath ℂ) :=
  {ω | ∀ t ≤ r ^ 2,
    ‖ω t - movedTemplate 0 r (Complex.arg (ω 0)) ((t : ℝ) / (r : ℝ) ^ 2)‖ < r / 2000}

/-- Exit time of the open disc of radius `r` about `0`, read in `WithTop ℝ≥0`. -/
noncomputable def discExitTime (r : ℝ) (ω : ContinuousPath ℂ) : WithTop ℝ≥0 :=
  ContinuousPath.exitTimeTop (ball (0 : ℂ) r) ω

theorem isStoppingTime_discExitTime (r : ℝ) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := ℂ)) (discExitTime r) :=
  ContinuousPath.isStoppingTime_exitTime _ isOpen_ball

/-- **The template tube at the exit time** `τ_r` of the disc of radius `r`: `τ_r` is finite and
the path shifted by `τ_r` lies in `templateTube r`. -/
def exitTemplateTube (r : ℝ≥0) : Set (ContinuousPath ℂ) :=
  {ω | discExitTime r ω < ⊤ ∧
    ContinuousPath.shift ((discExitTime r ω).untopD 0) ω ∈ templateTube r}

theorem mem_exitTemplateTube_iff {r : ℝ≥0} {ω : ContinuousPath ℂ} :
    ω ∈ exitTemplateTube r ↔ ∃ a : ℝ≥0, discExitTime r ω = a ∧
      ∀ t ≤ r ^ 2, ‖ω (a + t) - movedTemplate 0 r (Complex.arg (ω a)) ((t : ℝ) / (r : ℝ) ^ 2)‖ <
        r / 2000 := by
  constructor
  · rintro ⟨hlt, h⟩
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hlt.ne
    refine ⟨a, ha.symm, fun t ht => ?_⟩
    have h' := h t ht
    rw [← ha, WithTop.untopD_coe] at h'
    simpa only [ContinuousPath.shift_apply, add_zero] using h'
  · rintro ⟨a, ha, h⟩
    refine ⟨by rw [ha]; exact WithTop.coe_lt_top a, ?_⟩
    rw [ha, WithTop.untopD_coe]
    intro t ht
    simpa only [ContinuousPath.shift_apply, add_zero] using h t ht

/-- Norm of the moved polar template. -/
theorem norm_movedTemplate_le {r : ℝ} (hr : 0 ≤ r) (ϑ s : ℝ) :
    ‖movedTemplate 0 r ϑ s‖ ≤ 11 / 10 * r := by
  simpa only [sub_zero] using
    (MatedCRTHarmonic.CellFamily.waypointProof_movedTemplate_norm_bounds 0 hr ϑ s).2

/-- On the template tube at the exit time, the path stays in the disc of radius
`11r/10 + r/2000` up to time `τ_r + r²`. -/
theorem norm_lt_of_mem_exitTemplateTube {r : ℝ≥0} {ω : ContinuousPath ℂ}
    (hω : ω ∈ exitTemplateTube r) {a : ℝ≥0} (ha : discExitTime r ω = a) {t : ℝ≥0}
    (ht : t ≤ a + r ^ 2) : ‖ω t‖ < 11 / 10 * (r : ℝ) + r / 2000 := by
  obtain ⟨a', ha', htube⟩ := mem_exitTemplateTube_iff.mp hω
  have haa : a' = a := WithTop.coe_injective (ha'.symm.trans ha)
  subst haa
  have hr0 : (0 : ℝ) ≤ r := r.2
  rcases lt_or_ge t a' with hta | hat
  · have hlt : ((t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime (ball (0 : ℂ) r) ω := by
      have h1 : ContinuousPath.exitTime (ball (0 : ℂ) r) ω = (a' : ℝ≥0∞) := ha'
      rw [h1]
      exact ENNReal.coe_lt_coe.mpr hta
    have hmem := ContinuousPath.mem_of_lt_exitTime (ball (0 : ℂ) r) ω t hlt
    rw [mem_ball_zero_iff] at hmem
    linarith
  · obtain ⟨u, rfl⟩ : ∃ u, t = a' + u := ⟨t - a', (add_tsub_cancel_of_le hat).symm⟩
    have hu : u ≤ r ^ 2 := (add_le_add_iff_left a').mp ht
    have h1 := htube u hu
    have h2 := norm_movedTemplate_le hr0 (Complex.arg (ω a')) ((u : ℝ) / (r : ℝ) ^ 2)
    have h3 := norm_le_norm_sub_add (ω (a' + u))
      (movedTemplate 0 r (Complex.arg (ω a')) ((u : ℝ) / (r : ℝ) ^ 2))
    linarith

/-- **(A4) Tube at the exit time implies the template-piece event**, for `0 < r ≤ 1/4`, with the
piece `[τ_r, τ_r + r²]`, the linear reparametrization and the angle of the exit point. -/
theorem exitTemplateTube_subset_templatePieceEvent {r : ℝ≥0} (hr0 : 0 < r)
    (hr : (r : ℝ) ≤ 1 / 4) : exitTemplateTube r ⊆ templatePieceEvent r := by
  intro ω hω
  obtain ⟨a, ha, htube⟩ := mem_exitTemplateTube_iff.mp hω
  have hr' : (0 : ℝ) < r := hr0
  refine ⟨Complex.arg (ω a), a, a + r ^ 2, lt_add_of_pos_right a (pow_pos hr0 2), ?_,
    OrderIso.refl _, ?_⟩
  · intro t ht
    have h := norm_lt_of_mem_exitTemplateTube hω ha ht
    linarith
  · intro s
    have hs0 : (0 : ℝ) ≤ s := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hseg : segmentTime a (a + r ^ 2) s = a + Real.toNNReal s * r ^ 2 := by
      rw [segmentTime, add_tsub_cancel_left]
    have hle : Real.toNNReal s * r ^ 2 ≤ r ^ 2 := by
      have : Real.toNNReal s ≤ 1 := Real.toNNReal_le_one.mpr hs1
      calc Real.toNNReal s * r ^ 2 ≤ 1 * r ^ 2 := mul_le_mul_of_nonneg_right this zero_le
        _ = r ^ 2 := one_mul _
    have hdiv : (((Real.toNNReal s * r ^ 2 : ℝ≥0) : ℝ)) / (r : ℝ) ^ 2 = s := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ hs0, NNReal.coe_pow]
      field_simp
    have h := htube _ hle
    rw [hdiv] at h
    rw [hseg, OrderIso.refl_apply]
    exact h

/-- Adding a constant to a `WithTop ℝ≥0`-valued stopping time gives a stopping time. -/
theorem isStoppingTime_add_const_nnreal {Ω : Type*} {m : MeasurableSpace Ω}
    {f : Filtration ℝ≥0 m} {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime f τ) (s : ℝ≥0) :
    IsStoppingTime f fun ω => τ ω + s := by
  intro t
  by_cases hst : s ≤ t
  · have hset : {ω | τ ω + (s : WithTop ℝ≥0) ≤ t} = {ω | τ ω ≤ ((t - s : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq]
      cases τ ω with
      | top => simp only [WithTop.top_add, top_le_iff, WithTop.coe_ne_top]
      | coe a =>
        rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
        exact (le_tsub_iff_right hst).symm
    rw [hset]
    exact f.mono tsub_le_self _ (hτ (t - s))
  · have hset : {ω | τ ω + (s : WithTop ℝ≥0) ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      calc (t : WithTop ℝ≥0) < s := WithTop.coe_lt_coe.mpr (not_le.mp hst)
        _ ≤ τ ω + s := le_add_self
    rw [hset]
    exact @MeasurableSet.empty _ (f t)

/-- **Continuous tube conditions are measurable** for any σ-algebra in which each `Φ t`, `t ≤ T`,
is measurable, when `t ↦ Φ t ω` is continuous for every `ω`. -/
theorem measurableSet_forall_le_lt_of_continuous {Ω : Type*} (m : MeasurableSpace Ω) (T : ℝ≥0)
    (Φ : ℝ≥0 → Ω → ℝ) (hΦm : ∀ t ≤ T, Measurable[m] (Φ t))
    (hΦc : ∀ ω, Continuous fun t => Φ t ω) (c : ℝ) :
    MeasurableSet[m] {ω | ∀ t ≤ T, Φ t ω < c} := by
  have hset : {ω : Ω | ∀ t ≤ T, Φ t ω < c} =
      ⋃ k : ℕ, ⋂ q : ℚ, {ω | Φ (min (Real.toNNReal q) T) ω ≤ c - 1 / ((k : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    constructor
    · intro h
      obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).exists_isMaxOn
        (nonempty_Icc.mpr zero_le) (hΦc ω).continuousOn
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr (h t₀ ht₀.2))
      refine ⟨k, fun q => ?_⟩
      have h1 : Φ (min (Real.toNNReal q) T) ω ≤ Φ t₀ ω :=
        hmax ⟨zero_le, min_le_right _ _⟩
      linarith
    · rintro ⟨k, hk⟩ t ht
      have hcont : Continuous fun x : ℝ => Φ (min (Real.toNNReal x) T) ω :=
        (hΦc ω).comp (continuous_real_toNNReal.min continuous_const)
      have hcl : IsClosed {x : ℝ | Φ (min (Real.toNNReal x) T) ω ≤ c - 1 / ((k : ℝ) + 1)} :=
        isClosed_le hcont continuous_const
      have hsub : closure (range (Rat.cast : ℚ → ℝ)) ⊆
          {x : ℝ | Φ (min (Real.toNNReal x) T) ω ≤ c - 1 / ((k : ℝ) + 1)} :=
        hcl.closure_subset_iff.mpr (by rintro _ ⟨q, rfl⟩; exact hk q)
      have hx := hsub (by rw [Rat.denseRange_cast.closure_range]; trivial : (t : ℝ) ∈ _)
      have hle : Φ t ω ≤ c - 1 / ((k : ℝ) + 1) := by
        simpa only [mem_ofPred_eq, Real.toNNReal_coe, min_eq_left ht] using hx
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hset]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iInter fun q => ?_
  exact hΦm _ (min_le_right _ _) measurableSet_Iic

theorem continuous_movedTemplate_left (z : ℂ) (r s : ℝ) :
    Continuous fun ϑ : ℝ => movedTemplate z r ϑ s := by
  unfold movedTemplate
  fun_prop

theorem continuous_movedTemplate_right (z : ℂ) (r ϑ : ℝ) :
    Continuous fun s : ℝ => movedTemplate z r ϑ s := by
  unfold movedTemplate
  exact continuous_const.add (continuous_const.mul
    ((MatedCRTHarmonic.Topology.polarTemplate).continuous.comp continuous_projIcc))

/-- **(A5) The template tube at `τ_r` is measurable at a later exit time.** If
`11r/10 + r/2000 ≤ R`, the event `exitTemplateTube r` is measurable for the stopped σ-algebra at
the exit time of the disc of radius `R`. -/
theorem measurableSet_exitTemplateTube {r R : ℝ≥0}
    (hR : 11 / 10 * (r : ℝ) + r / 2000 ≤ R) :
    MeasurableSet[(isStoppingTime_discExitTime R).measurableSpace] (exitTemplateTube r) := by
  set τ := discExitTime r with hτdef
  have hτ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := ℂ)) τ :=
    isStoppingTime_discExitTime r
  have hτR := isStoppingTime_discExitTime R
  have hadd : ∀ s : ℝ≥0, IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := ℂ))
      fun ω => τ ω + s := fun s => isStoppingTime_add_const_nnreal hτ s
  have hσ := hadd (r ^ 2)
  have hmono : ∀ s ≤ r ^ 2, (hadd s).measurableSpace ≤ hσ.measurableSpace := fun s hs =>
    (hadd s).measurableSpace_mono hσ fun ω => add_le_add le_rfl (WithTop.coe_le_coe.mpr hs)
  have hτσ : hτ.measurableSpace ≤ hσ.measurableSpace :=
    hτ.measurableSpace_mono hσ fun ω => le_self_add
  -- the tube functional
  let Φ : ℝ≥0 → ContinuousPath ℂ → ℝ := fun t ω =>
    ‖ω ((τ ω + t).untopD 0) - movedTemplate 0 r (Complex.arg (ω ((τ ω).untopD 0)))
      ((t : ℝ) / (r : ℝ) ^ 2)‖
  have hΦm : ∀ t ≤ r ^ 2, Measurable[hσ.measurableSpace] (Φ t) := by
    intro t ht
    have h1 : Measurable[hσ.measurableSpace] fun ω : ContinuousPath ℂ => ω ((τ ω + t).untopD 0) :=
      (ContinuousPath.measurable_eval_untopD_stoppingTime_stopped _ (hadd t)).mono
        (hmono t ht) le_rfl
    have h2 : Measurable[hσ.measurableSpace] fun ω : ContinuousPath ℂ => ω ((τ ω).untopD 0) :=
      (ContinuousPath.measurable_eval_untopD_stoppingTime_stopped _ hτ).mono hτσ le_rfl
    have h3 : Measurable[hσ.measurableSpace] fun ω : ContinuousPath ℂ =>
        movedTemplate 0 r (Complex.arg (ω ((τ ω).untopD 0))) ((t : ℝ) / (r : ℝ) ^ 2) :=
      (continuous_movedTemplate_left 0 r _).measurable.comp (Complex.measurable_arg.comp h2)
    exact (continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable.comp
      (h1.prodMk h3)
  have hΦc : ∀ ω, Continuous fun t => Φ t ω := by
    intro ω
    have hT : ∀ y : ℂ, Continuous fun t : ℝ≥0 =>
        movedTemplate 0 r (Complex.arg y) ((t : ℝ) / (r : ℝ) ^ 2) := fun y =>
      (continuous_movedTemplate_right 0 r _).comp (NNReal.continuous_coe.div_const _)
    cases hω : τ ω with
    | top =>
      simp only [Φ, hω, WithTop.top_add, WithTop.untopD_top]
      exact (continuous_const.sub (hT _)).norm
    | coe a =>
      simp only [Φ, hω, ← WithTop.coe_add, WithTop.untopD_coe]
      exact ((ω.continuous.comp (show Continuous fun t : ℝ≥0 => a + t from
        continuous_const.add continuous_id)).sub (hT _)).norm
  have hset : exitTemplateTube r = {ω | τ ω < ⊤} ∩ {ω | ∀ t ≤ r ^ 2, Φ t ω < r / 2000} := by
    ext ω
    rw [mem_exitTemplateTube_iff]
    constructor
    · rintro ⟨a, ha, h⟩
      refine ⟨by simp only [mem_ofPred_eq, hτdef, ha]; exact WithTop.coe_lt_top a, fun t ht => ?_⟩
      simp only [Φ, hτdef, ha, ← WithTop.coe_add, WithTop.untopD_coe]
      exact h t ht
    · rintro ⟨hlt, h⟩
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (show τ ω < ⊤ from hlt))
      refine ⟨a, ha.symm, fun t ht => ?_⟩
      have h' := h t ht
      have ha' : discExitTime r ω = a := ha.symm
      simp only [Φ, hτdef, ha', ← WithTop.coe_add, WithTop.untopD_coe] at h'
      exact h'
  have hG : MeasurableSet[hσ.measurableSpace] (exitTemplateTube r) := by
    rw [hset]
    exact (hτσ _ (MarkovProcess.StoppingTime.measurableSet_stoppingTime_lt_top hτ)).inter
      (measurableSet_forall_le_lt_of_continuous _ _ Φ hΦm hΦc _)
  -- on the event, the larger disc is left only after `τ_r + r²`
  have hsub : exitTemplateTube r ⊆ {ω | τ ω + ((r ^ 2 : ℝ≥0) : WithTop ℝ≥0) ≤ discExitTime R ω} := by
    intro ω hω
    obtain ⟨a, ha, -⟩ := mem_exitTemplateTube_iff.mp hω
    simp only [mem_ofPred_eq, hτdef, ha, ← WithTop.coe_add]
    show ((a + r ^ 2 : ℝ≥0) : ℝ≥0∞) ≤ ContinuousPath.exitTime (ball (0 : ℂ) R) ω
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨e, he⟩ : ∃ e : ℝ≥0, ContinuousPath.exitTime (ball (0 : ℂ) R) ω = e :=
      ⟨_, (ENNReal.coe_toNNReal (ne_top_of_lt hlt)).symm⟩
    rw [he, ENNReal.coe_lt_coe] at hlt
    -- the path meets the complement of the open disc of radius `R` by time `e < τ_r + r²`
    obtain ⟨⟨u, hu⟩, hout⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy (ball (0 : ℂ) R)
      isOpen_ball e ω).mp (le_of_eq he)
    have hnorm := norm_lt_of_mem_exitTemplateTube hω ha (le_of_lt (lt_of_le_of_lt hu hlt))
    exact hout (mem_ball_zero_iff.mpr (by linarith))
  have h := (hσ.measurableSet_inter_le hτR _ hG)
  rw [inter_eq_left.mpr hsub] at h
  exact (hσ.min hτR).measurableSpace_mono hτR (fun ω => min_le_right _ _) _ h

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.exitTemplateTube_subset_templatePieceEvent
#print axioms MatedCRT.measurableSet_exitTemplateTube
