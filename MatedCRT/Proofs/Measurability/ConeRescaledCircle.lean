import MatedCRT.Steps.Sec2.ConeScaleInvarianceUpToFixedTime
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.ContinuousFieldMeasurable

/-!
# The rescaled cone field is a random variable (`ConeRescaledCircleAEMeasurableStep`)

`ConeRescaledCircleAEMeasurableStep` (MatedCRT/Steps/Sec2/ConeScaleInvarianceUpToFixedTime.lean, used for Lemmas 2.5
and 2.6) asks that the circle average process of `h(R_b ·) + Q log R_b - γ⁻¹ log b` be a random variable. We prove it
from `ConeScaleRadiusPosStep` (`R_b > 0` a.s.), which the reductions of Lemmas 2.5 and 2.6 already assume.

* **The cone scale radius is a.e. measurable** (`aemeasurable_coneScaleRadius`). With `f(r) = h_r(0) + Q log r`, which
  is a.s. continuous on `(0, ∞)`, the level set `L = {r > 0 : f(r) = γ⁻¹ log b}` meets a compact interval `[α, β]`
  iff `f` takes values `≤ γ⁻¹ log b` and `≥ γ⁻¹ log b` there (intermediate value theorem), iff it does so up to every
  `1/(m+1)` at rational points (`levelTest_iff`). Hence `{x < R_b = sup L}` is, up to a null set, a countable Boolean
  combination of the events `{h_q(0) < a}`, `q ∈ ℚ_{>0}` (`lt_sSup_level_iff`; `sup L = 0` if `L` is empty or
  unbounded).
* **The rescaled circle process.** The circle average process has a jointly measurable version
  (`exists_jointlyMeasurable_of_ae_continuous`), which is evaluated at the radii `R_b r > 0`.
-/

open HarmonicBalls

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-! ### Level sets of continuous functions through rational points -/

/-- `f` takes values below `c + 1/(m+1)` and above `c - 1/(m+1)` at rational points of `[α, β]`, for every `m`. -/
def levelTest (f : ℝ → ℝ) (c α β : ℝ) : Prop :=
  (∀ m : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc α β ∧ f q < c + 1 / ((m : ℝ) + 1)) ∧
    ∀ m : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc α β ∧ c - 1 / ((m : ℝ) + 1) < f q

/-- For `f` continuous on `[α, β]`, `α < β`, the level `c` is attained on `[α, β]` iff `levelTest f c α β`. -/
theorem levelTest_iff {f : ℝ → ℝ} {c α β : ℝ} (hf : ContinuousOn f (Icc α β)) (hαβ : α < β) :
    levelTest f c α β ↔ ∃ r ∈ Icc α β, f r = c := by
  constructor
  · rintro ⟨h1, h2⟩
    have hne : (Icc α β).Nonempty := nonempty_Icc.2 hαβ.le
    obtain ⟨r₁, hr₁, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
    obtain ⟨r₂, hr₂, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
    have hle₁ : f r₁ ≤ c := by
      by_contra h
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 (not_le.1 h))
      obtain ⟨q, hq, hfq⟩ := h1 m
      have := isMinOn_iff.1 hmin _ hq
      linarith
    have hge₂ : c ≤ f r₂ := by
      by_contra h
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 (not_le.1 h))
      obtain ⟨q, hq, hfq⟩ := h2 m
      have := isMaxOn_iff.1 hmax _ hq
      linarith
    have hsub : uIcc r₁ r₂ ⊆ Icc α β := uIcc_subset_Icc hr₁ hr₂
    obtain ⟨r, hr, hfr⟩ := intermediate_value_uIcc (hf.mono hsub) (mem_uIcc.2 (Or.inl ⟨hle₁, hge₂⟩))
    exact ⟨r, hsub hr, hfr⟩
  · rintro ⟨r, hr, hfr⟩
    have key : ∀ m : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc α β ∧ |f q - c| < 1 / ((m : ℝ) + 1) := by
      intro m
      have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 (hf r hr) _ hm
      have hlo : max α (r - δ) < min β (r + δ) := by
        apply max_lt <;> apply lt_min
        · exact hαβ
        · linarith [hr.1]
        · linarith [hr.2]
        · linarith
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlo
      have hqI : (q : ℝ) ∈ Icc α β :=
        ⟨(le_max_left _ _).trans hq1.le, hq2.le.trans (min_le_left _ _)⟩
      have hqd : dist (q : ℝ) r < δ := by
        rw [Real.dist_eq, abs_sub_lt_iff]
        constructor
        · linarith [min_le_right β (r + δ)]
        · linarith [le_max_right α (r - δ)]
      refine ⟨q, hqI, ?_⟩
      have := hδf hqI hqd
      rwa [Real.dist_eq, hfr] at this
    refine ⟨fun m => ?_, fun m => ?_⟩
    · obtain ⟨q, hq, h⟩ := key m
      exact ⟨q, hq, by linarith [(abs_sub_lt_iff.1 h).1]⟩
    · obtain ⟨q, hq, h⟩ := key m
      exact ⟨q, hq, by linarith [(abs_sub_lt_iff.1 h).2]⟩

/-- Some rational interval `[α, β] ⊆ (max x 0, ∞)` passes the level test. -/
def existsLevelAbove (f : ℝ → ℝ) (c x : ℝ) : Prop :=
  ∃ α β : ℚ, x < α ∧ 0 < α ∧ α < β ∧ levelTest f c α β

/-- No interval `[N + 1, N + 2 + n]` passes the level test, for some `N`. -/
def levelBoundedTest (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, ¬ levelTest f c ((N : ℝ) + 1) ((N : ℝ) + 2 + n)

theorem existsLevelAbove_iff {f : ℝ → ℝ} {c x : ℝ} (hf : ContinuousOn f (Ioi 0)) :
    existsLevelAbove f c x ↔ ∃ r, (0 < r ∧ f r = c) ∧ x < r := by
  constructor
  · rintro ⟨α, β, hxα, hα, hαβ, hT⟩
    have hα0 : (0 : ℝ) < α := by exact_mod_cast hα
    have hαβ' : (α : ℝ) < β := by exact_mod_cast hαβ
    obtain ⟨r, hr, hfr⟩ := (levelTest_iff (hf.mono fun y hy => hα0.trans_le hy.1) hαβ').1 hT
    exact ⟨r, ⟨hα0.trans_le hr.1, hfr⟩, hxα.trans_le hr.1⟩
  · rintro ⟨r, ⟨hr0, hfr⟩, hxr⟩
    obtain ⟨α, hα1, hα2⟩ := exists_rat_btwn (max_lt hxr hr0)
    obtain ⟨β, hβ⟩ := exists_rat_gt r
    have hα0 : (0 : ℝ) < α := (le_max_right x 0).trans_lt hα1
    refine ⟨α, β, (le_max_left x 0).trans_lt hα1, by exact_mod_cast hα0, by exact_mod_cast hα2.trans hβ, ?_⟩
    exact (levelTest_iff (hf.mono fun y hy => hα0.trans_le hy.1) (hα2.trans hβ)).2 ⟨r, ⟨hα2.le, hβ.le⟩, hfr⟩

theorem levelBoundedTest_iff {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousOn f (Ioi 0)) :
    levelBoundedTest f c ↔ BddAbove {r | 0 < r ∧ f r = c} := by
  have hI : ∀ N n : ℕ, ContinuousOn f (Icc ((N : ℝ) + 1) ((N : ℝ) + 2 + n)) := fun N n =>
    hf.mono fun y hy => lt_of_lt_of_le (by positivity) hy.1
  have hlt : ∀ N n : ℕ, (N : ℝ) + 1 < (N : ℝ) + 2 + n := fun N n => by
    have := (n.cast_nonneg : (0 : ℝ) ≤ n)
    linarith
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨(N : ℝ) + 1, fun r hr => ?_⟩
    by_contra h
    have h' : (N : ℝ) + 1 < r := not_le.1 h
    obtain ⟨n, hn⟩ := exists_nat_gt r
    have hN0 := (N.cast_nonneg : (0 : ℝ) ≤ N)
    exact hN n ((levelTest_iff (hI N n) (hlt N n)).2 ⟨r, ⟨h'.le, by linarith⟩, hr.2⟩)
  · rintro ⟨B, hB⟩
    obtain ⟨N, hN⟩ := exists_nat_ge B
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨r, hr, hfr⟩ := (levelTest_iff (hI N n) (hlt N n)).1 hn
    have hrB := hB ⟨(by positivity : (0 : ℝ) < (N : ℝ) + 1).trans_le hr.1, hfr⟩
    linarith [hr.1]

/-- **`sup` of a level set through rational tests.** For `f` continuous on `(0, ∞)`,
`x < sup {r > 0 : f(r) = c}` iff either the level set is bounded and meets `(x, ∞)`, or `x < 0` and the level set is
empty or unbounded (then its `sSup` is `0`). -/
theorem lt_sSup_level_iff {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousOn f (Ioi 0)) (x : ℝ) :
    x < sSup {r | 0 < r ∧ f r = c} ↔ (levelBoundedTest f c ∧ existsLevelAbove f c x) ∨
      (x < 0 ∧ ¬(levelBoundedTest f c ∧ existsLevelAbove f c 0)) := by
  rw [levelBoundedTest_iff hf, existsLevelAbove_iff hf, existsLevelAbove_iff hf]
  by_cases hL : BddAbove {r | 0 < r ∧ f r = c} ∧ {r | 0 < r ∧ f r = c}.Nonempty
  · have h0 : ∃ r, (0 < r ∧ f r = c) ∧ 0 < r := by
      obtain ⟨r, hr⟩ := hL.2
      exact ⟨r, hr, hr.1⟩
    constructor
    · intro h
      obtain ⟨r, hr, hxr⟩ := exists_lt_of_lt_csSup hL.2 h
      exact Or.inl ⟨hL.1, r, hr, hxr⟩
    · rintro (⟨-, r, hr, hxr⟩ | ⟨-, hn⟩)
      · exact lt_csSup_of_lt hL.1 hr hxr
      · exact absurd ⟨hL.1, h0⟩ hn
  · have hsup : sSup {r | 0 < r ∧ f r = c} = 0 := by
      by_cases hb : BddAbove {r | 0 < r ∧ f r = c}
      · have he : {r | 0 < r ∧ f r = c} = ∅ := by
          rw [← not_nonempty_iff_eq_empty]
          exact fun hne => hL ⟨hb, hne⟩
        rw [he, Real.sSup_empty]
      · exact Real.sSup_of_not_bddAbove hb
    rw [hsup]
    constructor
    · intro h
      exact Or.inr ⟨h, fun ⟨hb, r, hr, _⟩ => hL ⟨hb, r, hr⟩⟩
    · rintro (⟨hb, r, hr, _⟩ | ⟨h, _⟩)
      · exact absurd ⟨hb, r, hr⟩ hL
      · exact h

/-! ### Measurability -/

section Measurable

variable {Ω : Type*} [MeasurableSpace Ω] {F : Ω → ℝ → ℝ}

theorem measurableSet_levelTest (hF : ∀ q : ℚ, 0 < (q : ℝ) → Measurable fun ω => F ω q) {c α β : ℝ}
    (hα : 0 < α) : MeasurableSet {ω | levelTest (F ω) c α β} := by
  have h : ∀ (q : ℚ) (a : ℝ), Measurable fun ω => (q : ℝ) ∈ Icc α β ∧ F ω q < a := by
    intro q a
    by_cases hq : (q : ℝ) ∈ Icc α β
    · exact measurable_const.and
        (measurableSet_setOfPred.1 (measurableSet_lt (hF q (hα.trans_le hq.1)) measurable_const))
    · simp only [hq, false_and]
      exact measurable_const
  have h' : ∀ (q : ℚ) (a : ℝ), Measurable fun ω => (q : ℝ) ∈ Icc α β ∧ a < F ω q := by
    intro q a
    by_cases hq : (q : ℝ) ∈ Icc α β
    · exact measurable_const.and
        (measurableSet_setOfPred.1 (measurableSet_lt measurable_const (hF q (hα.trans_le hq.1))))
    · simp only [hq, false_and]
      exact measurable_const
  unfold levelTest
  exact measurableSet_setOfPred.2 ((Measurable.forall fun _ => Measurable.exists fun q => h q _).and
    (Measurable.forall fun _ => Measurable.exists fun q => h' q _))

theorem measurableSet_levelBoundedTest (hF : ∀ q : ℚ, 0 < (q : ℝ) → Measurable fun ω => F ω q) (c : ℝ) :
    MeasurableSet {ω | levelBoundedTest (F ω) c} := by
  unfold levelBoundedTest
  exact measurableSet_setOfPred.2 (Measurable.exists fun N => Measurable.forall fun n =>
    (measurableSet_setOfPred.1 (measurableSet_levelTest hF (c := c) (β := (N : ℝ) + 2 + n)
      (by positivity : (0 : ℝ) < (N : ℝ) + 1))).not)

theorem measurableSet_existsLevelAbove (hF : ∀ q : ℚ, 0 < (q : ℝ) → Measurable fun ω => F ω q) (c x : ℝ) :
    MeasurableSet {ω | existsLevelAbove (F ω) c x} := by
  unfold existsLevelAbove
  refine measurableSet_setOfPred.2 (Measurable.exists fun α => Measurable.exists fun β => ?_)
  by_cases hα : (0 : ℚ) < α
  · exact measurable_const.and (measurable_const.and (measurable_const.and
      (measurableSet_setOfPred.1 (measurableSet_levelTest hF (c := c) (β := β) (by exact_mod_cast hα)))))
  · simp only [hα, false_and, and_false]
    exact measurable_const

end Measurable

/-- **The cone scale radius `R_b` is an a.e. measurable random variable.** -/
theorem aemeasurable_coneScaleRadius {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hQC : IsQuantumCone γ P hC hcirc) (b : ℝ) :
    AEMeasurable (fun ω => coneScaleRadius γ (hcirc ω) b) P := by
  set F : Ω → ℝ → ℝ := fun ω r => hcirc ω r 0 + lqgQ γ * Real.log r with hFdef
  have hF : ∀ q : ℚ, 0 < (q : ℝ) → Measurable fun ω => F ω q := fun q hq =>
    (hQC.measurable_circle q 0 hq).add_const _
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (F ω) (Ioi 0) := by
    filter_upwards [hQC.ae_continuousOn_circle] with ω hω
    exact (hω.comp (continuous_id.prodMk continuous_const).continuousOn fun r hr => ⟨hr, mem_univ _⟩).add
      (continuousOn_const.mul (Real.continuousOn_log.mono fun r hr => (show (0 : ℝ) < r from hr).ne'))
  have hnull : NullMeasurable (fun ω => coneScaleRadius γ (hcirc ω) b) P := by
    refine measurable_of_Ioi (δ := NullMeasurableSpace Ω P) fun x => ?_
    have hM : MeasurableSet {ω | (levelBoundedTest (F ω) (γ⁻¹ * Real.log b) ∧
        existsLevelAbove (F ω) (γ⁻¹ * Real.log b) x) ∨ (x < 0 ∧ ¬(levelBoundedTest (F ω) (γ⁻¹ * Real.log b) ∧
          existsLevelAbove (F ω) (γ⁻¹ * Real.log b) 0))} :=
      ((measurableSet_levelBoundedTest hF _).inter (measurableSet_existsLevelAbove hF _ x)).union
        ((MeasurableSet.const (x < 0)).inter
          ((measurableSet_levelBoundedTest hF _).inter (measurableSet_existsLevelAbove hF _ 0)).compl)
    refine hM.nullMeasurableSet.congr ?_
    filter_upwards [hcont] with ω hω
    exact propext (lt_sSup_level_iff hω x).symm
  exact hnull.aemeasurable

/-- **`ConeRescaledCircleAEMeasurableStep`** from `ConeScaleRadiusPosStep`. -/
theorem coneRescaledCircleAEMeasurableStep_of_pos (hpos : ConeScaleRadiusPosStep) :
    ConeRescaledCircleAEMeasurableStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc _ hcone b hb
  obtain ⟨hP, hQC, -⟩ := hcone
  have hRpos := hpos γ hγ hγ2 Ω P hC hcirc hP hQC b hb
  obtain ⟨R', hR'm, hR'ae⟩ := aemeasurable_coneScaleRadius hQC b
  obtain ⟨Rp, hRpm, hRp0, hRpae⟩ : ∃ Rp : Ω → ℝ, Measurable Rp ∧ (∀ ω, 0 < Rp ω) ∧
      ∀ᵐ ω ∂P, Rp ω = coneScaleRadius γ (hcirc ω) b := by
    refine ⟨fun ω => if 0 < R' ω then R' ω else 1,
      Measurable.ite (measurableSet_lt measurable_const hR'm) hR'm measurable_const, fun ω => ?_, ?_⟩
    · dsimp only
      split_ifs with h
      exacts [h, one_pos]
    · filter_upwards [hRpos, hR'ae] with ω hω hR'
      have h0 : 0 < R' ω := hR' ▸ hω
      simp [h0, hR']
  obtain ⟨g, hgm, hgae⟩ := exists_jointlyMeasurable_of_ae_continuous P (X := Ioi (0 : ℝ) × ℂ)
    (fun ω p => circleProcess (hcirc ω) p) (fun p => (hQC.measurable_circle p.1 p.2 p.1.2).aemeasurable)
    (by
      filter_upwards [hQC.ae_continuousOn_circle] with ω hω
      exact hω.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        fun p => ⟨p.1.2, mem_univ _⟩)
  refine ⟨fun ω p => g (ω, (⟨Rp ω * p.1, mul_pos (hRp0 ω) p.1.2⟩, (Rp ω : ℂ) * p.2)) +
    lqgQ γ * Real.log (Rp ω) - γ⁻¹ * Real.log b, ?_, ?_⟩
  · refine measurable_pi_iff.2 fun p => ?_
    exact ((hgm.comp (measurable_id.prodMk (((hRpm.mul_const _).subtype_mk).prodMk
      ((Complex.measurable_ofReal.comp hRpm).mul_const _)))).add
        (measurable_const.mul hRpm.log)).sub_const _
  · filter_upwards [hRpae, hgae] with ω hRω hgω
    funext p
    simp only [hgω, circleProcess, rescaledCircle]
    rw [hRω]

end MatedCRT
