import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.ConeMeasure
import MatedCRT.Steps.Sec2.ConeHarmonicBallsUpToFixedTime

/-! # The half-ball stopping time from countable tests -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls TopologicalSpace
open scoped ENNReal

/-- The rational positive times used to reconstruct a stopping time. -/
abbrev PositiveRational := {q : ℚ // 0 < (q : ℝ)}

/-- An open set is tested for containment in a ball of radius less than
one half using a countable dense sequence. -/
def halfBallTest (U : Set ℂ) : Prop :=
  ∃ r : ℚ, (r : ℝ) < 1 / 2 ∧ ∀ n : ℕ,
    denseSeq ℂ n ∈ U → denseSeq ℂ n ∈ closedBall (0 : ℂ) r

theorem measurable_halfBallTest : Measurable halfBallTest := by
  unfold halfBallTest
  apply Measurable.exists
  intro r
  apply measurable_const.and
  apply Measurable.forall
  intro n
  exact (measurable_pi_apply (denseSeq ℂ n)).imp measurable_const

theorem closure_subset_closedBall_of_halfBallTest {U : Set ℂ} (ho : IsOpen U)
    {r : ℝ} (h : ∀ n : ℕ, denseSeq ℂ n ∈ U →
      denseSeq ℂ n ∈ closedBall (0 : ℂ) r) : closure U ⊆ closedBall (0 : ℂ) r := by
  rw [closure_eq_closure_inter_denseSeq ho]
  apply closure_minimal _ isClosed_closedBall
  rintro x ⟨hx, n, rfl⟩
  exact h n hx

/-- Rational tests characterize the interval before the stopping time for
an increasing open family agreeing with a strictly growing stopped family. -/
theorem halfBallTest_iff_lt {C : Ioi (0 : ℝ) → Set ℂ} {Λ : ℝ → Set ℂ} {T : ℝ}
    (ho : ∀ t, IsOpen (C t)) (hm : Monotone C)
    (heq : ∀ t (ht : t ∈ Ioo 0 T), C ⟨t, ht.1⟩ = Λ t)
    (hs : IsStoppedAtHalfBall Λ T) (hg : IsStrictlyGrowingOn Λ T)
    (q : PositiveRational) : halfBallTest (C ⟨q, q.property⟩) ↔ (q : ℝ) < T := by
  constructor
  · rintro ⟨r, hr, htest⟩
    by_contra hq
    have hTq : T ≤ (q : ℝ) := le_of_not_gt hq
    obtain ⟨r', hrr', hr'⟩ := exists_rat_btwn hr
    obtain ⟨t, ht, hx⟩ := hs.2 r' hr'
    have hsub := (closure_subset_closedBall_of_halfBallTest (ho ⟨q, q.property⟩) htest)
    apply hx
    intro x hxΛ
    have hxC : x ∈ C ⟨t, ht.1⟩ := by rwa [heq t ht]
    have hxq := (hm (show (⟨t, ht.1⟩ : Ioi (0 : ℝ)) ≤ ⟨q, q.property⟩ from
      le_of_lt (ht.2.trans_le hTq))) hxC
    have hdist : dist x 0 ≤ (r : ℝ) := hsub (subset_closure hxq)
    exact hdist.trans_lt hrr'
  · intro hq
    obtain ⟨t, hqt, htT⟩ := exists_between hq
    have ht0 : 0 < t := q.property.trans hqt
    have hcl : closure (Λ q) ⊆ ball 0 (1 / 2) :=
      (hg q t q.property hqt htT).trans (hs.1 t ⟨ht0, htT⟩)
    obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball isClosed_closure hcl
    obtain ⟨r', hrr', hr'⟩ := exists_rat_btwn hr
    refine ⟨r', hr', fun n hn => ?_⟩
    rw [heq q ⟨q.property, hq⟩] at hn
    exact le_of_lt ((hsub (subset_closure hn)).trans hrr')

/-- A countable supremum of the successful rational tests. -/
noncomputable def halfBallTestHorizon (C : Ioi (0 : ℝ) → Set ℂ) : ℝ≥0∞ := by
  classical
  exact ⨆ q : PositiveRational, if halfBallTest (C ⟨q, q.property⟩) then ENNReal.ofReal q else 0

theorem measurable_halfBallTestHorizon : Measurable halfBallTestHorizon := by
  classical
  unfold halfBallTestHorizon
  apply Measurable.iSup
  intro q
  exact Measurable.ite (measurable_halfBallTest.comp
    (measurable_pi_apply (⟨q, q.property⟩ : Ioi (0 : ℝ)))).setOf
    measurable_const measurable_const

/-- The countable horizon recovers the stopping time. -/
theorem halfBallTestHorizon_eq {C : Ioi (0 : ℝ) → Set ℂ} {T : ℝ}
    (h : ∀ q : PositiveRational, halfBallTest (C ⟨q, q.property⟩) ↔ (q : ℝ) < T) :
    halfBallTestHorizon C = ENNReal.ofReal T := by
  classical
  have hle : halfBallTestHorizon C ≤ ENNReal.ofReal T := by
    apply iSup_le
    intro q
    by_cases hq : halfBallTest (C ⟨q, q.property⟩)
    · simp only [hq, ite_true]
      exact ENNReal.ofReal_le_ofReal (le_of_lt ((h q).mp hq))
    · simp [hq]
  have hfin : halfBallTestHorizon C ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hrev : T ≤ (halfBallTestHorizon C).toReal := by
    by_contra hn
    have hlt : (halfBallTestHorizon C).toReal < T := lt_of_not_ge hn
    have hnonneg : 0 ≤ (halfBallTestHorizon C).toReal := ENNReal.toReal_nonneg
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq0 : 0 < (q : ℝ) := hnonneg.trans_lt hq1
    let p : PositiveRational := ⟨q, hq0⟩
    have hp : halfBallTest (C ⟨p, p.property⟩) := (h p).mpr hq2
    have hbound : ENNReal.ofReal (q : ℝ) ≤ halfBallTestHorizon C := by
      apply le_iSup_of_le p
      simp [p, hp]
    exact (not_le_of_gt hq1) ((ENNReal.ofReal_le_iff_le_toReal hfin).mp hbound)
  apply le_antisymm hle
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mpr hrev

/-- A stopped family agreeing with a measurable increasing open family has
an almost-everywhere measurable stopping time. -/
theorem aemeasurable_stoppingTime_of_open_family
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {C : Ω → Ioi (0 : ℝ) → Set ℂ} {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hC : AEMeasurable C P)
    (hf : ∀ᵐ ω ∂P, 0 < T ω ∧ (∀ t, IsOpen (C ω t)) ∧ Monotone (C ω) ∧
      (∀ t (ht : t ∈ Ioo 0 (T ω)), C ω ⟨t, ht.1⟩ = Λ ω t) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω) ∧ IsStrictlyGrowingOn (Λ ω) (T ω)) :
    AEMeasurable T P := by
  let C' := hC.mk C
  have hmeas : Measurable (fun ω => (halfBallTestHorizon (C' ω)).toReal) :=
    (measurable_halfBallTestHorizon.comp hC.measurable_mk).ennreal_toReal
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hf, hC.ae_eq_mk] with ω hω heq
  have htest : ∀ q : PositiveRational,
      halfBallTest (C ω ⟨q, q.property⟩) ↔ (q : ℝ) < T ω :=
    fun q => halfBallTest_iff_lt hω.2.1 hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2.1 hω.2.2.2.2.2 q
  have hh := congrArg ENNReal.toReal (halfBallTestHorizon_eq htest)
  simpa only [← heq, C', ENNReal.toReal_ofReal hω.1.le] using hh

/-- Under the volume-growth estimate and strict growth, the stopping time
of a cone harmonic-ball family is measurable. -/
theorem aemeasurable_coneHalfBallStoppingTime
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    (hgrow : ConeHarmonicBallStrictGrowthStep) {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hf : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω)) : AEMeasurable T P := by
  let C : Ω → Ioi (0 : ℝ) → Set ℂ := fun ω t =>
    interior (closure (cluster (μ ω) (3 / 4) 0 t))
  let curry : ((Ioi (0 : ℝ) × ℂ) → Prop) → Ioi (0 : ℝ) → Set ℂ :=
    fun F t x => F (t, x)
  have hcurry : Measurable curry := by
    apply Measurable.of_eval
    intro t
    apply Measurable.of_eval
    intro x
    exact measurable_pi_apply (t, x)
  have hg : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) (3 / 4) βminus βplus :=
    hcone.ae_volumeGrowth_inside_unit hγ hγ2 h27 (by norm_num)
  have hCm : AEMeasurable C P := hcurry.comp_aemeasurable
    (aemeasurable_regularizedClusterFamily_of_volumeGrowth (by norm_num)
      hcone.aemeasurable_lqgMeasure hg)
  apply aemeasurable_stoppingTime_of_open_family hCm
  filter_upwards [hf, hg, hgrow γ hγ hγ2 Ω P hC hcirc μ hcone] with ω hω hv hstrict
  refine ⟨hω.1, (fun _ => isOpen_interior), ?_, ?_, hω.2.2, hstrict _ _ hω.2.1⟩
  · intro s t hst
    apply interior_mono (closure_mono ?_)
    obtain ⟨hμω, βm, βp, hV⟩ := hv
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds
      obstacleCompatibilityShiftStep_holds hμω (by norm_num) hV
      (mem_ball_self (by norm_num)) s.property hst
  · intro t ht
    exact (hω.2.1.eq_threeQuarterDisk_cluster hω.2.2 ht).symm

/-- The circle-average process and the stopped harmonic-ball family are
jointly measurable under volume growth and strict growth. -/
theorem aemeasurable_coneHalfBallPair
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hcone : IsConeField γ P hC hcirc μ) (h27 : VolumeGrowthStmt)
    (hgrow : ConeHarmonicBallStrictGrowthStep) {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hf : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω)) :
    AEMeasurable (fun ω => (circleProcess (hcirc ω), familyProcess (Λ ω) (T ω))) P := by
  have hT := aemeasurable_coneHalfBallStoppingTime hγ hγ2 hcone h27 hgrow hf
  have hΛ := aemeasurable_coneFamilyProcess hγ hγ2 hcone h27 hT (hf.mono fun _ h => h.2)
  have hc : Measurable (fun ω => circleProcess (hcirc ω)) := by
    apply Measurable.of_eval
    intro p
    exact hcone.2.1.measurable_circle p.1 p.2 p.1.property
  exact hc.aemeasurable.prodMk hΛ

end MatedCRT
