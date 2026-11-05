import MatedCRT.Proofs.Sec2.ConeFamilyMeasurable.MeasureFunctional
import HarmonicBalls.Proofs.Sec5.IntervalRestriction
import MatedCRT.Proofs.Sec2.ConeScaleInvarianceUpToFixedTime.LQGScaling

/-! # Radial compact containment and the half-ball horizon -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls TopologicalSpace
open scoped ENNReal

/-- Compact containment in the half disk follows from strict growth and
containment of each later family member in the half disk. -/
theorem exists_smaller_ball_of_strictGrowth {Λ : ℝ → Set ℂ} {T : ℝ}
    (hs : IsStoppedAtHalfBall Λ T) (hg : IsStrictlyGrowingOn Λ T)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ∃ r : ℝ, r < 1 / 2 ∧ Λ t ⊆ ball 0 r := by
  obtain ⟨s, hts, hsT⟩ := exists_between ht.2
  have hs0 : 0 < s := ht.1.trans hts
  have hcl : closure (Λ t) ⊆ ball 0 (1 / 2) :=
    (hg t s ht.1 hts hsT).trans (hs.1 s ⟨hs0, hsT⟩)
  obtain ⟨r, hr, hsub⟩ := exists_lt_subset_ball isClosed_closure hcl
  exact ⟨r, hr, subset_closure.trans hsub⟩

/-- The stopping horizon is reconstructed from rational tests when every
before-horizon set lies in a strictly smaller concentric ball. -/
theorem halfBallTest_iff_lt_of_radial_containment
    {C : Ioi (0 : ℝ) → Set ℂ} {Λ : ℝ → Set ℂ} {T : ℝ}
    (ho : ∀ t, IsOpen (C t)) (hm : Monotone C)
    (heq : ∀ t (ht : t ∈ Ioo 0 T), C ⟨t, ht.1⟩ = Λ t)
    (hs : IsStoppedAtHalfBall Λ T)
    (hcompact : ∀ t ∈ Ioo 0 T, ∃ r : ℝ, r < 1 / 2 ∧ Λ t ⊆ ball 0 r)
    (q : PositiveRational) : halfBallTest (C ⟨q, q.property⟩) ↔ (q : ℝ) < T := by
  constructor
  · rintro ⟨r, hr, htest⟩
    by_contra hq
    have hTq : T ≤ (q : ℝ) := le_of_not_gt hq
    obtain ⟨r', hrr', hr'⟩ := exists_rat_btwn hr
    obtain ⟨t, ht, hx⟩ := hs.2 r' hr'
    have hsub := closure_subset_closedBall_of_halfBallTest (ho ⟨q, q.property⟩) htest
    apply hx
    intro x hxΛ
    have hxC : x ∈ C ⟨t, ht.1⟩ := by rwa [heq t ht]
    have hxq := hm (show (⟨t, ht.1⟩ : Ioi (0 : ℝ)) ≤ ⟨q, q.property⟩ from
      le_of_lt (ht.2.trans_le hTq)) hxC
    exact (hsub (subset_closure hxq)).trans_lt hrr'
  · intro hq
    obtain ⟨r, hr, hsub⟩ := hcompact q ⟨q.property, hq⟩
    obtain ⟨r', hrr', hr'⟩ := exists_rat_btwn hr
    refine ⟨r', hr', fun n hn => ?_⟩
    rw [heq q ⟨q.property, hq⟩] at hn
    exact le_of_lt ((hsub hn).trans hrr')

/-- Before-horizon radial compact containment is enough for measurability of
the stopping time. -/
theorem aemeasurable_stoppingTime_of_radial_containment
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {C : Ω → Ioi (0 : ℝ) → Set ℂ} {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hC : AEMeasurable C P)
    (hf : ∀ᵐ ω ∂P, 0 < T ω ∧ (∀ t, IsOpen (C ω t)) ∧ Monotone (C ω) ∧
      (∀ t (ht : t ∈ Ioo 0 (T ω)), C ω ⟨t, ht.1⟩ = Λ ω t) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω) ∧
      ∀ t ∈ Ioo 0 (T ω), ∃ r : ℝ, r < 1 / 2 ∧ Λ ω t ⊆ ball 0 r) :
    AEMeasurable T P := by
  let C' := hC.mk C
  have hmeas : Measurable (fun ω => (halfBallTestHorizon (C' ω)).toReal) :=
    (measurable_halfBallTestHorizon.comp hC.measurable_mk).ennreal_toReal
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hf, hC.ae_eq_mk] with ω hω heq
  have htest : ∀ q : PositiveRational,
      halfBallTest (C ω ⟨q, q.property⟩) ↔ (q : ℝ) < T ω :=
    fun q => halfBallTest_iff_lt_of_radial_containment hω.2.1 hω.2.2.1
      hω.2.2.2.1 hω.2.2.2.2.1 hω.2.2.2.2.2 q
  have hh := congrArg ENNReal.toReal (halfBallTestHorizon_eq htest)
  simpa only [← heq, C', ENNReal.toReal_ofReal hω.1.le] using hh

/-- If one before-horizon set reaches every smaller concentric ball, the same
family already satisfies the stopping predicate at every later intermediate
time. -/
theorem IsStoppedAtHalfBall.restrict_of_early_contact
    {Λ : ℝ → Set ℂ} {T S t : ℝ} (hs : IsStoppedAtHalfBall Λ T)
    (hST : S ≤ T) (ht : t ∈ Ioo 0 S)
    (hcontact : ∀ r : ℝ, r < 1 / 2 → ¬ Λ t ⊆ ball 0 r) :
    IsStoppedAtHalfBall Λ S := by
  refine ⟨?_, ?_⟩
  · intro u hu
    exact hs.1 u ⟨hu.1, hu.2.trans_le hST⟩
  · intro r hr
    exact ⟨t, ht, hcontact r hr⟩

/-- A cone harmonic-ball family remains a family when its time interval is
restricted. -/
theorem IsConeHarmonicBallFamilyOn.restrict_time
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {S T : ℝ}
    (hf : IsConeHarmonicBallFamilyOn μ Λ T) (hS : 0 < S) (hST : S ≤ T) :
    IsConeHarmonicBallFamilyOn μ Λ S := by
  have hsub : Ioo (0 : ℝ) S ⊆ Ioo 0 T := fun _ ht => ⟨ht.1, ht.2.trans_le hST⟩
  refine ⟨fun t ht => hf.1 t (hsub ht), hf.2.1.restrict_time hS hST, ?_⟩
  intro t r ht hr hball ρ hρ
  exact hf.2.2 t r (hsub ht) hr hball ρ hρ


/-- A single measurable functional reconstructs all half-ball stopped
families with radial compact containment and disk volume growth. -/
theorem exists_measurable_halfBallFamily_of_radial_containment :
    ∃ F : Measure ℂ → (ℝ × ℂ → Prop), Measurable F ∧
      ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν (3 / 4) βm βp) →
        ∀ (T : ℝ) (Λ : ℝ → Set ℂ), 0 < T →
          IsConeHarmonicBallFamilyOn ν Λ T → IsStoppedAtHalfBall Λ T →
          (∀ t ∈ Ioo 0 T, ∃ r : ℝ, r < 1 / 2 ∧ Λ t ⊆ ball 0 r) →
          F ν = familyProcess Λ T := by
  classical
  obtain ⟨A, hA, hAeq⟩ := exists_measurable_clusterFamily_of_volumeGrowth
    (R := (3 / 4 : ℝ)) (by norm_num)
  let z : ball (0 : ℂ) (3 / 4) := ⟨0, mem_ball_self (by norm_num)⟩
  let C : Measure ℂ → Ioi (0 : ℝ) → Set ℂ := fun ν t =>
    denseSequenceRegularization (A ν (z, t))
  have hC : Measurable C := by
    apply Measurable.of_eval
    intro t
    exact measurable_denseSequenceRegularization.comp ((measurable_pi_apply (z, t)).comp hA)
  let H : Measure ℂ → ℝ := fun ν => (halfBallTestHorizon (C ν)).toReal
  have hH : Measurable H := (measurable_halfBallTestHorizon.comp hC).ennreal_toReal
  let F : Measure ℂ → (ℝ × ℂ → Prop) := fun ν p =>
    if hp : 0 < p.1 then p.1 < H ν ∧ p.2 ∈ C ν ⟨p.1, hp⟩ else False
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro p
    by_cases hp : 0 < p.1
    · simp only [F, hp, dite_true]
      apply measurableSet_setOfPred.mp
      exact (measurableSet_lt (measurable_const : Measurable fun _ : Measure ℂ => p.1) hH).inter
        (measurableSet_setOfPred.mpr ((measurable_pi_apply p.2).comp
          ((measurable_pi_apply (⟨p.1, hp⟩ : Ioi (0 : ℝ))).comp hC)))
    · simp [F, hp]
  refine ⟨F, hF, ?_⟩
  intro ν hloc hvol T Λ hT hf hs hg
  have hCeq (t : Ioi (0 : ℝ)) : C ν t =
      interior (closure (cluster ν (3 / 4) 0 t)) := by
    have hcluster := congrFun (hAeq ν hloc hvol) (z, t)
    have hopen : IsOpen (cluster ν (3 / 4) 0 t) := by
      obtain ⟨βm, βp, hV⟩ := hvol
      exact (cluster_open_laplacian_of_general greenFunctionBall
        obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
        obstacleCompatibilityShiftStep_holds hloc (by norm_num) hV
        (mem_ball_self (by norm_num)) t.property).1
    simp only [C, hcluster, z]
    exact denseSequenceRegularization_eq hopen
  have hmono : Monotone (C ν) := by
    intro s t hst
    rw [hCeq s, hCeq t]
    apply interior_mono (closure_mono ?_)
    obtain ⟨βm, βp, hV⟩ := hvol
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds
      obstacleCompatibilityShiftStep_holds hloc (by norm_num) hV
      (mem_ball_self (by norm_num)) s.property hst
  have heq : ∀ t (ht : t ∈ Ioo 0 T), C ν ⟨t, ht.1⟩ = Λ t := by
    intro t ht
    rw [hCeq]
    exact (hf.eq_threeQuarterDisk_cluster hs ht).symm
  have htest : ∀ q : PositiveRational, halfBallTest (C ν ⟨q, q.property⟩) ↔ (q : ℝ) < T :=
    fun q => halfBallTest_iff_lt_of_radial_containment
      (fun t => by rw [hCeq]; exact isOpen_interior) hmono heq hs hg q
  have hHν : H ν = T := by
    have hh := congrArg ENNReal.toReal (halfBallTestHorizon_eq htest)
    simpa only [H, ENNReal.toReal_ofReal hT.le] using hh
  funext p
  apply propext
  by_cases hp : 0 < p.1
  · simp only [F, hp, dite_true, hHν, familyProcess, mem_Ioo]
    constructor
    · rintro ⟨ht, hx⟩
      exact ⟨⟨trivial, ht⟩, by rw [← heq p.1 ⟨hp, ht⟩]; exact hx⟩
    · rintro ⟨⟨_, ht⟩, hx⟩
      exact ⟨ht, by rw [heq p.1 ⟨hp, ht⟩]; exact hx⟩
  · simp [F, hp, familyProcess]


/-- A half-ball stopped family is measurable under radial compact containment
and volume growth for its underlying measure. -/
theorem aemeasurable_halfBallFamily_of_radial_containment
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {T : Ω → ℝ} {Λ : Ω → ℝ → Set ℂ}
    (hμ : AEMeasurable μ P)
    (hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βm βp, VolumeGrowth (μ ω) (3 / 4) βm βp)
    (hf : ∀ᵐ ω ∂P, 0 < T ω ∧ IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (T ω) ∧
      IsStoppedAtHalfBall (Λ ω) (T ω) ∧
      ∀ t ∈ Ioo 0 (T ω), ∃ r : ℝ, r < 1 / 2 ∧ Λ ω t ⊆ ball 0 r) :
    AEMeasurable (fun ω => familyProcess (Λ ω) (T ω)) P := by
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_halfBallFamily_of_radial_containment
  refine (hF.comp_aemeasurable hμ).congr ?_
  filter_upwards [hgood, hf] with ω hm hω
  exact hFeq _ hm.1 hm.2 _ _ hω.1 hω.2.1 hω.2.2.1 hω.2.2.2


/-- Early radial contact would make the stated stopped-family conditions
valid at two different horizons for the same family, with distinct stopped
processes. -/
theorem exists_shorter_stopped_family_of_early_contact
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {T t : ℝ}
    (hf : IsConeHarmonicBallFamilyOn μ Λ T) (hs : IsStoppedAtHalfBall Λ T)
    (ht : t ∈ Ioo 0 T)
    (hcontact : ∀ r : ℝ, r < 1 / 2 → ¬ Λ t ⊆ ball 0 r) :
    ∃ S : ℝ, 0 < S ∧ S < T ∧ IsConeHarmonicBallFamilyOn μ Λ S ∧
      IsStoppedAtHalfBall Λ S ∧ familyProcess Λ S ≠ familyProcess Λ T := by
  obtain ⟨S, htS, hST⟩ := exists_between ht.2
  have hS : 0 < S := ht.1.trans htS
  refine ⟨S, hS, hST, hf.restrict_time hS hST.le,
    hs.restrict_of_early_contact hST.le ⟨ht.1, htS⟩ hcontact, ?_⟩
  obtain ⟨u, hSu, huT⟩ := exists_between hST
  have hu : u ∈ Ioo (0 : ℝ) T := ⟨hS.trans hSu, huT⟩
  have hmem : familyProcess Λ T (u, 0) := ⟨hu, hf.2.1.mem u hu⟩
  intro heq
  have hnot : ¬ familyProcess Λ S (u, 0) := by
    intro h
    exact (not_lt_of_ge hSu.le) h.1.2
  exact hnot (heq ▸ hmem)


/-- Uniqueness of the stopped horizon forces every before-horizon family
member to be contained in a strictly smaller concentric ball. -/
theorem radial_containment_of_unique_stopped_family
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {T : ℝ}
    (hf : IsConeHarmonicBallFamilyOn μ Λ T) (hs : IsStoppedAtHalfBall Λ T)
    (huniq : ∀ (S : ℝ) (Γ : ℝ → Set ℂ), 0 < S → IsConeHarmonicBallFamilyOn μ Γ S →
      IsStoppedAtHalfBall Γ S → S = T) :
    ∀ t ∈ Ioo 0 T, ∃ r : ℝ, r < 1 / 2 ∧ Λ t ⊆ ball 0 r := by
  intro t ht
  by_contra h
  push Not at h
  obtain ⟨S, hS, hST, hfS, hsS, _⟩ :=
    exists_shorter_stopped_family_of_early_contact hf hs ht h
  exact (ne_of_lt hST) (huniq S Λ hS hfS hsS)


/-- The uniqueness assertions in Lemmas 2.4 and 2.5 imply measurability of
their stopped families, under cone volume growth and the scaling inputs. -/
theorem coneFamilyAEMeasurableStep_of_unique_stopped_families
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (h27 : VolumeGrowthStmt) (hscale : QuantumConeScalingInput)
    (hlqg : ConeLQGScalingStep) : ConeFamilyAEMeasurableStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  let : IsProbabilityMeasure P := hcone.1
  have h24ae := h24 γ hγ hγ2 Ω P hC hcirc μ hcone
  have hex : ∀ᵐ ω ∂P, ∃ y : ℝ × (ℝ → Set ℂ),
      0 < y.1 ∧ IsConeHarmonicBallFamilyOn (μ ω) y.2 y.1 ∧ IsStoppedAtHalfBall y.2 y.1 := by
    filter_upwards [h24ae] with ω hω
    obtain ⟨T, hT, Λ, hΛ, hs, _⟩ := hω
    exact ⟨(T, Λ), hT, hΛ, hs⟩
  obtain ⟨x, hx⟩ : ∃ x : Ω → ℝ × (ℝ → Set ℂ), ∀ᵐ ω ∂P,
      0 < (x ω).1 ∧ IsConeHarmonicBallFamilyOn (μ ω) (x ω).2 (x ω).1 ∧
        IsStoppedAtHalfBall (x ω).2 (x ω).1 :=
    ⟨fun ω => Classical.epsilon fun y : ℝ × (ℝ → Set ℂ) =>
      0 < y.1 ∧ IsConeHarmonicBallFamilyOn (μ ω) y.2 y.1 ∧ IsStoppedAtHalfBall y.2 y.1,
      by filter_upwards [hex] with ω hω; exact Classical.epsilon_spec hω⟩
  constructor
  · intro T Λ hf
    apply hcone.2.1.measurable_circleProcess.aemeasurable.prodMk
    apply aemeasurable_halfBallFamily_of_radial_containment hcone.aemeasurable_lqgMeasure
      (hcone.ae_volumeGrowth_inside_unit hγ hγ2 h27 (by norm_num))
    filter_upwards [hf, h24ae] with ω hω hgood
    refine ⟨hω.1, hω.2.1, hω.2.2, ?_⟩
    obtain ⟨T₀, hT₀, Λ₀, hΛ₀, hs₀, huniq⟩ := hgood
    have heq := (huniq (T ω) (Λ ω) hω.1 hω.2.1 hω.2.2).1
    apply radial_containment_of_unique_stopped_family hω.2.1 hω.2.2
    intro S Γ hS hΓ hsΓ
    exact ((huniq S Γ hS hΓ hsΓ).1).trans heq.symm
  · intro b hb T Λ hf
    obtain ⟨T₀, Λ₀, hbase, _⟩ :=
      h25 γ hγ hγ2 Ω P hC hcirc μ hcone (fun ω => (x ω).1) (fun ω => (x ω).2) hx b hb
    have hs := hlqg γ hγ hγ2 Ω P hC hcirc μ hcone b hb
    have hR : ∀ᵐ ω ∂P, 0 < coneScaleRadius γ (hcirc ω) b := hs.mono fun _ h => h.1
    have hgood : ∀ᵐ ω ∂P,
        IsLocallyFiniteMeasure (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b) ∧
        ∃ βm βp, VolumeGrowth (rescaledMeasure (μ ω) (coneScaleRadius γ (hcirc ω) b) b)
          (3 / 4) βm βp := by
      filter_upwards [hs, hcone.ae_rescaledVolumeGrowth_inside_unit hγ hγ2 h27 hscale hlqg
        hb (R := (3 / 4 : ℝ)) (by norm_num) (by norm_num)] with ω hω hv
      exact ⟨hω.2.isLocallyFiniteMeasure, hv⟩
    apply (Sec1.aemeasurable_circleProcess_rescaledCircle hscale hγ hγ2 hcone.2.1 hb).prodMk
    apply aemeasurable_halfBallFamily_of_radial_containment
      (hcone.aemeasurable_rescaledMeasure b hR) hgood
    filter_upwards [hf, hbase, hR] with ω hω hbaseω hRω
    refine ⟨hω.1, coneHarmonicBallFamilyOnScalingStep (μ ω) (Λ ω) _ b (T ω)
      hRω hb hω.2.1, hω.2.2, ?_⟩
    intro t ht
    by_contra h
    push Not at h
    obtain ⟨S, htS, hST⟩ := exists_between ht.2
    have hS : 0 < S := ht.1.trans htS
    have hsS := hω.2.2.restrict_of_early_contact hST.le ⟨ht.1, htS⟩ h
    have hfS : IsConeHarmonicBallFamilyOn (μ ω) (Λ ω) (b * S) :=
      hω.2.1.restrict_time (mul_pos hb hS) (mul_le_mul_of_nonneg_left hST.le hb.le)
    have heqS := (hbaseω.2.2.2 S (Λ ω) hS hfS hsS).1
    have heqT := (hbaseω.2.2.2 (T ω) (Λ ω) hω.1 hω.2.1 hω.2.2).1
    exact (ne_of_lt hST) (heqS.trans heqT.symm)


/-- Cone-family measurability from the numbered uniqueness and volume-growth
results, quantum-cone scaling, and the LQG measure properties. -/
theorem coneFamilyAEMeasurableStep_of_numbered_results
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (h27 : VolumeGrowthStmt) (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) : ConeFamilyAEMeasurableStep :=
  coneFamilyAEMeasurableStep_of_unique_stopped_families h24 h25 h27 hscale
    (coneLQGScalingStep_of_steps h22 (coneScaleRadiusPosStep_of_input hscale))


/-- Theorem 2.3 follows from Lemmas 2.4, 2.5 and 2.7 together with the
quantum-cone scaling input and the LQG measure properties. -/
theorem coneHarmonicBalls_of_numbered_results
    (h24 : ConeHarmonicBallsUpToFixedTimeStmt)
    (h25 : ConeScaleInvarianceUpToFixedTimeStmt)
    (h27 : VolumeGrowthStmt) (hscale : QuantumConeScalingInput)
    (h22 : LQGMeasurePropertiesStmt) : ConeHarmonicBallsStmt :=
  coneHarmonicBalls_of_steps h24 h25
    (coneFamilyAEMeasurableStep_of_numbered_results h24 h25 h27 hscale h22)

end MatedCRT
