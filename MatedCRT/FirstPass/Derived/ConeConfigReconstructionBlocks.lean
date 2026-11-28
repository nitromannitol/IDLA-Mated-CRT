import MatedCRT.FirstPass.Derived.ConeConfigReconstructionMap
import MatedCRT.FirstPass.Derived.ConeConfigReconstructionClock

/-!
# The block clocks of the reconstruction are the quantum clock

Let `ξ = e ∘ φ` be a curve parametrized by the mass of a measure `μ` (`IsMassParam`): `φ` is an increasing
homeomorphism of the line fixing `0`, and `μ (ξ ([s, t])) = t - s`. For a curve `e` in the curve event
`ReconCurveEvent α R a L δ M`, the two blocks `e([-L, -a])` and `e([a, L])` lie in the annulus `{δ < |z| < M}`, where
the capped restriction of `μ` is `μ` itself. This file shows that on the two blocks the inverse mass clock of the
reconstruction (`posBlockTime`, `negBlockTime`) is the quantum clock `φ`, and that the masses of the blocks are the
quantum lengths of the blocks (`posBlockMass`, `negBlockMass`).

## Main statements

* `IsMassParam`: `ξ = e ∘ φ` is parametrized by the mass of `μ`.
* `IsMassParam.measure_image`, `quantumTimeOffsets_eq`: `μ (e ([u, v])) = φ⁻¹ v - φ⁻¹ u`, and the two offsets are
  `(φ⁻¹ (-a), φ⁻¹ a)`.
* `posBlockMass_eq`, `negBlockMass_eq`, `posBlockTime_eq`, `negBlockTime_eq`: the masses and clocks of the blocks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRT

open LatticeProb.LQG (massClock massClockInv)

/-- `ξ = e ∘ φ` is parametrized by the mass of `μ`. -/
structure IsMassParam (e ξ : C(ℝ, ℂ)) (φ : ℝ ≃o ℝ) (μ : Measure ℂ) : Prop where
  zero : φ 0 = 0
  comp : ∀ t, ξ t = e (φ t)
  area : ∀ s t : ℝ, s ≤ t → μ (ξ '' Icc s t) = ENNReal.ofReal (t - s)

variable {α R a L δ M : ℝ} {e ξ : C(ℝ, ℂ)} {φ : ℝ ≃o ℝ} {μ : Measure ℂ}

theorem IsMassParam.symm_zero (hp : IsMassParam e ξ φ μ) : φ.symm 0 = 0 :=
  φ.symm_apply_eq.2 hp.zero.symm

theorem IsMassParam.measure_image (hp : IsMassParam e ξ φ μ) {u v : ℝ} (huv : u ≤ v) :
    μ (e '' Icc u v) = ENNReal.ofReal (φ.symm v - φ.symm u) := by
  have hξ : ⇑ξ = ⇑e ∘ ⇑φ := funext hp.comp
  have himg : e '' Icc u v = ξ '' Icc (φ.symm u) (φ.symm v) := by
    rw [hξ, Set.image_comp, φ.image_Icc, φ.apply_symm_apply, φ.apply_symm_apply]
  rw [himg]
  exact hp.area _ _ (φ.symm.monotone huv)

theorem quantumTimeOffsets_eq (hp : IsMassParam e ξ φ μ) (ha : 0 < a) :
    quantumTimeOffsets e μ a = ![φ.symm (-a), φ.symm a] := by
  have h1 : φ.symm (-a) ≤ 0 := by
    rw [← hp.symm_zero]
    exact φ.symm.monotone (by linarith)
  have h2 : 0 ≤ φ.symm a := by
    rw [← hp.symm_zero]
    exact φ.symm.monotone ha.le
  unfold quantumTimeOffsets
  rw [hp.measure_image (by linarith), hp.measure_image ha.le, hp.symm_zero,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ext i
  fin_cases i <;> simp

/-! ### The capped measure on the annulus -/

/-- On the annulus, the capped restriction of a measure finite on compacts is the measure. -/
theorem cappedMeasure_restrict_apply [IsFiniteMeasureOnCompacts μ] {S : Set ℂ}
    (hS : S ⊆ offsetOuterAnnulus δ M) :
    cappedMeasure M (μ.restrict (offsetOuterAnnulus δ M)) S = μ S := by
  have hfin : μ.restrict (offsetOuterAnnulus δ M) (closedBall (0 : ℂ) M) < ⊤ :=
    lt_of_le_of_lt ((Measure.le_iff'.1 Measure.restrict_le_self) _)
      (isCompact_closedBall (0 : ℂ) M).measure_lt_top
  have hsub : offsetOuterAnnulus δ M ⊆ closedBall (0 : ℂ) M := fun z hz =>
    ball_subset_closedBall (show z ∈ ball (0 : ℂ) M \ closedBall (0 : ℂ) δ from hz).1
  unfold cappedMeasure
  rw [ite_eq_left hfin, Measure.restrict_apply' measurableSet_closedBall,
    Measure.restrict_apply' (measurableSet_offsetOuterAnnulus δ M),
    inter_eq_left.2 (hS.trans hsub), inter_eq_left.2 hS]

theorem offsetOuterAnnulus_two_mul_subset (hδ : 0 < δ) :
    offsetOuterAnnulus (2 * δ) (M / 2) ⊆ offsetOuterAnnulus δ M := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := show z ∈ ball (0 : ℂ) (M / 2) \ closedBall (0 : ℂ) (2 * δ) from hz
  rw [mem_ball_zero_iff] at hz1
  rw [mem_closedBall_zero_iff, not_le] at hz2
  refine ⟨mem_ball_zero_iff.2 (by linarith [norm_nonneg z]), fun h => ?_⟩
  rw [mem_closedBall_zero_iff] at h
  linarith

theorem image_Icc_pos_subset (hE : e ∈ ReconCurveEvent α R a L δ M) (hδ : 0 < δ) {u v : ℝ}
    (hu : a ≤ u) (hv : v ≤ L) : e '' Icc u v ⊆ offsetOuterAnnulus δ M := by
  rintro _ ⟨t, ht, rfl⟩
  exact offsetOuterAnnulus_two_mul_subset hδ (hE.2.2 (Or.inr ⟨hu.trans ht.1, ht.2.trans hv⟩))

theorem image_Icc_neg_subset (hE : e ∈ ReconCurveEvent α R a L δ M) (hδ : 0 < δ) {u v : ℝ}
    (hu : -L ≤ u) (hv : v ≤ -a) : e '' Icc u v ⊆ offsetOuterAnnulus δ M := by
  rintro _ ⟨t, ht, rfl⟩
  exact offsetOuterAnnulus_two_mul_subset hδ (hE.2.2 (Or.inl ⟨hu.trans ht.1, ht.2.trans hv⟩))

/-- The shifted clock `s ↦ φ (φ⁻¹ c + s) - c` of the block starting at the quantum time `φ⁻¹ c`. -/
def blockShiftIso (φ : ℝ ≃o ℝ) (c : ℝ) : ℝ ≃o ℝ :=
  (OrderIso.addLeft (φ.symm c)).trans (φ.trans (OrderIso.addRight (-c)))

theorem blockShiftIso_apply (φ : ℝ ≃o ℝ) (c s : ℝ) :
    blockShiftIso φ c s = φ (φ.symm c + s) - c := by
  simp [blockShiftIso, sub_eq_add_neg]

theorem blockShiftIso_symm_apply (φ : ℝ ≃o ℝ) (c q : ℝ) :
    (blockShiftIso φ c).symm q = φ.symm (c + q) - φ.symm c := by
  rw [OrderIso.symm_apply_eq, blockShiftIso_apply]
  simp

theorem blockShiftIso_zero (φ : ℝ ≃o ℝ) (c : ℝ) : blockShiftIso φ c 0 = 0 := by
  rw [blockShiftIso_apply]
  simp

/-- The image of an interval under a translated curve. -/
theorem image_shift_Icc (e : C(ℝ, ℂ)) (c u v : ℝ) :
    (fun t => e (c + t)) '' Icc u v = e '' Icc (c + u) (c + v) := by
  rw [show (fun t => e (c + t)) = e ∘ (fun t => c + t) from rfl, Set.image_comp,
    Set.image_const_add_Icc]

variable [IsFiniteMeasureOnCompacts μ]

/-! ### The positive block -/

/-- The capped mass of the image of `[a, a + q]` on the positive block. -/
theorem pos_capped_image (hp : IsMassParam e ξ φ μ) (hE : e ∈ ReconCurveEvent α R a L δ M)
    (hδ : 0 < δ) {q : ℝ} (hq0 : 0 ≤ q) (hqL : a + q ≤ L) :
    cappedMeasure M (μ.restrict (offsetOuterAnnulus δ M)) (e '' Icc a (a + q)) =
      ENNReal.ofReal (φ.symm (a + q) - φ.symm a) := by
  rw [cappedMeasure_restrict_apply (image_Icc_pos_subset hE hδ le_rfl hqL),
    hp.measure_image (by linarith)]

theorem posBlockMass_eq (hp : IsMassParam e ξ φ μ) (haL : a < L)
    (hδ : 0 < δ) (hE : e ∈ ReconCurveEvent α R a L δ M) :
    posBlockMass a L M e (μ.restrict (offsetOuterAnnulus δ M)) = φ.symm L - φ.symm a := by
  unfold posBlockMass
  rw [cappedMeasure_restrict_apply (image_Icc_pos_subset hE hδ le_rfl le_rfl),
    hp.measure_image haL.le, ENNReal.toReal_ofReal]
  have := φ.symm.monotone haL.le
  linarith

theorem posBlockTime_eq (hp : IsMassParam e ξ φ μ) (haL : a < L)
    (hδ : 0 < δ) (hE : e ∈ ReconCurveEvent α R a L δ M) {s : ℝ} (hs0 : 0 ≤ s)
    (hsT : s < φ.symm L - φ.symm a) :
    posBlockTime a M e (μ.restrict (offsetOuterAnnulus δ M)) s = φ (φ.symm a + s) := by
  set c := cappedMeasure M (μ.restrict (offsetOuterAnnulus δ M)) with hc
  set v := blockShiftIso φ a with hv
  have hsucc : ∀ q : ℝ, 0 ≤ q → a + q ≤ L →
      massClock c (fun t => e (a + t)) q = φ.symm (a + q) - φ.symm a := by
    intro q hq0 hqL
    have himg : (fun t => e (a + t)) '' Icc 0 q = e '' Icc a (a + q) := by
      rw [image_shift_Icc, add_zero]
    unfold massClock
    rw [ite_eq_left hq0, himg, hc, pos_capped_image hp hE hδ hq0 hqL, ENNReal.toReal_ofReal]
    have := φ.symm.monotone (show a ≤ a + q by linarith)
    linarith
  have hvT : v (φ.symm L - φ.symm a) = L - a := by
    rw [hv, blockShiftIso_apply]
    simp
  have hres := massClockInv_eq_of_posBlock (μ := c) (L := fun t => e (a + t)) (v := v)
    (blockShiftIso_zero φ a) (T := φ.symm L - φ.symm a)
    (fun q hq0 hqv => by
      rw [hv, blockShiftIso_symm_apply]
      rw [hvT] at hqv
      exact hsucc q hq0 (by linarith))
    (fun q hq => by
      rw [hvT] at hq
      have hq0 : 0 ≤ q := by linarith
      have hmono : (c (e '' Icc a L)).toReal ≤ (c ((fun t => e (a + t)) '' Icc 0 q)).toReal := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
        rw [image_shift_Icc, add_zero]
        exact Set.image_mono (Icc_subset_Icc le_rfl (by linarith))
      have hL : (c (e '' Icc a L)).toReal = φ.symm L - φ.symm a := by
        have := posBlockMass_eq hp haL hδ hE
        exact this
      unfold massClock
      rw [ite_eq_left hq0]
      linarith)
    (fun q hq => by
      unfold massClock
      rw [ite_eq_right (not_le.2 hq)]
      exact neg_nonpos.2 ENNReal.toReal_nonneg)
    hs0 hsT
  unfold posBlockTime
  rw [hres, hv, blockShiftIso_apply]
  ring

/-! ### The negative block -/

theorem negBlockMass_eq (hp : IsMassParam e ξ φ μ) (haL : a < L)
    (hδ : 0 < δ) (hE : e ∈ ReconCurveEvent α R a L δ M) :
    negBlockMass a L M e (μ.restrict (offsetOuterAnnulus δ M)) =
      φ.symm (-a) - φ.symm (-L) := by
  unfold negBlockMass
  rw [cappedMeasure_restrict_apply (image_Icc_neg_subset hE hδ le_rfl le_rfl),
    hp.measure_image (by linarith), ENNReal.toReal_ofReal]
  have := φ.symm.monotone (show -L ≤ -a by linarith)
  linarith

theorem negBlockTime_eq (hp : IsMassParam e ξ φ μ) (haL : a < L)
    (hδ : 0 < δ) (hE : e ∈ ReconCurveEvent α R a L δ M) {s : ℝ}
    (hsT : -(φ.symm (-a) - φ.symm (-L)) < s) (hs0 : s ≤ 0) :
    negBlockTime a M e (μ.restrict (offsetOuterAnnulus δ M)) s = φ (φ.symm (-a) + s) := by
  set c := cappedMeasure M (μ.restrict (offsetOuterAnnulus δ M)) with hc
  set v := blockShiftIso φ (-a) with hv
  set T := φ.symm (-a) - φ.symm (-L) with hT
  have hcneg : ∀ q : ℝ, q ≤ 0 → -L ≤ -a + q →
      c (e '' Icc (-a + q) (-a)) = ENNReal.ofReal (φ.symm (-a) - φ.symm (-a + q)) := by
    intro q hq hqL
    rw [hc, cappedMeasure_restrict_apply (image_Icc_neg_subset hE hδ hqL le_rfl),
      hp.measure_image (by linarith)]
  have hvT : v (-T) = a - L := by
    have h : φ.symm (-a) + -T = φ.symm (-L) := by
      rw [hT]
      ring
    rw [hv, blockShiftIso_apply, h, φ.apply_symm_apply]
    ring
  have hres := massClockInv_eq_of_negBlock (μ := c) (L := fun t => e (-a + t)) (v := v)
    (blockShiftIso_zero φ (-a)) (T := T)
    (fun q hqv hq0 => by
      rw [hv, blockShiftIso_symm_apply]
      rw [hvT] at hqv
      rcases eq_or_lt_of_le hq0 with hq | hq
      · subst hq
        have himg : (fun t => e (-a + t)) '' Icc 0 0 = e '' Icc (-a + 0) (-a + 0) := by
          rw [image_shift_Icc]
        unfold massClock
        rw [ite_eq_left le_rfl, himg, hc,
          cappedMeasure_restrict_apply (image_Icc_neg_subset hE hδ (by linarith) (by linarith)),
          hp.measure_image le_rfl]
        simp
      · have himg : (fun t => e (-a + t)) '' Icc q 0 = e '' Icc (-a + q) (-a) := by
          rw [image_shift_Icc, add_zero]
        unfold massClock
        rw [ite_eq_right (not_le.2 hq), himg, hcneg q hq0 (by linarith), ENNReal.toReal_ofReal]
        · ring
        · have := φ.symm.monotone (show -a + q ≤ -a by linarith)
          linarith)
    (fun q hq => by
      rw [hvT] at hq
      have hq0 : q < 0 := by linarith
      have himg : (fun t => e (-a + t)) '' Icc q 0 = e '' Icc (-a + q) (-a) := by
        rw [image_shift_Icc, add_zero]
      have hmono : (c (e '' Icc (-L) (-a))).toReal ≤ (c (e '' Icc (-a + q) (-a))).toReal := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
        exact Set.image_mono (Icc_subset_Icc (by linarith) le_rfl)
      have hL : (c (e '' Icc (-L) (-a))).toReal = T := negBlockMass_eq hp haL hδ hE
      unfold massClock
      rw [ite_eq_right (not_le.2 hq0), himg]
      linarith)
    (fun q hq => by
      -- positivity just after `-a`
      have hmem : e (-a) ∈ offsetOuterAnnulus δ M :=
        offsetOuterAnnulus_two_mul_subset hδ (hE.2.2 (Or.inl ⟨by linarith, le_rfl⟩))
      have hopen : IsOpen (offsetOuterAnnulus δ M) := isOpen_ball.sdiff isClosed_closedBall
      have hcont : Continuous fun t : ℝ => e (-a + t) := e.continuous.comp (by fun_prop)
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), e (-a + t) ∈ offsetOuterAnnulus δ M :=
        hcont.continuousAt.eventually_mem (by simpa using hopen.mem_nhds hmem)
      obtain ⟨ε, hε, hεU⟩ := Metric.eventually_nhds_iff.1 hev
      set q' := min q (ε / 2) with hq'
      have hq'0 : 0 < q' := lt_min hq (half_pos hε)
      have hq'q : q' ≤ q := min_le_left _ _
      have hsub : e '' Icc (-a) (-a + q') ⊆ offsetOuterAnnulus δ M := by
        rintro _ ⟨t, ht, rfl⟩
        have h := hεU (y := t - -a) (by
          rw [Real.dist_eq, sub_zero, abs_lt]
          have : q' ≤ ε / 2 := min_le_right _ _
          constructor <;> linarith [ht.1, ht.2])
        simpa using h
      have himg : (fun t => e (-a + t)) '' Icc 0 q = e '' Icc (-a + 0) (-a + q) := by
        rw [image_shift_Icc]
      have hmass : c (e '' Icc (-a) (-a + q')) =
          ENNReal.ofReal (φ.symm (-a + q') - φ.symm (-a)) := by
        rw [hc, cappedMeasure_restrict_apply hsub, hp.measure_image (by linarith)]
      have hpos : 0 < φ.symm (-a + q') - φ.symm (-a) := by
        have := φ.symm.strictMono (show -a < -a + q' by linarith)
        linarith
      have hmono : (c (e '' Icc (-a) (-a + q'))).toReal ≤
          (c (e '' Icc (-a + 0) (-a + q))).toReal := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
        exact Set.image_mono (Icc_subset_Icc (by linarith) (by linarith))
      unfold massClock
      rw [ite_eq_left hq.le, himg]
      rw [hmass, ENNReal.toReal_ofReal hpos.le] at hmono
      linarith)
    hsT hs0
  unfold negBlockTime
  rw [hres, hv, blockShiftIso_apply]
  ring

end MatedCRT
