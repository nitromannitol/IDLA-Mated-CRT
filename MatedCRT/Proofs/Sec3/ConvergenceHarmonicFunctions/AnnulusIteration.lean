import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusDisconnection

/-! # Iteration of annulus crossing estimates -/

namespace MatedCRT

open Set MeasureTheory
open scoped ENNReal

/-- The indicator for reaching the successive target sets before leaving the
corresponding regions. Stages are indexed in decreasing order, so the restart
vertex at stage `n + 1` belongs to the starting set of stage `n`. -/
noncomputable def annulusCrossings (A U B : ℕ → Set ℤ) : ℕ → (ℕ → ℤ) → ℝ≥0∞
  | 0, _ => 1
  | n + 1, x => ∑' k : ℕ,
      {x | vHitTime (A n ∪ (U n)ᶜ) x = k}.indicator
        (fun x => (B n).indicator 1 (x k) *
          annulusCrossings A U B n (pathShift k x)) x

/-- The event that the walk completes each of the specified finite stages. -/
def annulusCrossingEvent (A U B : ℕ → Set ℤ) : ℕ → Set (ℕ → ℤ)
  | 0 => Set.univ
  | n + 1 => ⋃ k : ℕ, {x | vHitTime (A n ∪ (U n)ᶜ) x = k ∧ x k ∈ B n ∧
      pathShift k x ∈ annulusCrossingEvent A U B n}

/-- The integral formulation agrees pointwise with the crossing event. -/
theorem annulusCrossings_eq_indicator (A U B : ℕ → Set ℤ) (n : ℕ) :
    annulusCrossings A U B n = (annulusCrossingEvent A U B n).indicator 1 := by
  classical
  induction n with
  | zero => funext x; simp [annulusCrossings, annulusCrossingEvent]
  | succ n ih =>
    funext x
    simp only [annulusCrossings, annulusCrossingEvent]
    by_cases hx : ∃ k : ℕ, vHitTime (A n ∪ (U n)ᶜ) x = k ∧ x k ∈ B n ∧
        pathShift k x ∈ annulusCrossingEvent A U B n
    · obtain ⟨k, hk, hb, hc⟩ := hx
      rw [tsum_eq_single k]
      · simp [hk, hb, ih, hc, Set.indicator]
      · intro j hj
        have hne : vHitTime (A n ∪ (U n)ᶜ) x ≠ j := by
          intro hj'
          apply hj
          have he := hj'.symm.trans hk
          exact_mod_cast he
        simp [hne, Set.indicator]
    · have hnot : x ∉ ⋃ k : ℕ, {x | vHitTime (A n ∪ (U n)ᶜ) x = k ∧ x k ∈ B n ∧
          pathShift k x ∈ annulusCrossingEvent A U B n} := by
        simpa only [Set.mem_iUnion, mem_ofPred_eq] using hx
      rw [Set.indicator_of_notMem hnot]
      apply ENNReal.tsum_eq_zero.2
      intro k
      by_cases hk : vHitTime (A n ∪ (U n)ᶜ) x = k
      · by_cases hb : x k ∈ B n
        · have hc : pathShift k x ∉ annulusCrossingEvent A U B n :=
            fun hc => hx ⟨k, hk, hb, hc⟩
          simp [hk, hb, ih, hc, Set.indicator]
        · simp [hk, hb, Set.indicator]
      · simp [hk, Set.indicator]

/-- Crossing events are measurable. -/
theorem measurableSet_annulusCrossingEvent (A U B : ℕ → Set ℤ) (n : ℕ) :
    MeasurableSet (annulusCrossingEvent A U B n) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    simp only [annulusCrossingEvent]
    exact MeasurableSet.iUnion fun k => (measurableSet_vHitTime_eq _ k).inter
      (((Set.to_countable (B n)).measurableSet.preimage (measurable_pi_apply k)).inter
        (ih.preimage (measurable_pathShift k)))

/-- The finite-stage crossing indicator is measurable in the walk. -/
theorem measurable_annulusCrossings (A U B : ℕ → Set ℤ) (n : ℕ) :
    Measurable (annulusCrossings A U B n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [annulusCrossings]
    apply Measurable.tsum
    intro k
    exact (((measurable_of_countable ((B n).indicator (1 : ℤ → ℝ≥0∞))).comp
      (measurable_pi_apply k)).mul (ih.comp (measurable_pathShift k))).indicator
      (measurableSet_vHitTime_eq _ k)

/-- If each annulus crossing has probability at most `q`, the probability
of crossing all stages is at most the corresponding power of `q`. -/
theorem lintegral_annulusCrossings_le_pow
    (m : ℤ → ℤ → ℕ) (A U B S : ℕ → Set ℤ) (q : ℝ≥0∞)
    (hnext : ∀ n, B (n + 1) ⊆ S n)
    (hstage : ∀ n v, v ∈ S n →
      srwLaw m v (⋃ k : ℕ, {x | vHitTime (A n ∪ (U n)ᶜ) x = k ∧ x k ∈ B n}) ≤ q) :
    ∀ n v, v ∈ S n →
      (∫⁻ x, annulusCrossings A U B (n + 1) x ∂srwLaw m v) ≤ q ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro v hv
    simp only [annulusCrossings]
    rw [lintegral_tsum fun k => by
      exact ((((measurable_of_countable ((B 0).indicator (1 : ℤ → ℝ≥0∞))).comp
        (measurable_pi_apply k)).mul (measurable_const.comp (measurable_pathShift k))).indicator
        (measurableSet_vHitTime_eq _ k)).aemeasurable]
    calc
      _ ≤ srwLaw m v (⋃ k : ℕ, {x | vHitTime (A 0 ∪ (U 0)ᶜ) x = k ∧ x k ∈ B 0}) * 1 :=
        tsum_lintegral_hitTime_indicator_continuation_le_mul m _ (B 0) measurable_const v 1
          (fun b hb => by simp)
      _ ≤ q := by simpa using hstage 0 v hv
      _ = q ^ (0 + 1) := by simp
  | succ n ih =>
    intro v hv
    simp only [annulusCrossings]
    rw [lintegral_tsum fun k => by
      exact ((((measurable_of_countable ((B (n + 1)).indicator (1 : ℤ → ℝ≥0∞))).comp
        (measurable_pi_apply k)).mul ((measurable_annulusCrossings A U B (n + 1)).comp
          (measurable_pathShift k))).indicator (measurableSet_vHitTime_eq _ k)).aemeasurable]
    calc
      _ ≤ srwLaw m v (⋃ k : ℕ, {x | vHitTime (A (n + 1) ∪ (U (n + 1))ᶜ) x = k ∧
            x k ∈ B (n + 1)}) * q ^ (n + 1) :=
        tsum_lintegral_hitTime_indicator_continuation_le_mul m _ (B (n + 1))
          (measurable_annulusCrossings A U B (n + 1)) v (q ^ (n + 1))
          (fun b hb => ih b (hnext n hb))
      _ ≤ q * q ^ (n + 1) := by gcongr; exact hstage (n + 1) v hv
      _ = q ^ (n + 1 + 1) := by simp only [pow_succ]; ac_rfl

/-- The finite-stage crossing event has geometrically decaying probability. -/
theorem measure_annulusCrossingEvent_le_pow
    (m : ℤ → ℤ → ℕ) (A U B S : ℕ → Set ℤ) (q : ℝ≥0∞)
    (hnext : ∀ n, B (n + 1) ⊆ S n)
    (hstage : ∀ n v, v ∈ S n →
      srwLaw m v (⋃ k : ℕ, {x | vHitTime (A n ∪ (U n)ᶜ) x = k ∧ x k ∈ B n}) ≤ q)
    (n : ℕ) (v : ℤ) (hv : v ∈ S n) :
    srwLaw m v (annulusCrossingEvent A U B (n + 1)) ≤ q ^ (n + 1) := by
  rw [← lintegral_indicator_one (measurableSet_annulusCrossingEvent A U B (n + 1)),
    ← annulusCrossings_eq_indicator]
  exact lintegral_annulusCrossings_le_pow m A U B S q hnext hstage n v hv

/-- Simultaneous disconnection estimates give a geometric bound on the
probability of completing the specified annulus crossings. The graph walks
in `hgeom` are the deterministic separation paths. -/
theorem measure_annulusCrossingEvent_le_of_disconnection
    (m : ℤ → ℤ → ℕ) (A I U B S : ℕ → Set ℤ) (p : ℝ) (hp : 0 ≤ p)
    (hnext : ∀ n, B (n + 1) ⊆ S n) (hBA : ∀ n, B n ⊆ A n)
    (hgeom : ∀ n, ∃ y a, y ∈ I n ∧ a ∈ A n ∧
      ∃ w : (adjGraph m).Walk y a, ∀ u ∈ w.support, u ∉ U n)
    (hdisc : ∀ n v, v ∈ S n → ENNReal.ofReal p ≤ srwLaw m v
      {x | ∀ y ∈ I n, walkDisconnectsBeforeHit m (A n) y x})
    (n : ℕ) (v : ℤ) (hv : v ∈ S n) :
    srwLaw m v (annulusCrossingEvent A U B (n + 1)) ≤
      ENNReal.ofReal (1 - p) ^ (n + 1) := by
  apply measure_annulusCrossingEvent_le_pow m A U B S _ hnext _ n v hv
  intro j b hb
  obtain ⟨y, a, hy, ha, w, hw⟩ := hgeom j
  exact (measure_mono (hit_target_before_exit_subset_stay (A j) (U j) (B j) (hBA j))).trans
    (srwLaw_stay_le_of_annulus_disconnection hy ha w hw hp (hdisc j b hb))

end MatedCRT
