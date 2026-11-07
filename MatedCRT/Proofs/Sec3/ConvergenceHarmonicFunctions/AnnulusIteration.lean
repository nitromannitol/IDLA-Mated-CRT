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

/-- A finite sequence of ordered first-hit times witnesses the corresponding
crossing event. Indices decrease as time advances. -/
theorem pathShift_mem_annulusCrossingEvent_of_hit_schedule
    (A U B : ℕ → Set ℤ) (x : ℕ → ℤ) (t : ℕ → ℕ)
    (ht : Antitone t) (n : ℕ)
    (hstage : ∀ i < n,
      vHitTime (A i ∪ (U i)ᶜ) (pathShift (t (i + 1)) x) = (t i - t (i + 1) : ℕ) ∧
        x (t i) ∈ B i) :
    pathShift (t n) x ∈ annulusCrossingEvent A U B n := by
  induction n with
  | zero => simp [annulusCrossingEvent]
  | succ n ih =>
    have hle : t (n + 1) ≤ t n := ht (Nat.le_succ n)
    have hn := hstage n (Nat.lt_succ_self n)
    simp only [annulusCrossingEvent, Set.mem_iUnion, mem_ofPred_eq]
    refine ⟨t n - t (n + 1), hn.1, ?_, ?_⟩
    · simpa [pathShift, Nat.sub_add_cancel hle] using hn.2
    · have hshift : pathShift (t n - t (n + 1)) (pathShift (t (n + 1)) x) =
          pathShift (t n) x := by
        funext j
        simp only [pathShift]
        congr 1
        omega
      rw [hshift]
      exact ih (fun i hi => hstage i (Nat.lt_succ_of_lt hi))

/-- A first-hit schedule beginning at time zero forces all staged crossings. -/
theorem mem_annulusCrossingEvent_of_hit_schedule
    (A U B : ℕ → Set ℤ) (x : ℕ → ℤ) (t : ℕ → ℕ)
    (ht : Antitone t) (n : ℕ) (hzero : t n = 0)
    (hstage : ∀ i < n,
      vHitTime (A i ∪ (U i)ᶜ) (pathShift (t (i + 1)) x) = (t i - t (i + 1) : ℕ) ∧
        x (t i) ∈ B i) : x ∈ annulusCrossingEvent A U B n := by
  simpa [hzero] using pathShift_mem_annulusCrossingEvent_of_hit_schedule A U B x t ht n hstage

/-- If a path avoids a set on a finite interval and enters it at the end,
then its shifted first-hit time is the length of that interval. -/
theorem vHitTime_pathShift_eq_of_segment
    (D : Set ℤ) (x : ℕ → ℤ) {s t : ℕ} (hst : s ≤ t)
    (hbefore : ∀ j, s ≤ j → j < t → x j ∉ D) (hend : x t ∈ D) :
    vHitTime D (pathShift s x) = (t - s : ℕ) := by
  unfold vHitTime
  rw [vExitTime_eq_natCast_iff]
  constructor
  · intro h
    have hmem := (natCast_lt_vExitTime_iff.1 h) (t - s) le_rfl
    simp only [pathShift, Nat.sub_add_cancel hst, mem_compl_iff] at hmem
    exact hmem hend
  · intro j hj
    change x (j + s) ∉ D
    exact hbefore (j + s) (by omega) (by omega)

/-- Interval-wise avoidance and target membership provide the first-hit
schedule needed by the iterated crossing event. -/
theorem mem_annulusCrossingEvent_of_segments
    (A U B : ℕ → Set ℤ) (x : ℕ → ℤ) (t : ℕ → ℕ)
    (ht : Antitone t) (n : ℕ) (hzero : t n = 0)
    (hBA : ∀ i < n, B i ⊆ A i)
    (hend : ∀ i < n, x (t i) ∈ B i)
    (hbefore : ∀ i < n, ∀ j, t (i + 1) ≤ j → j < t i →
      x j ∉ A i ∧ x j ∈ U i) :
    x ∈ annulusCrossingEvent A U B n := by
  apply mem_annulusCrossingEvent_of_hit_schedule A U B x t ht n hzero
  intro i hi
  refine ⟨vHitTime_pathShift_eq_of_segment (A i ∪ (U i)ᶜ) x (ht (Nat.le_succ i)) ?_ ?_,
    hend i hi⟩
  · intro j hstart hstop
    have h := hbefore i hi j hstart hstop
    simp only [mem_union, mem_compl_iff, not_or, not_not]
    exact h
  · exact Or.inl (hBA i hi (hend i hi))

/-- Ordered finite first hits, together with survival in each region until
its target is reached, force the staged crossing event. -/
theorem mem_annulusCrossingEvent_of_ordered_firstHits
    (A U B : ℕ → Set ℤ) (x : ℕ → ℤ) (n : ℕ)
    (hfinite : ∀ i ≤ n, vHitTime (A i) x ≠ ⊤)
    (horder : ∀ i j, i ≤ j → j ≤ n → vHitTime (A j) x ≤ vHitTime (A i) x)
    (hBA : ∀ i ≤ n, B i ⊆ A i)
    (hend : ∀ i ≤ n, x (vHitTime (A i) x).toNat ∈ B i)
    (hstay : ∀ i ≤ n, ∀ j : ℕ, (j : ℕ∞) < vHitTime (A i) x → x j ∈ U i) :
    x ∈ annulusCrossingEvent A U B (n + 1) := by
  let t : ℕ → ℕ := fun i => if i ≤ n then (vHitTime (A i) x).toNat else 0
  have ht : Antitone t := by
    intro i j hij
    by_cases hj : j ≤ n
    · have hi : i ≤ n := hij.trans hj
      simp only [t, ite_eq_left hi, ite_eq_left hj]
      exact ENat.toNat_le_toNat (horder i j hij hj) (hfinite i hi)
    · simp [t, hj]
  have hz : t (n + 1) = 0 := by simp [t]
  apply mem_annulusCrossingEvent_of_segments A U B x t ht (n + 1) hz
  · intro i hi
    exact hBA i (by omega)
  · intro i hi
    have hi' : i ≤ n := by omega
    simpa [t, hi'] using hend i hi'
  · intro i hi j _ hstop
    have hi' : i ≤ n := by omega
    have hstop' : j < (vHitTime (A i) x).toNat := by simpa [t, hi'] using hstop
    have hj : (j : ℕ∞) < vHitTime (A i) x := by
      rw [← ENat.natCast_toNat (hfinite i hi')]
      exact_mod_cast hstop'
    exact ⟨(ConstantOrderDiv.lt_vExitTime_iff'.1 hj) j le_rfl, hstay i hi' j hj⟩

end MatedCRT
