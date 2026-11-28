import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraSteps
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The summation step of Shimura's theorem

From the cell bounds `μ (cellEvent n i) ≤ C / n` and the occupancy bounds
`μ (firstCellEvent n k ∩ cellEvent n (k + j)) ≥ c / (j - 1) * μ (firstCellEvent n k)` this file proves that the
unit event `UnitOppositeSideMin` is null (`shimuraSummation_holds`).

The events `cellEvent n k` are closed subsets of the path space `C(ℝ, ℝ × ℝ)`, hence measurable. A witness of the
unit event lies in one of the first `n` cells, hence in one of the disjoint events `firstCellEvent n k` with
`k ≤ n`. The events with `μ (firstCellEvent n k) < 2 / n ^ 2` contribute at most `2 / n`. For the others the
occupancy bound, summed over `1 + 6 log n < j ≤ n`, bounds `μ (firstCellEvent n k)` by the occupation of the later
cells, and these sum to at most `2 C` by disjointness of the events `firstCellEvent n k`. The harmonic sum
`∑_{1 + 6 log n < j ≤ n} 1 / (j - 1)` tends to infinity, which gives the nullity.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open MatedCRTHarmonic.MatedCRT (Path2)
open scoped NNReal ENNReal

namespace MatedCRT.PeanosphereTriplePoints

/-! ### Measurability of the cell events -/

theorem isClosed_exists_min {f : ℝ × ℝ → ℝ} (hf : Continuous f) (a b c d : ℝ) :
    IsClosed {p : Path2 | ∃ s ∈ Icc a b, ∀ u ∈ Icc c d, f (p s) ≤ f (p u)} := by
  have hev : Continuous fun q : Path2 × ℝ => q.1 q.2 := ContinuousEval.continuous_eval
  have hG : IsClosed {q : Path2 × Icc a b | ∀ u ∈ Icc c d, f (q.1 (q.2 : ℝ)) ≤ f (q.1 u)} := by
    have : {q : Path2 × Icc a b | ∀ u ∈ Icc c d, f (q.1 (q.2 : ℝ)) ≤ f (q.1 u)} =
        ⋂ u ∈ Icc c d, {q : Path2 × Icc a b | f (q.1 (q.2 : ℝ)) ≤ f (q.1 u)} := by
      ext q
      simp only [mem_ofPred_eq, mem_iInter]
    rw [this]
    refine isClosed_biInter fun u _ => isClosed_le ?_ ?_
    · exact hf.comp (hev.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    · exact hf.comp (hev.comp (continuous_fst.prodMk continuous_const))
  have himg : IsClosed (Prod.fst ''
      {q : Path2 × Icc a b | ∀ u ∈ Icc c d, f (q.1 (q.2 : ℝ)) ≤ f (q.1 u)}) :=
    isClosedMap_fst_of_compactSpace _ hG
  have : {p : Path2 | ∃ s ∈ Icc a b, ∀ u ∈ Icc c d, f (p s) ≤ f (p u)} =
      Prod.fst '' {q : Path2 × Icc a b | ∀ u ∈ Icc c d, f (q.1 (q.2 : ℝ)) ≤ f (q.1 u)} := by
    ext p
    constructor
    · rintro ⟨s, hs, h⟩
      exact ⟨(p, ⟨s, hs⟩), h, rfl⟩
    · rintro ⟨⟨p', s⟩, h, rfl⟩
      exact ⟨s.1, s.2, h⟩
  rw [this]
  exact himg

theorem measurableSet_cellEvent (n k : ℕ) : MeasurableSet (cellEvent n k) := by
  have h1 := isClosed_exists_min (f := fun x : ℝ × ℝ => x.1) continuous_fst
    (((k : ℝ) - 1) / n) ((k : ℝ) / n) ((k : ℝ) / n - 2) (((k : ℝ) - 1) / n)
  have h2 := isClosed_exists_min (f := fun x : ℝ × ℝ => x.2) continuous_snd
    (((k : ℝ) - 1) / n) ((k : ℝ) / n) ((k : ℝ) / n) (((k : ℝ) - 1) / n + 2)
  exact (h1.inter h2).measurableSet

theorem measurableSet_firstCellEvent (n k : ℕ) : MeasurableSet (firstCellEvent n k) :=
  (measurableSet_cellEvent n k).diff
    (Finset.measurableSet_biUnion _ fun i _ => measurableSet_cellEvent n i)

theorem firstCellEvent_subset (n k : ℕ) : firstCellEvent n k ⊆ cellEvent n k :=
  fun _ hp => hp.1

theorem disjoint_firstCellEvent {n k k' : ℕ} (hk : 1 ≤ k) (h : k < k') :
    Disjoint (firstCellEvent n k) (firstCellEvent n k') :=
  Set.disjoint_left.2 fun _ hp hp' =>
    hp'.2 (mem_iUnion₂.2 ⟨k, Finset.mem_Ico.2 ⟨hk, h⟩, hp.1⟩)

theorem sum_firstCell_inter_le (μ : Measure Path2) (n i : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, μ (firstCellEvent n k ∩ cellEvent n i) ≤ μ (cellEvent n i) := by
  have hdisj : (↑(Finset.Icc 1 n) : Set ℕ).PairwiseDisjoint
      fun k => firstCellEvent n k ∩ cellEvent n i := by
    intro k hk k' hk' hne
    have hk1 := (Finset.mem_Icc.1 hk).1
    have hk1' := (Finset.mem_Icc.1 hk').1
    rcases lt_or_gt_of_ne hne with h | h
    · exact (disjoint_firstCellEvent hk1 h).mono inter_subset_left inter_subset_left
    · exact ((disjoint_firstCellEvent hk1' h).mono inter_subset_left inter_subset_left).symm
  rw [← measure_biUnion_finset hdisj fun k _ =>
    (measurableSet_firstCellEvent n k).inter (measurableSet_cellEvent n i)]
  exact measure_mono (iUnion₂_subset fun k _ => inter_subset_right)

/-! ### The unit event and the first occupied cell -/

theorem unit_subset_cells {n : ℕ} (hn : 1 ≤ n) :
    {p : Path2 | UnitOppositeSideMin (fun t => (p t).1) (fun t => (p t).2)} ⊆
      ⋃ k ∈ Finset.Icc 1 n, cellEvent n k := by
  rintro p ⟨t, ht, hX, hY⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have htn : 0 ≤ t * n := mul_nonneg ht.1 hn'.le
  have hk1 : 1 ≤ max 1 ⌈t * n⌉₊ := le_max_left _ _
  have hkn : max 1 ⌈t * n⌉₊ ≤ n := by
    refine max_le hn (Nat.ceil_le.2 ?_)
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2) hn'.le]
  have h1 : t ≤ ((max 1 ⌈t * n⌉₊ : ℕ) : ℝ) / n := by
    rw [le_div_iff₀ hn']
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have h2 : (((max 1 ⌈t * n⌉₊ : ℕ) : ℝ) - 1) / n ≤ t := by
    rw [div_le_iff₀ hn']
    by_cases hc : 1 ≤ ⌈t * n⌉₊
    · rw [max_eq_right hc]
      linarith [Nat.ceil_lt_add_one htn]
    · rw [max_eq_left (by omega)]
      push_cast
      linarith
  refine mem_iUnion₂.2 ⟨max 1 ⌈t * n⌉₊, Finset.mem_Icc.2 ⟨hk1, hkn⟩, ?_⟩
  refine ⟨⟨t, ⟨h2, h1⟩, fun u hu => ?_⟩, ⟨t, ⟨h2, h1⟩, fun u hu => ?_⟩⟩
  · exact hX u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · exact hY u ⟨by linarith [hu.1], by linarith [hu.2]⟩

theorem exists_firstCell {n : ℕ} {p : Path2} :
    ∀ k : ℕ, 1 ≤ k → p ∈ cellEvent n k → ∃ i, 1 ≤ i ∧ i ≤ k ∧ p ∈ firstCellEvent n i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hp
    by_cases hfirst : p ∈ firstCellEvent n k
    · exact ⟨k, hk, le_rfl, hfirst⟩
    · have hex : ∃ i ∈ Finset.Ico 1 k, p ∈ cellEvent n i := by
        by_contra hno
        refine hfirst ⟨hp, fun hmem => hno ?_⟩
        obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 hmem
        exact ⟨i, hi, hpi⟩
      obtain ⟨i, hi, hpi⟩ := hex
      have hi' := Finset.mem_Ico.1 hi
      obtain ⟨i', h1, h2, h3⟩ := ih i hi'.2 hi'.1 hpi
      exact ⟨i', h1, h2.trans hi'.2.le, h3⟩

/-! ### The harmonic sum -/

/-- The indices `j` with `1 + 6 log n < j ≤ n`. -/
noncomputable def Jn (n : ℕ) : Finset ℕ := Finset.Ioc ⌊1 + 6 * Real.log n⌋₊ n

/-- The sum `∑_{1 + 6 log n < j ≤ n} 1 / (j - 1)`. -/
noncomputable def hsum (n : ℕ) : ℝ := ∑ j ∈ Jn n, 1 / ((j : ℝ) - 1)

theorem zero_le_one_add_six_log {n : ℕ} (hn : 1 ≤ n) : 0 ≤ 1 + 6 * Real.log n := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  linarith

theorem mem_Jn {n j : ℕ} (hn : 1 ≤ n) : j ∈ Jn n ↔ 1 + 6 * Real.log n < j ∧ j ≤ n := by
  rw [Jn, Finset.mem_Ioc, Nat.floor_lt (zero_le_one_add_six_log hn)]

/-- The partial harmonic sums. -/
noncomputable def Hh (n : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 n, ((j : ℕ) : ℝ)⁻¹

theorem Icc_one_eq_Ioc (x : ℕ) : Finset.Icc 1 x = Finset.Ioc 0 x := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem harmonic_cast (n : ℕ) : ((harmonic n : ℚ) : ℝ) = Hh n := by
  simp [harmonic_eq_sum_Icc, Hh]

theorem log_le_Hh (n : ℕ) : Real.log n ≤ Hh n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Hh]
  · have h := log_add_one_le_harmonic n
    rw [harmonic_cast] at h
    have h2 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
    exact h2.trans h

theorem Hh_le (n : ℕ) : Hh n ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  rwa [harmonic_cast] at h

theorem hsum_ge {n : ℕ} (hn : 122 ≤ n) : Real.log n / 2 - 12 ≤ hsum n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (122 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlog12 : Real.log 12 ≤ 11 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 12 by norm_num)
    linarith
  have hb1 : Real.log n ≤ n / 12 + 10 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / 12 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    linarith
  have hfl : 1 + 6 * Real.log n ≤ n := by linarith
  have hb2 : Real.log (1 + 6 * Real.log n) ≤ Real.log n / 2 + 11 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + 6 * Real.log n) / 12 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    linarith
  have hm1 : 1 ≤ ⌊1 + 6 * Real.log n⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hmx : (⌊1 + 6 * Real.log n⌋₊ : ℝ) ≤ 1 + 6 * Real.log n :=
    Nat.floor_le (zero_le_one_add_six_log hn1)
  have hmn : ⌊1 + 6 * Real.log n⌋₊ ≤ n := Nat.floor_le_of_le hfl
  have hle : ∑ j ∈ Finset.Ioc ⌊1 + 6 * Real.log n⌋₊ n, ((j : ℕ) : ℝ)⁻¹ ≤ hsum n := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_Ioc.1 hj
    have h2 : (2 : ℝ) ≤ j := by exact_mod_cast (by omega : 2 ≤ j)
    rw [← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hdiff : ∑ j ∈ Finset.Ioc ⌊1 + 6 * Real.log n⌋₊ n, ((j : ℕ) : ℝ)⁻¹ =
      Hh n - Hh ⌊1 + 6 * Real.log n⌋₊ := by
    have := Finset.sum_Ioc_consecutive (fun j : ℕ => ((j : ℕ) : ℝ)⁻¹)
      (Nat.zero_le ⌊1 + 6 * Real.log n⌋₊) hmn
    rw [Hh, Hh, Icc_one_eq_Ioc, Icc_one_eq_Ioc]
    linarith
  have hlogm : Real.log ⌊1 + 6 * Real.log n⌋₊ ≤ Real.log (1 + 6 * Real.log n) :=
    Real.log_le_log (by exact_mod_cast hm1) hmx
  have hHm := Hh_le ⌊1 + 6 * Real.log n⌋₊
  have hHn := log_le_Hh n
  have : hsum n = ∑ j ∈ Finset.Ioc ⌊1 + 6 * Real.log n⌋₊ n, 1 / ((j : ℝ) - 1) := rfl
  linarith

theorem tendsto_hsum : Tendsto hsum atTop atTop := by
  have hlow : Tendsto (fun n : ℕ => Real.log n / 2 - 12) atTop atTop := by
    have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (show (0 : ℝ) < 2 by norm_num)
    have h2 := tendsto_atTop_add_const_right atTop (-12 : ℝ) h
    simpa [sub_eq_add_neg] using h2
  exact tendsto_atTop_mono' atTop (eventually_atTop.2 ⟨122, fun n hn => hsum_ge hn⟩) hlow

/-! ### The summation bound at a fixed mesh -/

theorem measure_unit_le (μ : Measure Path2) {C c : ℝ} (hc : 0 < c) {n : ℕ}
    (hn : 1 ≤ n)
    (hcell : ∀ i : ℕ, 1 ≤ i → i ≤ 2 * n → μ (cellEvent n i) ≤ ENNReal.ofReal (C / n))
    (hocc : ∀ k j : ℕ, 1 ≤ k → k ≤ n →
      ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k) →
        1 + 6 * Real.log n < j → k + j ≤ 2 * n →
          ENNReal.ofReal (c / ((j : ℝ) - 1)) * μ (firstCellEvent n k) ≤
            μ (firstCellEvent n k ∩ cellEvent n (k + j)))
    (hpos : 0 < hsum n) :
    μ {p : Path2 | UnitOppositeSideMin (fun t => (p t).1) (fun t => (p t).2)} ≤
      ENNReal.ofReal (2 / n) + ENNReal.ofReal (2 * C / (c * hsum n)) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hunit : μ {p : Path2 | UnitOppositeSideMin (fun t => (p t).1) (fun t => (p t).2)} ≤
      ∑ k ∈ Finset.Icc 1 n, μ (firstCellEvent n k) := by
    refine (measure_mono ?_).trans (measure_biUnion_finset_le _ _)
    intro p hp
    obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.1 (unit_subset_cells hn hp)
    obtain ⟨i, hi1, hik, hpi⟩ := exists_firstCell k (Finset.mem_Icc.1 hk).1 hpk
    exact mem_iUnion₂.2 ⟨i, Finset.mem_Icc.2 ⟨hi1, hik.trans (Finset.mem_Icc.1 hk).2⟩, hpi⟩
  have hsplit : ∑ k ∈ Finset.Icc 1 n, μ (firstCellEvent n k) =
      ∑ k ∈ (Finset.Icc 1 n).filter
        (fun k => ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k)),
        μ (firstCellEvent n k) +
      ∑ k ∈ (Finset.Icc 1 n).filter
        (fun k => ¬ ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k)),
        μ (firstCellEvent n k) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hbad : ∑ k ∈ (Finset.Icc 1 n).filter
        (fun k => ¬ ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k)),
        μ (firstCellEvent n k) ≤ ENNReal.ofReal (2 / n) := by
    have hcard : ((Finset.Icc 1 n).filter
        (fun k => ¬ ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k))).card ≤ n :=
      (Finset.card_filter_le _ _).trans (by simp)
    calc _ ≤ ((Finset.Icc 1 n).filter
          (fun k => ¬ ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k))).card •
          ENNReal.ofReal (2 / (n : ℝ) ^ 2) :=
          Finset.sum_le_card_nsmul _ _ _ fun k hk => (not_le.1 (Finset.mem_filter.1 hk).2).le
      _ ≤ n • ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          exact mul_le_mul' (by exact_mod_cast hcard) le_rfl
      _ = ENNReal.ofReal (2 / n) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          field_simp
  have hH0 : (0 : ℝ) < c * hsum n := mul_pos hc hpos
  have hJsum : ENNReal.ofReal (c * hsum n) =
      ∑ j ∈ Jn n, ENNReal.ofReal (c / ((j : ℝ) - 1)) := by
    rw [hsum, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_one_div]
    · intro j hj
      have hj' := (mem_Jn hn).1 hj
      have hlog := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
      have : (0 : ℝ) < (j : ℝ) - 1 := by linarith [hj'.1]
      exact mul_nonneg hc.le (one_div_nonneg.2 this.le)
  have hgood : (∑ k ∈ (Finset.Icc 1 n).filter
        (fun k => ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k)),
        μ (firstCellEvent n k)) * ENNReal.ofReal (c * hsum n) ≤ ENNReal.ofReal (2 * C) := by
    calc (∑ k ∈ (Finset.Icc 1 n).filter
          (fun k => ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k)),
          μ (firstCellEvent n k)) * ENNReal.ofReal (c * hsum n)
        = ∑ k ∈ (Finset.Icc 1 n).filter
          (fun k => ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k)),
          ENNReal.ofReal (c * hsum n) * μ (firstCellEvent n k) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ ≤ ∑ k ∈ (Finset.Icc 1 n).filter
          (fun k => ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k)),
          ∑ j ∈ Jn n, μ (firstCellEvent n k ∩ cellEvent n (k + j)) :=
          Finset.sum_le_sum fun k hk => by
            rw [hJsum, Finset.sum_mul]
            refine Finset.sum_le_sum fun j hj => ?_
            have hk' := Finset.mem_filter.1 hk
            have hk1 := Finset.mem_Icc.1 hk'.1
            have hj' := (mem_Jn hn).1 hj
            have hjn : j ≤ n := hj'.2
            have hkn : k ≤ n := hk1.2
            exact hocc k j hk1.1 hkn hk'.2 hj'.1 (by omega)
      _ ≤ ∑ k ∈ (Finset.Icc 1 n).filter
          (fun k => ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k)),
          ∑ i ∈ Finset.Icc 1 (2 * n), μ (firstCellEvent n k ∩ cellEvent n i) :=
          Finset.sum_le_sum fun k hk => by
            have hk1 := Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1
            calc ∑ j ∈ Jn n, μ (firstCellEvent n k ∩ cellEvent n (k + j))
                = ∑ i ∈ (Jn n).image (fun j => k + j), μ (firstCellEvent n k ∩ cellEvent n i) :=
                (Finset.sum_image (f := fun i => μ (firstCellEvent n k ∩ cellEvent n i))
                  (s := Jn n) (g := fun j => k + j) (fun a _ b _ h => by simpa using h)).symm
              _ ≤ _ := Finset.sum_le_sum_of_subset (by
                  intro i hi
                  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
                  have hj' := (mem_Jn hn).1 hj
                  have hjn : j ≤ n := hj'.2
                  have hk1' : 1 ≤ k := hk1.1
                  have hkn : k ≤ n := hk1.2
                  show k + j ∈ Finset.Icc 1 (2 * n)
                  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      _ ≤ ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 (2 * n),
          μ (firstCellEvent n k ∩ cellEvent n i) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ∑ i ∈ Finset.Icc 1 (2 * n), ∑ k ∈ Finset.Icc 1 n,
          μ (firstCellEvent n k ∩ cellEvent n i) := Finset.sum_comm
      _ ≤ ∑ i ∈ Finset.Icc 1 (2 * n), μ (cellEvent n i) :=
          Finset.sum_le_sum fun i _ => sum_firstCell_inter_le μ n i
      _ ≤ ∑ i ∈ Finset.Icc 1 (2 * n), ENNReal.ofReal (C / n) :=
          Finset.sum_le_sum fun i hi =>
            hcell i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2
      _ = ENNReal.ofReal (2 * C) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          push_cast
          field_simp
  have hgood' : ∑ k ∈ (Finset.Icc 1 n).filter
        (fun k => ENNReal.ofReal (2 / (n : ℝ) ^ 2) ≤ μ (firstCellEvent n k)),
        μ (firstCellEvent n k) ≤ ENNReal.ofReal (2 * C / (c * hsum n)) := by
    rw [ENNReal.ofReal_div_of_pos hH0]
    exact (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hH0).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2 hgood
  calc _ ≤ _ := hunit
    _ = _ := hsplit
    _ ≤ ENNReal.ofReal (2 * C / (c * hsum n)) + ENNReal.ofReal (2 / n) := add_le_add hgood' hbad
    _ = _ := add_comm _ _

/-! ### The summation step -/

/-- The cell bounds and the occupation bound make the unit event null. -/
theorem shimuraSummation_holds (γ : ℝ) : ShimuraSummation γ := by
  intro hcell hocc μ hμ
  obtain ⟨C, N, hC⟩ := hcell
  obtain ⟨c, hc, N', hO⟩ := hocc
  have hC0 : 0 ≤ max C 0 := le_max_right C 0
  have hev : ∀ᶠ n : ℕ in atTop, μ {p : Path2 | UnitOppositeSideMin (fun t => (p t).1)
      (fun t => (p t).2)} ≤ ENNReal.ofReal (2 / n + 2 * max C 0 / (c * hsum n)) := by
    filter_upwards [eventually_ge_atTop (max (max N N') 122),
      tendsto_hsum.eventually_gt_atTop 0] with n hn hpos
    have hN : N ≤ n := (le_max_left N N').trans ((le_max_left _ _).trans hn)
    have hN' : N' ≤ n := (le_max_right N N').trans ((le_max_left _ _).trans hn)
    have h122 : 1 ≤ n := by
      have := (le_max_right (max N N') 122).trans hn
      omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast h122
    have hcell' : ∀ i : ℕ, 1 ≤ i → i ≤ 2 * n →
        μ (cellEvent n i) ≤ ENNReal.ofReal (max C 0 / n) := fun i h1 h2 =>
      (hC μ hμ n hN i h1 h2).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left C 0) hnR.le))
    have hbound := measure_unit_le μ hc h122 hcell'
      (fun k j hk1 hkn h2 hj hkj => hO μ hμ n hN' k j hk1 hkn h2 hj hkj) hpos
    rwa [← ENNReal.ofReal_add (by positivity)
      (div_nonneg (mul_nonneg (by norm_num) hC0) (mul_pos hc hpos).le)] at hbound
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (2 / n + 2 * max C 0 / (c * hsum n)))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => 2 * max C 0 / (c * hsum n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_hsum.const_mul_atTop hc)
    have h1 : Tendsto (fun n : ℕ => (2 : ℝ) / n + 2 * max C 0 / (c * hsum n)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).add h2
      simpa using this
    simpa using ENNReal.tendsto_ofReal h1
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto hlim hev)

end MatedCRT.PeanosphereTriplePoints
