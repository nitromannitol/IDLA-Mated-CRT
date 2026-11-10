import MatedCRT.FirstPass.S6r.OneTest.ParamOneTest

/-!
# The concrete test exit time of PRO step 8 and the hone of `exitQ_le_pow` (fp-S6r-one-test-concrete)

For the parameter `q = (R, x)` the test ball is `D = B_{R/4}(x)`, its discrete interior is
`I(D) = interiorCellVertices ε η D` (the cells meeting `D` but not `∂D`), and `σ_D` is the first exit time of the walk
from `I(D)` (Armitage–Gardiner: exit time of a set; Armstrong–Kuusi–Mourrat: discrete interior of a ball).

* `ballExitSigma` is `σ_D` as the ℕ-valued count bound of `occCount` (`toNat` convention of
  `firstMoment_occCount_fm` and `secondMoment_occCount`; on a non-exiting path it is `0`, a null set under the
  finite-exit-time hypothesis).
* `testEndExit` is the test end `L = T + vExitTime I(D_ρ)(post-T path)` with values in `ℕ∞`. It replaces
  `testEndParam` (ParamOneTest.lean), which is NOT a stopping time for the `toNat`-valued `σ`: on a non-exiting path
  `testEndParam = T`, so `{L ≤ n}` is not `𝓕_n`-measurable. `testEndExit` is a stopping time
  (`isStoppingTime_testEndExit`) and covers the count window (`testEndExit_cover`).
* Proved here: measurability of `σ_D` in the parameter and the path (`measurable_ballExitSigma`), that `testEndExit`
  is a stopping time, the coverage, the integrability of the count `V` from the named finite-exit-moment hypotheses,
  and the hone family `hone_exitQ_concrete` with the named PRO step 8 moment side conditions `hm`, `hRr`, `hstep1`,
  `hstep2`.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Window

open Lemma68WalkBridge

section BallExit

variable (ε : ℝ) (η : ℝ → ℂ)

/-- The discrete interior `I(D)` of the test ball `D = B_{R/4}(x)` for the parameter `q = (R, x)`. -/
noncomputable def ballInterior (q : ℝ × ℂ) : Set ℤ :=
  interiorCellVertices ε η (ball q.2 (q.1 / 4))

/-- The exit time `σ_D` of the discrete interior, as the ℕ-valued count bound (`toNat` convention). -/
noncomputable def ballExitSigma (q : ℝ × ℂ) (w : ℕ → ℤ) : ℕ :=
  (vExitTime (ballInterior ε η q) w).toNat

/-- The ℕ∞-valued test end `L = T + vExitTime I(D_ρ)(post-T path)`. -/
noncomputable def testEndExit (ρ : (ℕ → ℤ) → ℝ × ℂ) (T : (ℕ → ℤ) → ℕ∞) (w : ℕ → ℤ) : ℕ∞ :=
  T w + vExitTime (ballInterior ε η (ρ w)) (postTimePath (fun n w => w n) T w)

theorem mem_cellVertices_ball_iff (k : ℤ) (c : ℂ) (r : ℝ) :
    k ∈ cellVertices ε η (ball c r) ↔ ∃ t ∈ Icc (ε * (k - 1)) (ε * k), dist (η t) c < r := by
  simp only [cellVertices, cell, mem_ofPred_eq, Set.Nonempty]
  constructor
  · rintro ⟨x, ⟨⟨t, ht, rfl⟩, hx⟩⟩
    exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨η t, ⟨⟨t, ht, rfl⟩, h⟩⟩

theorem mem_cellVertices_frontier_ball_iff (k : ℤ) (c : ℂ) (r : ℝ) :
    k ∈ cellVertices ε η (frontier (ball c r)) ↔
      0 < r ∧ ∃ t ∈ Icc (ε * (k - 1)) (ε * k), dist (η t) c = r := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · rw [Metric.ball_eq_empty.2 hr.le, frontier_empty]
    simp [cellVertices, not_lt.2 hr.le]
  · simp [cellVertices]
  · rw [frontier_ball c hr.ne']
    simp only [cellVertices, cell, mem_ofPred_eq, Set.Nonempty, hr, true_and]
    constructor
    · rintro ⟨x, ⟨⟨t, ht, rfl⟩, hx⟩⟩
      exact ⟨t, ht, hx⟩
    · rintro ⟨t, ht, h⟩
      exact ⟨η t, ⟨⟨t, ht, rfl⟩, h⟩⟩

/-- The zero set of a continuous function on a compact interval, through the extreme values: a continuous function
on `[a, b]` has a zero iff its infimum is `≤ 0 ≤` its supremum (intermediate value theorem). -/
theorem exists_zero_iff_sInf_sSup {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) :
    (∃ t ∈ Icc a b, g t = 0) ↔ sInf (g '' Icc a b) ≤ 0 ∧ 0 ≤ sSup (g '' Icc a b) := by
  have hcpt : IsCompact (g '' Icc a b) := isCompact_Icc.image_of_continuousOn hg
  have hne : (g '' Icc a b).Nonempty := ⟨g a, a, ⟨le_rfl, hab⟩, rfl⟩
  have hpre : IsPreconnected (g '' Icc a b) := isPreconnected_Icc.image g hg
  constructor
  · rintro ⟨t, ht, h0⟩
    have h1 : sInf (g '' Icc a b) ≤ g t := csInf_le hcpt.bddBelow ⟨t, ht, rfl⟩
    have h2 : g t ≤ sSup (g '' Icc a b) := le_csSup hcpt.bddAbove ⟨t, ht, rfl⟩
    rw [h0] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨t, ht, h0⟩ := hpre.Icc_subset (hcpt.sInf_mem hne) (hcpt.sSup_mem hne) ⟨h1, h2⟩
    exact ⟨t, ht, h0⟩

theorem measurableSet_ballInterior_mem (hη : Continuous η) (hε : 0 < ε) (k : ℤ) :
    MeasurableSet {q : ℝ × ℂ | k ∈ ballInterior ε η q} := by
  have hIne : ε * (k - 1) ≤ ε * k := mul_le_mul_of_nonneg_left (by linarith) hε.le
  have hA : MeasurableSet {q : ℝ × ℂ | ∃ t ∈ Icc (ε * (k - 1)) (ε * k), dist (η t) q.2 < q.1 / 4} := by
    have e : {q : ℝ × ℂ | ∃ t ∈ Icc (ε * (k - 1)) (ε * k), dist (η t) q.2 < q.1 / 4}
        = ⋃ t ∈ Icc (ε * (k - 1)) (ε * k), {q : ℝ × ℂ | dist (η t) q.2 < q.1 / 4} := by
      ext q
      simp
    rw [e]
    exact (isOpen_biUnion fun t _ => isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  have hcont : Continuous (Function.uncurry fun (q : ℝ × ℂ) (t : ℝ) => dist (η t) q.2 - q.1 / 4) := by
    unfold Function.uncurry
    fun_prop
  have hcs : Continuous fun q : ℝ × ℂ =>
      sInf ((fun t => dist (η t) q.2 - q.1 / 4) '' Icc (ε * (k - 1)) (ε * k)) :=
    isCompact_Icc.continuous_sInf hcont
  have hcS : Continuous fun q : ℝ × ℂ =>
      sSup ((fun t => dist (η t) q.2 - q.1 / 4) '' Icc (ε * (k - 1)) (ε * k)) :=
    isCompact_Icc.continuous_sSup hcont
  have hB : MeasurableSet {q : ℝ × ℂ | 0 < q.1 / 4 ∧ ∃ t ∈ Icc (ε * (k - 1)) (ε * k), dist (η t) q.2 = q.1 / 4} := by
    have e : {q : ℝ × ℂ | 0 < q.1 / 4 ∧ ∃ t ∈ Icc (ε * (k - 1)) (ε * k), dist (η t) q.2 = q.1 / 4}
        = {q : ℝ × ℂ | 0 < q.1 / 4} ∩
          ({q : ℝ × ℂ | sInf ((fun t => dist (η t) q.2 - q.1 / 4) '' Icc (ε * (k - 1)) (ε * k)) ≤ 0} ∩
           {q : ℝ × ℂ | 0 ≤ sSup ((fun t => dist (η t) q.2 - q.1 / 4) '' Icc (ε * (k - 1)) (ε * k))}) := by
      ext q
      have key := exists_zero_iff_sInf_sSup (g := fun t => dist (η t) q.2 - q.1 / 4) hIne
        (by fun_prop : Continuous fun t => dist (η t) q.2 - q.1 / 4).continuousOn
      simp only [sub_eq_zero] at key
      simp only [mem_ofPred_eq, mem_inter_iff, key]
    rw [e]
    exact (measurableSet_lt measurable_const (measurable_fst.div_const 4)).inter
      ((measurableSet_le hcs.measurable measurable_const).inter
        (measurableSet_le measurable_const hcS.measurable))
  have e : {q : ℝ × ℂ | k ∈ ballInterior ε η q} =
      {q : ℝ × ℂ | ∃ t ∈ Icc (ε * (k - 1)) (ε * k), dist (η t) q.2 < q.1 / 4} \
        {q : ℝ × ℂ | 0 < q.1 / 4 ∧ ∃ t ∈ Icc (ε * (k - 1)) (ε * k), dist (η t) q.2 = q.1 / 4} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
    unfold ballInterior interiorCellVertices
    rw [Set.mem_sdiff, mem_cellVertices_ball_iff, mem_cellVertices_frontier_ball_iff]
  rw [e]
  exact hA.diff hB


open Classical in
theorem vExitTime_le_coe_iff (A : Set ℤ) (x : ℕ → ℤ) (k : ℕ) :
    vExitTime A x ≤ (k : ℕ∞) ↔ ∃ j ≤ k, x j ∉ A := by
  unfold vExitTime
  split_ifs with h
  · constructor
    · intro hk
      have hk' : Nat.find h ≤ k := by exact_mod_cast hk
      exact ⟨Nat.find h, hk', Nat.find_spec h⟩
    · rintro ⟨j, hj, hxj⟩
      exact_mod_cast (Nat.find_min' h hxj).trans hj
  · constructor
    · intro hk
      exact absurd hk (by simp)
    · rintro ⟨j, _, hj⟩
      exact absurd ⟨j, hj⟩ h

theorem measurableSet_vExitTime_le (hη : Continuous η) (hε : 0 < ε) (k : ℕ) :
    MeasurableSet {p : (ℝ × ℂ) × (ℕ → ℤ) | vExitTime (ballInterior ε η p.1) p.2 ≤ (k : ℕ∞)} := by
  have e : {p : (ℝ × ℂ) × (ℕ → ℤ) | vExitTime (ballInterior ε η p.1) p.2 ≤ (k : ℕ∞)} =
      ⋃ j : ℕ, ⋃ (_ : j ≤ k), ⋃ z : ℤ,
        ({p : (ℝ × ℂ) × (ℕ → ℤ) | p.2 j = z} ∩
          Prod.fst ⁻¹' {q : ℝ × ℂ | z ∈ ballInterior ε η q}ᶜ) := by
    ext p
    simp only [Set.mem_ofPred_eq, vExitTime_le_coe_iff, mem_iUnion, mem_inter_iff, mem_preimage,
      mem_compl_iff, exists_prop]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, p.2 j, ⟨rfl, hx⟩⟩
    · rintro ⟨j, hj, z, ⟨hz, hzn⟩⟩
      exact ⟨j, hj, by rw [hz]; exact hzn⟩
  rw [e]
  refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun z => ?_
  refine MeasurableSet.inter ?_ ?_
  · have hc : Measurable (fun p : (ℝ × ℂ) × (ℕ → ℤ) => p.2 j) := (measurable_pi_apply j).comp measurable_snd
    exact hc (measurableSet_singleton z)
  · exact measurable_fst (measurableSet_ballInterior_mem ε η hη hε z).compl

theorem toNat_eq_zero_iff' (e : ℕ∞) : e.toNat = 0 ↔ e ≤ 0 ∨ ¬ ∃ k : ℕ, e ≤ (k : ℕ∞) := by
  induction e using ENat.recTopCoe with
  | top => simp
  | coe m =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · constructor
      · intro h
        exfalso
        simp at h
        omega
      · rintro (h | h)
        · exfalso
          simp at h
          omega
        · exact absurd ⟨m, le_rfl⟩ h

theorem toNat_eq_succ_iff' (e : ℕ∞) (n : ℕ) :
    e.toNat = n + 1 ↔ e ≤ ((n + 1 : ℕ) : ℕ∞) ∧ ¬ e ≤ (n : ℕ∞) := by
  induction e using ENat.recTopCoe with
  | top => simp
  | coe m =>
    simp only [ENat.toNat_natCast, Nat.cast_le]
    constructor
    · intro h; exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩; omega

/-- **Measurability of the exit time `σ_D`** in the parameter `q = (R, x)` and the path (PRO step 8, `hσ`). -/
theorem measurable_ballExitSigma (hη : Continuous η) (hε : 0 < ε) :
    Measurable (fun p : (ℝ × ℂ) × (ℕ → ℤ) => ballExitSigma ε η p.1 p.2) := by
  refine measurable_to_countable' fun n => ?_
  cases n with
  | zero =>
    have e : (fun p : (ℝ × ℂ) × (ℕ → ℤ) => ballExitSigma ε η p.1 p.2) ⁻¹' {0} =
        {p : (ℝ × ℂ) × (ℕ → ℤ) | vExitTime (ballInterior ε η p.1) p.2 ≤ 0} ∪
          (⋃ k : ℕ, {p : (ℝ × ℂ) × (ℕ → ℤ) | vExitTime (ballInterior ε η p.1) p.2 ≤ (k : ℕ∞)})ᶜ := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, ballExitSigma, toNat_eq_zero_iff', mem_union, mem_compl_iff,
        mem_iUnion, Set.mem_ofPred_eq]
    rw [e]
    exact (measurableSet_vExitTime_le ε η hη hε 0).union
      (MeasurableSet.iUnion fun k => measurableSet_vExitTime_le ε η hη hε k).compl
  | succ n =>
    have e : (fun p : (ℝ × ℂ) × (ℕ → ℤ) => ballExitSigma ε η p.1 p.2) ⁻¹' {n + 1} =
        {p : (ℝ × ℂ) × (ℕ → ℤ) | vExitTime (ballInterior ε η p.1) p.2 ≤ ((n + 1 : ℕ) : ℕ∞)} ∩
          {p : (ℝ × ℂ) × (ℕ → ℤ) | vExitTime (ballInterior ε η p.1) p.2 ≤ (n : ℕ∞)}ᶜ := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, ballExitSigma, toNat_eq_succ_iff', mem_inter_iff, mem_compl_iff,
        Set.mem_ofPred_eq]
    rw [e]
    exact (measurableSet_vExitTime_le ε η hη hε (n + 1)).inter
      (measurableSet_vExitTime_le ε η hη hε n).compl

theorem add_le_coe_iff' (j n : ℕ) (e : ℕ∞) :
    (j : ℕ∞) + e ≤ (n : ℕ∞) ↔ j ≤ n ∧ e ≤ ((n - j : ℕ) : ℕ∞) := by
  induction e using ENat.recTopCoe with
  | top => simp
  | coe m => norm_cast; omega

theorem testEndExit_le_iff (ρ : (ℕ → ℤ) → ℝ × ℂ) (T : (ℕ → ℤ) → ℕ∞) (w : ℕ → ℤ) (n : ℕ) :
    testEndExit ε η ρ T w ≤ (n : ℕ∞) ↔
      ∃ j ≤ n, T w = (j : ℕ∞) ∧ ∃ k ≤ n - j, w (j + k) ∉ ballInterior ε η (ρ w) := by
  by_cases hw : T w = ⊤
  · simp [testEndExit, hw]
  · obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hw
    have hpost : ∀ k : ℕ, postTimePath (fun n w => w n) T w k = w (j + k) := by
      intro k
      simp [postTimePath, ← hj]
    unfold testEndExit
    rw [← hj, add_le_coe_iff', vExitTime_le_coe_iff]
    simp only [hpost]
    constructor
    · rintro ⟨hjn, k, hk, hx⟩
      exact ⟨j, hjn, rfl, k, hk, hx⟩
    · rintro ⟨j', hj', hjj, k, hk, hx⟩
      have hjj' : j = j' := by exact_mod_cast hjj
      subst hjj'
      exact ⟨hj', k, hk, hx⟩

/-- The test end `testEndExit` is a stopping time (`isStoppingTime_testEndExit`, the hypothesis `hLst`). -/
theorem isStoppingTime_testEndExit (hη : Continuous η) (hε : 0 < ε) {T : (ℕ → ℤ) → ℕ∞}
    (hT : IsStoppingTime coordFiltration T) {ρ : (ℕ → ℤ) → ℝ × ℂ} (hρ : Measurable[hT.measurableSpace] ρ) :
    IsStoppingTime coordFiltration (testEndExit ε η ρ T) := by
  refine fun n => ?_
  have e : {w | testEndExit ε η ρ T w ≤ (n : ℕ∞)} = ⋃ j : ℕ, ⋃ (_ : j ≤ n),
      ({w | T w = (j : ℕ∞)} ∩ {w | ∃ k ≤ n - j, w (j + k) ∉ ballInterior ε η (ρ w)}) := by
    ext w
    simp only [Set.mem_ofPred_eq, testEndExit_le_iff, mem_iUnion, mem_inter_iff, exists_prop]
  show MeasurableSet[coordFiltration n] ({w | testEndExit ε η ρ T w ≤ (n : ℕ∞)})
  rw [e]
  refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun hj => ?_
  have e2 : ({w | T w = (j : ℕ∞)} ∩ {w | ∃ k ≤ n - j, w (j + k) ∉ ballInterior ε η (ρ w)}) =
      ⋃ k : ℕ, ⋃ (_ : k ≤ n - j), ⋃ z : ℤ,
        ((ρ ⁻¹' {q : ℝ × ℂ | z ∉ ballInterior ε η q}) ∩ {w | T w = (j : ℕ∞)}) ∩ {w | w (j + k) = z} := by
    ext w
    simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_iUnion, mem_preimage, exists_prop]
    constructor
    · rintro ⟨hTw, k, hk, hx⟩
      exact ⟨k, hk, w (j + k), ⟨⟨hx, hTw⟩, rfl⟩⟩
    · rintro ⟨k, hk, z, ⟨⟨hz, hTw⟩, hwz⟩⟩
      exact ⟨hTw, k, hk, by rw [hwz]; exact hz⟩
  rw [e2]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk => MeasurableSet.iUnion fun z => ?_
  have hjk : j + k ≤ n := by omega
  refine MeasurableSet.inter ?_ ?_
  · have hU : MeasurableSet {q : ℝ × ℂ | z ∉ ballInterior ε η q} :=
      (measurableSet_ballInterior_mem ε η hη hε z).compl
    have h1 : MeasurableSet[hT.measurableSpace] ((ρ ⁻¹' {q : ℝ × ℂ | z ∉ ballInterior ε η q}) ∩
        {w | T w = (j : ℕ∞)}) :=
      MeasurableSet.inter (hρ hU) (hT.measurableSet_eq' j)
    exact coordFiltration.mono hj _ ((hT.measurableSet_inter_eq_iff _ j).1 h1)
  · exact coordFiltration.mono hjk _ (coord_measurable (j + k) (measurableSet_singleton z))

/-- The coverage `T + n < L` for `n < σ_D` on `{T < ∞}`: the hypothesis `hcov` of `conditional_one_test_gen`. -/
theorem testEndExit_cover (ρ : (ℕ → ℤ) → ℝ × ℂ) (T : (ℕ → ℤ) → ℕ∞) {w : ℕ → ℤ} (hw : T w < ⊤) (n : ℕ)
    (hn : n < ballExitSigma ε η (ρ w) (postTimePath (fun n w => w n) T w)) :
    T w + (n : ℕ∞) < testEndExit ε η ρ T w := by
  obtain ⟨t, htT⟩ : ∃ t : ℕ, T w = t := ⟨(T w).toNat, (ENat.natCast_toNat hw.ne).symm⟩
  unfold testEndExit ballExitSigma at *
  rw [htT]
  generalize vExitTime (ballInterior ε η (ρ w)) (postTimePath (fun n w => w n) T w) = e at hn ⊢
  induction e using ENat.recTopCoe with
  | top => simp at hn
  | coe m =>
    simp only [ENat.toNat_natCast] at hn
    norm_cast
    omega

end BallExit


theorem occCount_le (A : Set ℤ) (s : (ℕ → ℤ) → ℕ) (w : ℕ → ℤ) :
    0 ≤ occCount A s w ∧ occCount A s w ≤ (s w : ℝ) := by
  have hterm : ∀ n, 0 ≤ Aᶜ.indicator (fun _ => (1 : ℝ)) (w n) ∧ Aᶜ.indicator (fun _ => (1 : ℝ)) (w n) ≤ 1 :=
    fun n => by by_cases h : w n ∈ Aᶜ <;> simp [h]
  unfold occCount
  refine ⟨Finset.sum_nonneg fun n _ => (hterm n).1, ?_⟩
  calc ∑ n ∈ Finset.range (s w), Aᶜ.indicator (fun _ => (1 : ℝ)) (w n)
      ≤ ∑ _n ∈ Finset.range (s w), (1 : ℝ) := Finset.sum_le_sum fun n _ => (hterm n).2
    _ = (s w : ℝ) := by simp

/-- `{T < ∞}` is `𝓕`-measurable for a stopping time (a countable union of `{T ≤ k}`). -/
theorem measurableSet_lt_top_stop {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T) :
    MeasurableSet {w | T w < ⊤} := by
  have e : {w | T w < ⊤} = ⋃ k : ℕ, {w | T w ≤ (k : ℕ∞)} := by
    ext w
    simp only [Set.mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h.ne
      exact ⟨k, le_of_eq hk.symm⟩
    · rintro ⟨k, hk⟩
      exact lt_of_le_of_lt hk (ENat.natCast_lt_top k)
  rw [e]
  exact MeasurableSet.iUnion fun k => coordFiltration.le k _ (hT k)

/-- A stopping time is measurable for the ambient σ-algebra (ℕ∞ carries the discrete σ-algebra). -/
theorem measurable_stop_ambient {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T) :
    Measurable T := by
  refine measurable_to_countable' fun x => ?_
  induction x using ENat.recTopCoe with
  | top =>
    have e : T ⁻¹' {⊤} = {w | T w < ⊤}ᶜ := by
      ext w
      simp [lt_top_iff_ne_top]
    rw [e]
    exact (measurableSet_lt_top_stop hT).compl
  | coe k =>
    exact hT.measurableSpace_le _ (hT.measurableSet_eq' k)

theorem measurable_postTimePath_stop {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T) :
    Measurable (fun w : ℕ → ℤ => postTimePath (fun n w => w n) T w) := by
  refine measurable_pi_iff.2 fun n => ?_
  have hn : Measurable (fun w : ℕ → ℤ => (T w).toNat + n) :=
    ((measurable_of_countable (fun x : ℕ∞ => x.toNat)).comp (measurable_stop_ambient hT)).add_const n
  have hq : Measurable (fun p : ℕ × (ℕ → ℤ) => p.2 p.1) :=
    measurable_from_prod_countable_right fun k => measurable_pi_apply k
  exact hq.comp (hn.prodMk measurable_id)

/-- The count `V = 1_{T<∞} occCount(σ_{ρ}, post-T path)` is measurable. -/
theorem measurable_testCountParam (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η) (hε : 0 < ε) (A : Set ℤ)
    {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T)
    {ρ : (ℕ → ℤ) → ℝ × ℂ} (hρ : Measurable[hT.measurableSpace] ρ) :
    Measurable (testCountParam A (ballExitSigma ε η) ρ T) := by
  have hρ' : Measurable ρ := fun s hs => hT.measurableSpace_le _ (hρ hs)
  have hP : Measurable (fun w : ℕ → ℤ => (ρ w, postTimePath (fun n w => w n) T w)) :=
    hρ'.prodMk (measurable_postTimePath_stop hT)
  have hO : Measurable (fun q : (ℝ × ℂ) × (ℕ → ℤ) => occCount A (ballExitSigma ε η q.1) q.2) :=
    measurable_occCount_param (σ := ballExitSigma ε η) A (measurable_ballExitSigma ε η hη hε)
  have hV := hO.comp hP
  unfold testCountParam
  exact hV.indicator (measurableSet_lt_top_stop hT)

theorem integrable_testCountParam_of_moment (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η) (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ)
    {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T)
    {ρ : (ℕ → ℤ) → ℝ × ℂ} (hρ : Measurable[hT.measurableSpace] ρ)
    (hmom : Integrable ({w | T w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (ρ w) (postTimePath (fun n w => w n) T w) : ℕ) : ℝ))) (srwLaw m a)) :
    Integrable (testCountParam A (ballExitSigma ε η) ρ T) (srwLaw m a) := by
  refine hmom.mono' (measurable_testCountParam ε η hη hε A hT hρ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun w => ?_
  unfold testCountParam
  by_cases h : T w < ⊤
  · have hw : w ∈ {w' | T w' < ⊤} := h
    rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
    obtain ⟨h0, h1⟩ := occCount_le A (ballExitSigma ε η (ρ w)) (postTimePath (fun n w => w n) T w)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  · simp [Set.indicator, h]

theorem integrable_testCountParam_sq_of_moment (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η) (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ)
    {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T)
    {ρ : (ℕ → ℤ) → ℝ × ℂ} (hρ : Measurable[hT.measurableSpace] ρ)
    (hmom : Integrable ({w | T w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (ρ w) (postTimePath (fun n w => w n) T w) : ℕ) : ℝ) ^ 2)) (srwLaw m a)) :
    Integrable ({w | T w < ⊤}.indicator
      (fun w => occCount A (ballExitSigma ε η (ρ w)) (postTimePath (fun n w => w n) T w) ^ 2)) (srwLaw m a) := by
  have hρ' : Measurable ρ := fun s hs => hT.measurableSpace_le _ (hρ hs)
  have hV2 := ((measurable_occCount_param (σ := ballExitSigma ε η) A
    (measurable_ballExitSigma ε η hη hε)).comp (hρ'.prodMk (measurable_postTimePath_stop hT))).pow_const 2
  refine hmom.mono' (hV2.indicator (measurableSet_lt_top_stop hT)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun w => ?_
  by_cases h : T w < ⊤
  · have hw : w ∈ {w' | T w' < ⊤} := h
    rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h0, h1⟩ := occCount_le A (ballExitSigma ε η (ρ w)) (postTimePath (fun n w => w n) T w)
    rw [sq, sq]
    exact mul_le_mul h1 h1 h0 (h0.trans h1)
  · simp [Set.indicator, h]

/-- **The hone of `exitQ_le_pow` for the concrete test exit time** (the family over `k ≤ n`, for the parameter
`ρ k = (R, x)` and `σ = ballExitSigma ε η`, with the stopping-time test end `L k = testEndExit ε η (ρ k) (T k)`).
Discharged here: the stopping time `hLst`, the coverage `hcov`, the measurability of `σ_D` (`hσ`) and the integrability
of the count (`hint1`, `hint2`, from `hmom1`, `hmom2`). Named: the finite exit-time moments `hmom1`, `hmom2` (the
post-T exit times have finite first and second moments under `srwLaw m a`), and the PRO step 8 side conditions `hm`,
`hRr`, `hstep1`, `hstep2`. -/
theorem hone_exitQ_concrete (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η) (hε : 0 < ε)
    (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ) (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞}
    {c C r q0 q : ℝ} (hc : 0 < c) (hC : 0 < C) (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ c ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {ρ : ℕ → (ℕ → ℤ) → ℝ × ℂ} (hρ : ∀ k, Measurable[(hT k).measurableSpace] (ρ k))
    (hmom1 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (ρ k w) (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ))) (srwLaw m a))
    (hmom2 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => ((ballExitSigma ε η (ρ k w) (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2)) (srwLaw m a))
    {mm R : ℕ → (ℕ → ℤ) → ℝ}
    (hm : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, 0 < mm k ω)
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hstep1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      c * ε⁻¹ * mm k ω ≤ ∫ w, occCount A (ballExitSigma ε η (ρ k ω)) w ∂(srwLaw m (ω (T k ω).toNat)))
    (hstep2 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∫ w, occCount A (ballExitSigma ε η (ρ k ω)) w ^ 2 ∂(srwLaw m (ω (T k ω).toNat))
        ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R k ω)) ^ 2 * mm k ω ^ 2) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndExit ε η (ρ k) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q := by
  intro k _
  subst hq
  exact conditional_one_test_gen m a hA (measurable_ballExitSigma ε η hη hε) (hT k) (hρ k) hc hC hε hr hr1 hq0c
    (isStoppingTime_testEndExit ε η hη hε (hT k) (hρ k))
    (fun _ hw _ hn => testEndExit_cover ε η (ρ k) (T k) hw _ hn)
    (integrable_testCountParam_of_moment ε η hη hε m a A (hT k) (hρ k) (hmom1 k))
    (integrable_testCountParam_sq_of_moment ε η hη hε m a A (hT k) (hρ k) (hmom2 k))
    (hm k) (hRr k) (hstep1 k) (hstep2 k)

end Lemma68Window
end MatedCRT
