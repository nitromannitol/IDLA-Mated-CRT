import Mathlib

/-!
# A measurable diagonal subsequence

For measurable real random variables `y n i` (`n` the index of the sequence, `i` a coordinate), there is a random
subsequence `Φ`, each `Φ(k)` measurable, such that for every `ω` and every coordinate `i` along which `y · i` is
eventually bounded, `y (Φ k) i` converges (`exists_measurable_diagonal_subseq`). This is the measurable choice of the
subsequence `E₀` in Lemma 3.1 (line 988), by the diagonal argument behind the Arzelà-Ascoli theorem.

* One coordinate (`selIdx`): with `L = limsup arctan(z_n)`, the `k`-th index is the first one after the previous index
  with `|arctan(z_n) - L| < 1/(k+1)`. Then `arctan(z_{n_k}) → L`, and `z_{n_k} → tan L` if `z` is eventually bounded.
  The `arctan` makes every sequence bounded, so the choice needs no hypothesis.
* All coordinates (`stageSeq`, `diagSeq`): the `i`-th stage refines the previous one for coordinate `i`, and the
  diagonal `k ↦ stage_k(k)` is eventually a subsequence of every stage.
-/

namespace MatedCRT.Tightness

open MeasureTheory Filter Topology Set

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first index satisfying a measurable predicate is measurable. -/
theorem measurable_natFind {p : Ω → ℕ → Prop} [∀ ω, DecidablePred (p ω)] (hp : ∀ ω, ∃ N, p ω N)
    (hm : ∀ k, MeasurableSet {ω | p ω k}) : Measurable fun ω => Nat.find (hp ω) := by
  refine measurable_to_countable' fun n => ?_
  have h : (fun ω => Nat.find (hp ω)) ⁻¹' {n} = {ω | p ω n} ∩ ⋂ m ∈ Finset.range n, {ω | p ω m}ᶜ := by
    ext ω
    simp [Nat.find_eq_iff]
  rw [h]
  exact (hm n).inter (Finset.measurableSet_biInter _ fun m _ => (hm m).compl)

/-- A measurable family evaluated at a measurable index is measurable. -/
theorem measurable_comp_nat {β : Type*} [MeasurableSpace β] {f : Ω → ℕ → β}
    (hf : ∀ n, Measurable fun ω => f ω n) {g : Ω → ℕ} (hg : Measurable g) : Measurable fun ω => f ω (g ω) := by
  intro s hs
  have h : (fun ω => f ω (g ω)) ⁻¹' s = ⋃ m : ℕ, g ⁻¹' {m} ∩ (fun ω => f ω m) ⁻¹' s := by
    ext ω
    simp
  rw [h]
  exact MeasurableSet.iUnion fun m => (hg (measurableSet_singleton m)).inter (hf m hs)

end Measurability

section Subseq

open Classical in
/-- The subsequence whose `k`-th index is the first index after the previous one satisfying `P k`. -/
noncomputable def subseqOf (P : ℕ → ℕ → Prop) (hex : ∀ k m, ∃ n, m < n ∧ P k n) : ℕ → ℕ
  | 0 => Nat.find (hex 0 0)
  | k + 1 => Nat.find (hex (k + 1) (subseqOf P hex k))

theorem subseqOf_spec (P : ℕ → ℕ → Prop) (hex : ∀ k m, ∃ n, m < n ∧ P k n) (k : ℕ) :
    P k (subseqOf P hex k) := by
  classical
  cases k with
  | zero => exact (Nat.find_spec (hex 0 0)).2
  | succ k => exact (Nat.find_spec (hex (k + 1) (subseqOf P hex k))).2

theorem subseqOf_strictMono (P : ℕ → ℕ → Prop) (hex : ∀ k m, ∃ n, m < n ∧ P k n) :
    StrictMono (subseqOf P hex) := by
  classical
  exact strictMono_nat_of_lt_succ fun k => (Nat.find_spec (hex (k + 1) (subseqOf P hex k))).1

open Classical in
theorem measurable_subseqOf {Ω : Type*} [MeasurableSpace Ω] (P : Ω → ℕ → ℕ → Prop)
    (hex : ∀ ω k m, ∃ n, m < n ∧ P ω k n) (hP : ∀ k n, MeasurableSet {ω | P ω k n}) (k : ℕ) :
    Measurable fun ω => subseqOf (P ω) (hex ω) k := by
  induction k with
  | zero =>
    exact measurable_natFind (p := fun ω n => 0 < n ∧ P ω 0 n) (fun ω => hex ω 0 0)
      fun n => (MeasurableSet.const (0 < n)).inter (hP 0 n)
  | succ k ih =>
    exact measurable_natFind (p := fun ω n => subseqOf (P ω) (hex ω) k < n ∧ P ω (k + 1) n)
      (fun ω => hex ω (k + 1) (subseqOf (P ω) (hex ω) k))
      fun n => (ih (Set.to_countable (Iio n)).measurableSet).inter (hP (k + 1) n)

end Subseq

section OneCoordinate

/-- `limsup arctan(z_n)`: a cluster point of the bounded sequence `arctan(z_n)`. -/
noncomputable def atanLimsup (z : ℕ → ℝ) : ℝ :=
  limsup (fun n => Real.arctan (z n)) atTop

theorem exists_near_atanLimsup (z : ℕ → ℝ) (k m : ℕ) :
    ∃ n, m < n ∧ |Real.arctan (z n) - atanLimsup z| < 1 / ((k : ℝ) + 1) := by
  have hr : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hbdd : IsBoundedUnder (· ≤ ·) atTop fun n => Real.arctan (z n) :=
    isBoundedUnder_of ⟨Real.pi / 2, fun n => (Real.arctan_lt_pi_div_two _).le⟩
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop fun n => Real.arctan (z n) :=
    isCoboundedUnder_le_of_le atTop fun n => (Real.neg_pi_div_two_lt_arctan (z n)).le
  have h1 : ∃ᶠ n in atTop, atanLimsup z - 1 / ((k : ℝ) + 1) < Real.arctan (z n) :=
    frequently_lt_of_lt_limsup hcobdd (by unfold atanLimsup; linarith)
  have h2 : ∀ᶠ n in atTop, Real.arctan (z n) < atanLimsup z + 1 / ((k : ℝ) + 1) :=
    eventually_lt_of_limsup_lt (by unfold atanLimsup; linarith) hbdd
  obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and_eventually (h2.and (eventually_gt_atTop m))).exists
  exact ⟨n, hn3, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩

/-- The measurable subsequence for one real sequence. -/
noncomputable def selIdx (z : ℕ → ℝ) : ℕ → ℕ :=
  subseqOf (fun k n => |Real.arctan (z n) - atanLimsup z| < 1 / ((k : ℝ) + 1)) (exists_near_atanLimsup z)

theorem selIdx_strictMono (z : ℕ → ℝ) : StrictMono (selIdx z) :=
  subseqOf_strictMono _ _

theorem tendsto_arctan_selIdx (z : ℕ → ℝ) :
    Tendsto (fun k => Real.arctan (z (selIdx z k))) atTop (𝓝 (atanLimsup z)) := by
  rw [Metric.tendsto_atTop]
  intro r hr
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hr
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq]
  have h := subseqOf_spec (fun k n => |Real.arctan (z n) - atanLimsup z| < 1 / ((k : ℝ) + 1))
    (exists_near_atanLimsup z) k
  have hkN : (N : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  calc |Real.arctan (z (selIdx z k)) - atanLimsup z| < 1 / ((k : ℝ) + 1) := h
    _ ≤ 1 / ((N : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) hkN
    _ < r := hN

theorem tendsto_selIdx_of_bounded (z : ℕ → ℝ) {M : ℝ} (hM : ∀ᶠ n in atTop, |z n| ≤ M) :
    ∃ l, Tendsto (fun k => z (selIdx z k)) atTop (𝓝 l) := by
  have hT := tendsto_arctan_selIdx z
  have hM' : ∀ᶠ k in atTop, |z (selIdx z k)| ≤ M := (selIdx_strictMono z).tendsto_atTop.eventually hM
  have hup : atanLimsup z ≤ Real.arctan M :=
    le_of_tendsto hT (hM'.mono fun k hk => Real.arctan_strictMono.monotone (le_of_abs_le hk))
  have hlo : Real.arctan (-M) ≤ atanLimsup z :=
    ge_of_tendsto hT (hM'.mono fun k hk => Real.arctan_strictMono.monotone (neg_le_of_abs_le hk))
  have hcos : Real.cos (atanLimsup z) ≠ 0 := by
    refine (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne'
    · linarith [Real.neg_pi_div_two_lt_arctan (-M)]
    · linarith [Real.arctan_lt_pi_div_two M]
  refine ⟨Real.tan (atanLimsup z), ?_⟩
  have := ((Real.continuousAt_tan.2 hcos).tendsto).comp hT
  simpa [Function.comp_def, Real.tan_arctan] using this

theorem measurable_selIdx {Ω : Type*} [MeasurableSpace Ω] {z : Ω → ℕ → ℝ} (hz : ∀ n, Measurable fun ω => z ω n)
    (k : ℕ) : Measurable fun ω => selIdx (z ω) k := by
  have hA : ∀ n, Measurable fun ω => Real.arctan (z ω n) := fun n => Real.measurable_arctan.comp (hz n)
  have hL : Measurable fun ω => atanLimsup (z ω) := Measurable.limsup hA
  exact measurable_subseqOf (fun ω k n => |Real.arctan (z ω n) - atanLimsup (z ω)| < 1 / ((k : ℝ) + 1))
    (fun ω => exists_near_atanLimsup (z ω))
    (fun k n => measurableSet_lt (continuous_abs.measurable.comp ((hA n).sub hL)) measurable_const) k

end OneCoordinate

section Diagonal

/-- The `i`-th stage of the diagonal extraction for the coordinates `y n i`. -/
noncomputable def stageSeq (y : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ
  | 0 => selIdx fun n => y n 0
  | i + 1 => fun k => stageSeq y i (selIdx (fun n => y (stageSeq y i n) (i + 1)) k)

/-- The diagonal subsequence `k ↦ stage_k(k)`. -/
noncomputable def diagSeq (y : ℕ → ℕ → ℝ) (k : ℕ) : ℕ :=
  stageSeq y k k

theorem stageSeq_strictMono (y : ℕ → ℕ → ℝ) : ∀ i, StrictMono (stageSeq y i)
  | 0 => selIdx_strictMono _
  | i + 1 => (stageSeq_strictMono y i).comp (selIdx_strictMono _)

theorem stageSeq_eq (y : ℕ → ℕ → ℝ) (i : ℕ) :
    ∀ j, i ≤ j → ∀ n, ∃ m, n ≤ m ∧ stageSeq y j n = stageSeq y i m := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => exact fun n => ⟨n, le_rfl, rfl⟩
  | succ j hij ih =>
    intro n
    obtain ⟨m, hm, he⟩ := ih (selIdx (fun n => y (stageSeq y j n) (j + 1)) n)
    exact ⟨m, ((selIdx_strictMono _).id_le n).trans hm, he⟩

theorem diagSeq_strictMono (y : ℕ → ℕ → ℝ) : StrictMono (diagSeq y) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  show stageSeq y k k < stageSeq y k (selIdx (fun n => y (stageSeq y k n) (k + 1)) (k + 1))
  exact stageSeq_strictMono y k (lt_of_lt_of_le k.lt_succ_self ((selIdx_strictMono _).id_le _))

theorem tendsto_stageSeq (y : ℕ → ℕ → ℝ) (i : ℕ) {M : ℝ} (hM : ∀ᶠ n in atTop, |y n i| ≤ M) :
    ∃ l, Tendsto (fun k => y (stageSeq y i k) i) atTop (𝓝 l) := by
  cases i with
  | zero => exact tendsto_selIdx_of_bounded (fun n => y n 0) hM
  | succ i =>
    exact tendsto_selIdx_of_bounded (fun n => y (stageSeq y i n) (i + 1))
      ((stageSeq_strictMono y i).tendsto_atTop.eventually hM)

theorem tendsto_diagSeq (y : ℕ → ℕ → ℝ) (i : ℕ) {M : ℝ} (hM : ∀ᶠ n in atTop, |y n i| ≤ M) :
    ∃ l, Tendsto (fun k => y (diagSeq y k) i) atTop (𝓝 l) := by
  obtain ⟨l, hl⟩ := tendsto_stageSeq y i hM
  refine ⟨l, ?_⟩
  rw [tendsto_atTop'] at hl ⊢
  intro s hs
  obtain ⟨N, hN⟩ := hl s hs
  refine ⟨max i N, fun k hk => ?_⟩
  obtain ⟨m, hm, he⟩ := stageSeq_eq y i k (le_of_max_le_left hk) k
  show y (stageSeq y k k) i ∈ s
  rw [he]
  exact hN m ((le_of_max_le_right hk).trans hm)

theorem measurable_stageSeq {Ω : Type*} [MeasurableSpace Ω] {y : Ω → ℕ → ℕ → ℝ}
    (hy : ∀ n i, Measurable fun ω => y ω n i) : ∀ i k, Measurable fun ω => stageSeq (y ω) i k
  | 0, k => measurable_selIdx (fun n => hy n 0) k
  | i + 1, k => by
    have hz : ∀ n, Measurable fun ω => y ω (stageSeq (y ω) i n) (i + 1) :=
      fun n => measurable_comp_nat (fun m => hy m (i + 1)) (measurable_stageSeq hy i n)
    exact measurable_comp_nat (fun m => measurable_stageSeq hy i m) (measurable_selIdx hz k)

/-- **Measurable diagonal subsequence.** -/
theorem exists_measurable_diagonal_subseq {Ω : Type*} [MeasurableSpace Ω] (y : Ω → ℕ → ℕ → ℝ)
    (hy : ∀ n i, Measurable fun ω => y ω n i) :
    ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable fun ω => Φ ω k) ∧ ∀ ω, StrictMono (Φ ω) ∧
      ∀ i, (∃ M, ∀ᶠ n in atTop, |y ω n i| ≤ M) → ∃ l, Tendsto (fun k => y ω (Φ ω k) i) atTop (𝓝 l) :=
  ⟨fun ω => diagSeq (y ω), fun k => measurable_stageSeq hy k k,
    fun ω => ⟨diagSeq_strictMono _, fun i ⟨_, hM⟩ => tendsto_diagSeq (y ω) i hM⟩⟩

end Diagonal

end MatedCRT.Tightness
