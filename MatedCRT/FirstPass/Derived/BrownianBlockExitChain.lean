import MatedCRT.FirstPass.Derived.BrownianBlockExitKernel
import LatticeProb.Prob.KernelProkhorovHistoryChain
import LatticeProb.Prob.KernelChainSetMass

/-!
# Chaining the block exits: a walk chain against the frozen Brownian block-exit chain

The iteration step of the chaining argument in the proof of Theorem 3.10 of the
Gwynne-Miller-Sheffield invariance principle, with the bookkeeping of the corrected plan: step radii
`R_n = (n + 1) ε`, continuity errors `η_n = 24 R_n / s`, and frozen mass `ρ_n = n · 144 R_n / s`
near the lattice, accumulated over the fresh exits.

A chain on padded histories `Fin (N + 1) → ℂ` driven by history kernels `p n` (the walk's
conditional law of its next crossing point given the history) is compared with the chain driven by
the frozen block-exit kernel `gridRectBlockExitKernel s a₁ a₂ c₁ c₂` read at the current (last)
coordinate, both started from the constant history at `z`.

* `cellBlockExitKernel_gridLines_compl`: the block exit lies on the grid lines almost surely.
* `mem_latticeNbhd_of_infDist_lt`: a point at distance `< R` of the vertices is in `latticeNbhd s R`.
* `paddedHistoryKernel_apply_last_of_lt`: before the history is full, the last coordinate after one
  step has the law of the kernel.
* `chainSeqLaw_congr_of_lt`: the `n`-step law only uses the kernels of the steps `m < n`.
* `prokhorovLE_chainSeqLaw_gridRectBlockExit`: if the start `z` lies in the open rectangle, every
  walk kernel `p n g` (`n < N`) is carried by the grid lines and is `(ε, ε)`-close to the frozen
  block-exit kernel at the last coordinate of `g`, and `(N + 1) ε ≤ s / 4`, then the `N`-step
  history laws satisfy the one-sided Prokhorov bound at radius `(N + 1) ε` with error
  `∑_{m < N} (ε + 24 (m + 1) ε / s + m · 144 (m + 1) ε / s)`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric MarkovProcess Filter
open scoped ENNReal NNReal
open HarmonicBalls HarmonicBalls.Section6 LatticeProb LatticeProb.GridCells

namespace MatedCRT

namespace BlockExit

theorem measurableSet_gridLines (s : ℝ) : MeasurableSet (gridLines s) := by
  have : gridLines s = (⋃ j : ℤ, {y : ℂ | y.re = j * s}) ∪ ⋃ m : ℤ, {y : ℂ | y.im = m * s} := by
    ext y
    simp [gridLines]
  rw [this]
  exact (MeasurableSet.iUnion fun _ => measurableSet_eq_fun Complex.measurable_re measurable_const).union
    (MeasurableSet.iUnion fun _ => measurableSet_eq_fun Complex.measurable_im measurable_const)

/-- The boundary of a block lies on the grid lines. -/
theorem frontier_openBlock_subset_gridLines {s : ℝ} (hs : 0 < s) (a b : ℤ) :
    frontier (openBlock s a b) ⊆ gridLines s := by
  intro x hx
  have ha : ((a : ℝ) - 1) * s < ((a : ℝ) + 2) * s := by nlinarith
  have hb : ((b : ℝ) - 1) * s < ((b : ℝ) + 2) * s := by nlinarith
  rw [openBlock, Complex.frontier_reProdIm, frontier_Ioo ha, frontier_Ioo hb] at hx
  rcases hx with ⟨-, hx⟩ | ⟨hx, -⟩
  · right
    rcases hx with hx | hx
    · exact ⟨b - 1, by rw [hx]; push_cast; ring⟩
    · exact ⟨b + 2, by rw [hx]; push_cast; ring⟩
  · left
    rcases hx with hx | hx
    · exact ⟨a - 1, by rw [hx]; push_cast; ring⟩
    · exact ⟨a + 2, by rw [hx]; push_cast; ring⟩

/-- The block exit lies on the grid lines almost surely. -/
theorem cellBlockExitKernel_gridLines_compl {s : ℝ} (hs : 0 < s) (x : ℂ) :
    cellBlockExitKernel s x (gridLines s)ᶜ = 0 := by
  rw [cellBlockExitKernel_apply_set s x (measurableSet_gridLines s).compl]
  set U := openBlock s (cellIndex s x).1 (cellIndex s x).2
  have hU : IsOpen U := isOpen_openBlock _ _ _
  have hUb : Bornology.IsBounded U := isBounded_openBlock _ _ _
  have hxU : x ∈ U := closedBall_subset_openBlock hs (mem_closedCell_cellIndex hs x)
    (mem_closedBall_self (by positivity))
  have hfr : ∀ᵐ ω ∂(planarBrownianMotion x),
      ω ((ContinuousPath.exitTime U ω).toNNReal) ∈ frontier U := by
    obtain ⟨R, hR⟩ := hUb.subset_ball x
    filter_upwards [ae_planarBrownianMotion_eval_zero x,
      ae_planarBrownianMotion_exitTime_ball_lt_top x R] with ω h0 hfin
    refine ContinuousPath.coordinate_exitTime_mem_frontier U hU ω (by rw [h0]; exact hxU) ?_
    exact ((ContinuousPath.exitTime_mono hR ω).trans_lt hfin).ne
  refine ae_iff.1 ?_
  filter_upwards [hfr] with ω hω
  exact frontier_openBlock_subset_gridLines hs _ _ hω

theorem frozenBlockExitKernel_gridLines_compl_le {s : ℝ} (hs : 0 < s) {F : Set ℂ}
    (hF : MeasurableSet F) (x : ℂ) :
    frozenBlockExitKernel s hF x (gridLines s)ᶜ ≤ (gridLines s)ᶜ.indicator 1 x := by
  by_cases hx : x ∈ F
  · rw [frozenBlockExitKernel_of_mem s hF hx,
      Measure.dirac_apply' _ (measurableSet_gridLines s).compl]
  · rw [frozenBlockExitKernel_of_notMem s hF hx, cellBlockExitKernel_gridLines_compl hs x]
    simp

theorem mem_latticeNbhd_of_infDist_lt {s R : ℝ} {x : ℂ} (h : infDist x (vertices s) < R) :
    x ∈ latticeNbhd s R := by
  have hne : (vertices s).Nonempty := ⟨_, 0, 0, rfl⟩
  obtain ⟨v, ⟨m, k, rfl⟩, hv⟩ := (infDist_lt_iff hne).1 h
  exact ⟨m, k, hv⟩

/-- The block-exit kernel frozen off the open grid rectangle `(a₁ s, a₂ s) × (c₁ s, c₂ s)`. -/
noncomputable def gridRectBlockExitKernel (s : ℝ) (a₁ a₂ c₁ c₂ : ℤ) : Kernel ℂ ℂ :=
  frozenBlockExitKernel s (isOpen_gridRectOpen s a₁ a₂ c₁ c₂).measurableSet.compl

instance isMarkovKernel_gridRectBlockExitKernel (s : ℝ) (a₁ a₂ c₁ c₂ : ℤ) :
    IsMarkovKernel (gridRectBlockExitKernel s a₁ a₂ c₁ c₂) := by
  unfold gridRectBlockExitKernel
  infer_instance

/-! ## Padded histories -/

/-- Before the history is full (`m < N`), the last coordinate after one step has the law of the
kernel. -/
theorem paddedHistoryKernel_apply_last_of_lt {N m : ℕ} (hm : m < N)
    {p : (Fin (N + 1) → ℂ) → Measure ℂ} (g : Fin (N + 1) → ℂ) {D : Set ℂ} (hD : MeasurableSet D) :
    paddedHistoryKernel m p g {h | h (Fin.last N) ∈ D} = p g D := by
  have hD' : MeasurableSet {h : Fin (N + 1) → ℂ | h (Fin.last N) ∈ D} :=
    measurable_pi_apply (Fin.last N) hD
  rw [paddedHistoryKernel, Measure.map_apply (measurable_padAfter m g) hD']
  congr 1
  ext x
  simp only [mem_preimage, mem_ofPred_eq]
  rw [padAfter_of_lt g x (by simpa using hm)]

/-- The `n`-step law only uses the kernels of the steps `m < n`. -/
theorem chainSeqLaw_congr_of_lt {E : Type*} [MeasurableSpace E] {κ κ' : ℕ → E → Measure E}
    (μ : Measure E) {n : ℕ} (h : ∀ m < n, κ m = κ' m) : chainSeqLaw κ μ n = chainSeqLaw κ' μ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chainSeqLaw_succ, chainSeqLaw_succ, ih fun m hm => h m (hm.trans (Nat.lt_succ_self n)),
      h n (Nat.lt_succ_self n)]

/-! ## The chain comparison -/

/-- **Chaining the block exits.** Let the start `z` lie in the open grid rectangle, `0 < N`, and
`(N + 1) ε ≤ s / 4`. Suppose that for every step `n < N` and history `g` the walk kernel `p n g` is
carried by the grid lines and is `(ε, ε)`-close, in the one-sided Prokhorov sense, to the frozen
block-exit kernel at the current position `g (Fin.last N)`. Then the laws of the `N`-step padded
histories satisfy the one-sided Prokhorov bound with radius `(N + 1) ε` and error
`∑_{m < N} (ε + 24 (m + 1) ε / s + m · 144 (m + 1) ε / s)`. -/
theorem prokhorovLE_chainSeqLaw_gridRectBlockExit {s : ℝ} (hs : 0 < s) (a₁ a₂ c₁ c₂ : ℤ)
    {N : ℕ} (hN : 0 < N) {z : ℂ} (hz : z ∈ gridRectOpen s a₁ a₂ c₁ c₂) {ε : ℝ} (hε : 0 < ε)
    (hεs : ((N : ℝ) + 1) * ε ≤ s / 4)
    {p : ℕ → (Fin (N + 1) → ℂ) → Measure ℂ} (hp : ∀ n, Measurable (p n))
    [∀ n g, IsProbabilityMeasure (p n g)]
    (hpΓ : ∀ n < N, ∀ g, p n g (gridLines s)ᶜ = 0)
    (hK : ∀ n < N, ∀ g, ProkhorovLE (p n g)
      (gridRectBlockExitKernel s a₁ a₂ c₁ c₂ (g (Fin.last N))) ε ε) :
    ProkhorovLE (chainSeqLaw (fun m => paddedHistoryKernel m (p m)) (Measure.dirac fun _ => z) N)
      (chainSeqLaw (fun m => paddedHistoryKernel m
          (fun g => gridRectBlockExitKernel s a₁ a₂ c₁ c₂ (g (Fin.last N))))
        (Measure.dirac fun _ => z) N)
      (((N : ℝ) + 1) * ε)
      (∑ m ∈ Finset.range N, (ε + 24 * (((m : ℝ) + 1) * ε) / s +
        m * (144 * (((m : ℝ) + 1) * ε) / s))) := by
  set κ := gridRectBlockExitKernel s a₁ a₂ c₁ c₂ with hκdef
  have hzF : z ∉ (gridRectOpen s a₁ a₂ c₁ c₂)ᶜ := fun h => h hz
  have hκz : κ z = cellBlockExitKernel s z := frozenBlockExitKernel_of_notMem s _ hzF
  have hRpos : ∀ n : ℕ, 0 < ((n : ℝ) + 1) * ε := fun n => mul_pos (by positivity) hε
  have hRs4 : ∀ n : ℕ, n < N → ((n : ℝ) + 1) * ε ≤ s / 4 := by
    intro n hn
    refine le_trans ?_ hεs
    have : (n : ℝ) + 1 ≤ (N : ℝ) + 1 := by
      have : (n : ℝ) < N := by exact_mod_cast hn
      linarith
    exact mul_le_mul_of_nonneg_right this hε.le
  have hΓc : MeasurableSet (gridLines s)ᶜ := (measurableSet_gridLines s).compl
  have hΓc' : MeasurableSet {h : Fin (N + 1) → ℂ | h (Fin.last N) ∈ (gridLines s)ᶜ} :=
    measurable_pi_apply (Fin.last N) hΓc
  -- the walk kernels, extended by the block-exit kernel after the history is full
  obtain ⟨p', hp'def⟩ : ∃ p' : ℕ → (Fin (N + 1) → ℂ) → Measure ℂ,
      p' = fun n => if n < N then p n else fun g => κ (g (Fin.last N)) := ⟨_, rfl⟩
  have hp'lt : ∀ n < N, p' n = p n := fun n hn => by simp [hp'def, hn]
  have hp'ge : ∀ n, ¬ n < N → p' n = fun g => κ (g (Fin.last N)) := fun n hn => by
    simp [hp'def, hn]
  have hp' : ∀ n, Measurable (p' n) := by
    intro n
    by_cases hn : n < N
    · rw [hp'lt n hn]; exact hp n
    · rw [hp'ge n hn]; exact κ.measurable.comp (measurable_pi_apply _)
  have hp'P : ∀ n g, IsProbabilityMeasure (p' n g) := by
    intro n g
    by_cases hn : n < N
    · rw [hp'lt n hn]; infer_instance
    · rw [hp'ge n hn]; infer_instance
  have hqP : ∀ (_ : ℕ) (x : ℂ), IsProbabilityMeasure (κ x) := fun _ x => inferInstance
  have hlaw : chainSeqLaw (fun m => paddedHistoryKernel m (p m)) (Measure.dirac fun _ => z) N =
      chainSeqLaw (fun m => paddedHistoryKernel m (p' m)) (Measure.dirac fun _ => z) N :=
    chainSeqLaw_congr_of_lt _ fun m hm => by rw [hp'lt m hm]
  have hκW : ∀ n, Measurable (paddedHistoryKernel n (p' n)) := fun n =>
    measurable_paddedHistoryKernel n (hp' n)
  have hκQ : ∀ n, Measurable (paddedHistoryKernel n fun g : Fin (N + 1) → ℂ => κ (g (Fin.last N))) :=
    fun n => measurable_paddedHistoryKernel n (κ.measurable.comp (measurable_pi_apply _))
  -- support and straddle sets
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ → Set ℂ,
      H = fun n => if n = 0 then {z} else if n < N then gridLines s else univ := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → Set ℂ, G = fun n => if n = 0 then {z} else if n < N then
      {b | b ∈ gridLines s ∧ ((n : ℝ) + 1) * ε ≤ infDist b (vertices s)} else ∅ := ⟨_, rfl⟩
  have hH : ∀ n, MeasurableSet (H n) := by
    intro n
    simp only [hHdef]
    split_ifs
    exacts [measurableSet_singleton z, measurableSet_gridLines s, MeasurableSet.univ]
  have hdirac : (Measure.dirac fun _ : Fin (N + 1) => z)
      {h | h (Fin.last N) ∈ ({z} : Set ℂ)}ᶜ = 0 := by
    have hm : MeasurableSet {h : Fin (N + 1) → ℂ | h (Fin.last N) ∈ ({z} : Set ℂ)} :=
      measurable_pi_apply (Fin.last N) (measurableSet_singleton z)
    rw [Measure.dirac_apply' _ hm.compl]
    simp
  have hμH : ∀ n, chainSeqLaw (fun m => paddedHistoryKernel m (p' m)) (Measure.dirac fun _ => z) n
      {h | h (Fin.last N) ∈ H n}ᶜ = 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [hHdef]
    by_cases hnN : n < N
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero hn0.ne'
      have hset : {h : Fin (N + 1) → ℂ | h (Fin.last N) ∈ H (n' + 1)}ᶜ =
          {h | h (Fin.last N) ∈ (gridLines s)ᶜ} := by
        ext h
        simp [hHdef, hnN]
      rw [hset]
      refine le_antisymm ?_ zero_le
      calc _ ≤ ∑ _m ∈ Finset.range (n' + 1), (0 : ℝ≥0∞) := by
            refine chainSeqLaw_succ_apply_le_sum hκW hΓc' ?_ ?_
            · rw [chainSeqLaw_succ, chainSeqLaw_zero, Measure.dirac_bind (hκW 0),
                paddedHistoryKernel_apply_last_of_lt hN _ hΓc, hp'lt 0 hN, hpΓ 0 hN]
            · intro m _ hm
              have hmN : m < N := by omega
              refine Eventually.of_forall fun g => ?_
              rw [paddedHistoryKernel_apply_last_of_lt hmN _ hΓc, hp'lt m hmN, hpΓ m hmN]
              exact zero_le
        _ = 0 := by simp
    · simp [hHdef, hn0.ne', hnN]
  have hG : ∀ n, chainSeqLaw (fun m => paddedHistoryKernel m fun g : Fin (N + 1) → ℂ =>
      κ (g (Fin.last N))) (Measure.dirac fun _ => z) n {h | h (Fin.last N) ∈ G n}ᶜ ≤
      ENNReal.ofReal (if n < N then (n : ℝ) * (144 * (((n : ℝ) + 1) * ε) / s) else 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have := hdirac
      simp only [hGdef, ↓reduceIte, chainSeqLaw_zero]
      rw [this]
      exact zero_le
    by_cases hnN : n < N
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero hn0.ne'
      set R := (((n' + 1 : ℕ) : ℝ) + 1) * ε with hR
      have hsub : {h : Fin (N + 1) → ℂ | h (Fin.last N) ∈ G (n' + 1)}ᶜ ⊆
          {h | h (Fin.last N) ∈ (gridLines s)ᶜ} ∪ {h | h (Fin.last N) ∈ latticeNbhd s R} := by
        intro h hh
        simp only [hGdef, Nat.add_one_ne_zero, hnN, ↓reduceIte, mem_compl_iff, mem_ofPred_eq,
          not_and, not_le] at hh
        by_cases hΓ : h (Fin.last N) ∈ gridLines s
        · exact Or.inr (mem_latticeNbhd_of_infDist_lt (hh hΓ))
        · exact Or.inl hΓ
      have h1 : chainSeqLaw (fun m => paddedHistoryKernel m fun g : Fin (N + 1) → ℂ =>
          κ (g (Fin.last N))) (Measure.dirac fun _ => z) (n' + 1)
          {h | h (Fin.last N) ∈ (gridLines s)ᶜ} ≤ ∑ _m ∈ Finset.range (n' + 1), (0 : ℝ≥0∞) := by
        refine chainSeqLaw_paddedHistory_last_le_sum (q := fun _ => κ) hN z (fun _ => κ.measurable)
          hΓc ?_ ?_
        · rw [hκz, cellBlockExitKernel_gridLines_compl hs z]
        · intro m _ _ x
          exact (frozenBlockExitKernel_gridLines_compl_le hs _ x).trans (le_of_eq (add_zero _).symm)
      have h2 : chainSeqLaw (fun m => paddedHistoryKernel m fun g : Fin (N + 1) → ℂ =>
          κ (g (Fin.last N))) (Measure.dirac fun _ => z) (n' + 1)
          {h | h (Fin.last N) ∈ latticeNbhd s R} ≤
            ∑ _m ∈ Finset.range (n' + 1), ENNReal.ofReal (144 * R / s) := by
        refine chainSeqLaw_paddedHistory_last_le_sum (q := fun _ => κ) hN z (fun _ => κ.measurable)
          (measurableSet_latticeNbhd s R) ?_ ?_
        · rw [hκz]
          exact cellBlockExitKernel_latticeNbhd_le hs z (hRpos _) (hRs4 _ hnN)
        · intro m _ _ x
          exact frozenBlockExitKernel_latticeNbhd_le hs _ x (hRpos _) (hRs4 _ hnN)
      calc _ ≤ _ := measure_mono hsub
        _ ≤ _ := measure_union_le _ _
        _ ≤ ∑ _m ∈ Finset.range (n' + 1), (0 : ℝ≥0∞) +
            ∑ _m ∈ Finset.range (n' + 1), ENNReal.ofReal (144 * R / s) := add_le_add h1 h2
        _ = _ := by
          simp only [hnN, ↓reduceIte]
          rw [Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    · have := isProbabilityMeasure_chainSeqLaw hκQ (μ := Measure.dirac fun _ : Fin (N + 1) => z) n
      simp [hGdef, hn0.ne', hnN]
  have hcont : ∀ n, ∀ b ∈ G n, ∀ y ∈ H n, dist y b < ((n : ℝ) + 1) * ε → ∀ A : Set ℂ,
      MeasurableSet A → κ y A ≤ κ b (thickening (((n : ℝ) + 1) * ε) A) +
        ENNReal.ofReal (24 * (((n : ℝ) + 1) * ε) / s) := by
    intro n b hb y hy hd A hA
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [hGdef, hHdef, ↓reduceIte, mem_singleton_iff] at hb hy
      subst hb hy
      exact (measure_mono (self_subset_thickening (hRpos 0) A)).trans le_self_add
    by_cases hnN : n < N
    · simp only [hGdef, hHdef, hn0.ne', hnN, ↓reduceIte, mem_ofPred_eq] at hb hy
      have hRs : ((n : ℝ) + 1) * ε ≤ s := (hRs4 n hnN).trans (by linarith)
      exact frozenBlockExitKernel_le_thickening_add_of_gridLines hs a₁ a₂ c₁ c₂ hy hb.1 hd hRs
        hb.2 le_rfl hA
    · simp [hGdef, hn0.ne', hnN] at hb
  have hK' : ∀ n (g : Fin (N + 1) → ℂ), ProkhorovLE (p' n g) (κ (g (Fin.last N))) ε ε := by
    intro n g
    by_cases hn : n < N
    · rw [hp'lt n hn]; exact hK n hn g
    · rw [hp'ge n hn]
      exact fun A _ => (measure_mono (self_subset_thickening hε A)).trans le_self_add
  have hsum : (∑ m ∈ Finset.range N, (ε + 24 * (((m : ℝ) + 1) * ε) / s +
        m * (144 * (((m : ℝ) + 1) * ε) / s))) =
      ∑ m ∈ Finset.range N, (ε + 24 * (((m : ℝ) + 1) * ε) / s +
        (if m < N then (m : ℝ) * (144 * (((m : ℝ) + 1) * ε) / s) else 1)) :=
    Finset.sum_congr rfl fun m hm => by simp only [Finset.mem_range.1 hm, ↓reduceIte]
  rw [hlaw, hsum]
  exact prokhorovLE_chainSeqLaw_paddedHistory_const (N := N) z (p := p') (q := fun _ => κ)
    (ε := fun _ => ε) (r := fun n => ((n : ℝ) + 1) * ε) (R := fun n => ((n : ℝ) + 1) * ε)
    (η := fun n => 24 * (((n : ℝ) + 1) * ε) / s)
    (ρ := fun n => if n < N then (n : ℝ) * (144 * (((n : ℝ) + 1) * ε) / s) else 1)
    hp' (fun _ => κ.measurable) (fun _ => Fin.last N) (fun _ => hε.le)
    (fun n => div_nonneg (mul_nonneg (by norm_num) (hRpos n).le) hs.le)
    (fun n => by
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg n)
          (div_nonneg (mul_nonneg (by norm_num) (hRpos n).le) hs.le)
      · exact zero_le_one)
    (by simpa using hε) (fun n => by push_cast; ring) (fun _ => le_rfl) hK' hH hμH hG hcont N

end BlockExit

end MatedCRT
