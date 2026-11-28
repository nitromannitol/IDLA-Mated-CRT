import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyUpper
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyGap
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyPieces
import MatedCRT.FirstPass.Derived.PeanosphereTriplePoints.ShimuraOccupancyDeterministic

/-!
# The lower bound for the occupation of a later cell in Shimura's argument

For the `γ`-correlated two-sided Brownian pair `(L, R)`, this file proves `OccupancyLower γ`:
`P(B_k ∩ A_{k+j}) ≥ c/(j - 1) E[1_{C_k ∩ F} U_k]` for `1 + 6 log n < j`.

Write `b = k/n`, `A = (k + j - 1)/n`, `Bl = (k + j)/n`, `e = n^{-1/2}`, `d = (j - 1)/n`. On a level set
`{⌊U_k / h⌋ = m}` of the past event `C_k ∩ F`, the gap piece `G` of Lemma 2 on `[b, A]`
(`ShimuraLemmaTwo`), the cell piece `P` on `[A, Bl]` and the survival piece `S` of `R` on
`[Bl, Bl + 2 - 1/n]` imply the occupation of the cell `k + j` (`mem_firstCell_inter_cell_of_pieces`).
These four events depend on the increments over the four windows `[b - 3, b]`, `[b, A]`, `[A, Bl]`,
`[Bl, Bl + 2 - 1/n]` with disjoint interiors, hence are independent (`indep_windows`). Their
probabilities are bounded below by `exists_le_measure_gap`, `exists_pos_le_measure_polygon` and
`le_measure_survivalR`; summing over the levels and letting `h → 0` gives the bound. Two departures from
the written argument: `P` comes from one straight tube in whitened coordinates in place of the polygon `0, -3u, -3v, 0`,
and `S` is the unconditional survival of `R` in place of the conditional probability `q(U_l) ≥ c e`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MatedCRT.PeanosphereTriplePoints

open MatedCRTHarmonic.MatedCRT (Path2 IsCorrelatedBM2 lrCoord)
open LatticeProb.CorrelatedBM (coneIncr iIndepFun_increment_windows)

/-! ### Independence of finitely many windows -/

/-- Events determined by the increments of `(L, R)` over finitely many windows with disjoint
interiors are independent. -/
theorem indep_windows {ι : Type*} [Fintype ι] {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (l r : ι → ℝ) (hle : ∀ i, l i ≤ r i)
    (hsep : ∀ i j, i ≠ j → r i ≤ l j ∨ r j ≤ l i) (E : ι → Set Path2)
    (hE : ∀ i, MeasurableSet (E i)) :
    μ (⋂ i, winPath (l i) (r i) ⁻¹' E i) = ∏ i, μ (winPath (l i) (r i) ⁻¹' E i) := by
  let g : ∀ i : ι, (Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)} → ℝ) → ℝ → ℝ × ℝ :=
    fun i x t =>
      (x (0, ⟨max (l i) (min (r i) t), le_max_left _ _, max_le (hle i) (min_le_left _ _)⟩),
        x (1, ⟨max (l i) (min (r i) t), le_max_left _ _, max_le (hle i) (min_le_left _ _)⟩))
  have hg : ∀ i, Measurable (g i) := fun i =>
    measurable_pi_iff.2 fun t => (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hind := (iIndepFun_increment_windows hμ l r hsep).comp g hg
  choose E' hE'm hE'eq using fun i => measurableSet_exists_pi (hE i)
  have hcoe : ∀ i ω, (fun t => winPath (l i) (r i) ω t) =
      g i (fun p : Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)} => coneIncr p.1 p.2.1 (l i) ω) := by
    intro i ω
    funext t
    refine Prod.ext ?_ ?_
    · simp [g, winPath_apply, coneIncr, lrCoord]
    · simp [g, winPath_apply, coneIncr, lrCoord]
  have hpre : ∀ i, winPath (l i) (r i) ⁻¹' E i =
      (fun ω => g i (fun p : Fin 2 × {x : ℝ // x ∈ Icc (l i) (r i)} =>
        coneIncr p.1 p.2.1 (l i) ω)) ⁻¹' E' i := by
    intro i
    ext ω
    rw [mem_preimage, mem_preimage, ← hE'eq i]
    exact Iff.of_eq (congrArg (· ∈ E' i) (hcoe i ω))
  have key := hind.measure_inter_preimage_eq_mul Finset.univ (sets := E') (fun i _ => hE'm i)
  rw [show (⋂ i, winPath (l i) (r i) ⁻¹' E i) =
    ⋂ i ∈ (Finset.univ : Finset ι), winPath (l i) (r i) ⁻¹' E i by ext ω; simp]
  simp only [hpre]
  exact key

/-! ### The pieces -/

/-- The gap piece on `[b, A]`. -/
def gapSet (b A θ e s : ℝ) : Set Path2 :=
  {p | (∀ u ∈ Icc b A, (p b).2 - θ ≤ (p u).2) ∧ (p b).2 + s ≤ (p A).2 ∧
    (∀ u ∈ Icc b A, (p A).1 - e ≤ (p u).1) ∧ (p A).1 ≤ (p b).1 - s}

/-- The cell piece on `[a, a']`. -/
def polySet (a a' e : ℝ) : Set Path2 :=
  {p | (∃ s ∈ Icc a a', (p s).1 ≤ (p a).1 - 2 * e) ∧
    (∃ s ∈ Icc a a', (p s).2 ≤ (p a').2 - 2 * e) ∧
    (∀ s ∈ Icc a a', (p a).2 - 4 * e ≤ (p s).2) ∧ (p a).2 - e ≤ (p a').2}

/-- The survival piece on `[c0, c0 + T]`. -/
def survSet (c0 T x : ℝ) : Set Path2 :=
  {p | ∀ u ∈ Icc c0 (c0 + T), (p c0).2 - x ≤ (p u).2}

/-- The level set `{⌊U_k / h⌋ = m}` of the past event and the tameness event. -/
def levelSet (n k j : ℕ) (h : ℝ) (m : ℕ) : Set Path2 :=
  (pastEvent n k ∩ tameEvent n k j) ∩ {p | ⌊cellDropR n k p / h⌋₊ = m}

theorem winPath_fst {l r t : ℝ} (ht : t ∈ Icc l r) (ω : Path2) :
    (winPath l r ω t).1 = (ω t).1 - (ω l).1 := by
  rw [winPath_of_mem ht, Prod.fst_sub]

theorem winPath_snd {l r t : ℝ} (ht : t ∈ Icc l r) (ω : Path2) :
    (winPath l r ω t).2 = (ω t).2 - (ω l).2 := by
  rw [winPath_of_mem ht, Prod.snd_sub]

theorem winPath_mem_gapSet {b A : ℝ} (hbA : b ≤ A) (θ e s : ℝ) (ω : Path2) :
    winPath b A ω ∈ gapSet b A θ e s ↔ ω ∈ gapSet b A θ e s := by
  have hb : b ∈ Icc b A := ⟨le_rfl, hbA⟩
  have hA : A ∈ Icc b A := ⟨hbA, le_rfl⟩
  unfold gapSet
  simp only [mem_ofPred_eq]
  refine and_congr (forall₂_congr fun u hu => ?_) (and_congr ?_
    (and_congr (forall₂_congr fun u hu => ?_) ?_))
  · rw [winPath_snd hb, winPath_snd hu]
    constructor <;> intro h <;> linarith
  · rw [winPath_snd hb, winPath_snd hA]
    constructor <;> intro h <;> linarith
  · rw [winPath_fst hA, winPath_fst hu]
    constructor <;> intro h <;> linarith
  · rw [winPath_fst hA, winPath_fst hb]
    constructor <;> intro h <;> linarith

theorem winPath_mem_polySet {a a' : ℝ} (haa : a ≤ a') (e : ℝ) (ω : Path2) :
    winPath a a' ω ∈ polySet a a' e ↔ ω ∈ polySet a a' e := by
  have ha : a ∈ Icc a a' := ⟨le_rfl, haa⟩
  have ha' : a' ∈ Icc a a' := ⟨haa, le_rfl⟩
  unfold polySet
  simp only [mem_ofPred_eq]
  refine and_congr (exists_congr fun s => and_congr_right fun hs => ?_) (and_congr
    (exists_congr fun s => and_congr_right fun hs => ?_) (and_congr
    (forall₂_congr fun s hs => ?_) ?_))
  · rw [winPath_fst hs, winPath_fst ha]
    constructor <;> intro h <;> linarith
  · rw [winPath_snd hs, winPath_snd ha']
    constructor <;> intro h <;> linarith
  · rw [winPath_snd ha, winPath_snd hs]
    constructor <;> intro h <;> linarith
  · rw [winPath_snd ha, winPath_snd ha']
    constructor <;> intro h <;> linarith

theorem winPath_mem_survSet {c0 T : ℝ} (hT : 0 ≤ T) (x : ℝ) (ω : Path2) :
    winPath c0 (c0 + T) ω ∈ survSet c0 T x ↔ ω ∈ survSet c0 T x := by
  have ha : c0 ∈ Icc c0 (c0 + T) := ⟨le_rfl, by linarith⟩
  unfold survSet
  simp only [mem_ofPred_eq]
  refine forall₂_congr fun u hu => ?_
  rw [winPath_snd ha, winPath_snd hu]
  constructor <;> intro h <;> linarith

theorem level_win_iff {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) (j : ℕ) (h : ℝ) (m : ℕ) (ω : Path2) :
    winPath ((k : ℝ) / n - 3) ((k : ℝ) / n) ω ∈ levelSet n k j h m ↔ ω ∈ levelSet n k j h m := by
  have hpast : winPath ((k : ℝ) / n - 3) ((k : ℝ) / n) ω ∈ pastEvent n k ↔
      ω ∈ pastEvent n k :=
    priorCellsFail_shift hn hkn (cX := (ω ((k : ℝ) / n - 3)).1) (cY := (ω ((k : ℝ) / n - 3)).2)
      (fun t ht => by simp only [winPath_of_mem ht, Prod.fst_sub])
      (fun t ht => by simp only [winPath_of_mem ht, Prod.snd_sub])
  have hR := cellDropR_winPath hn hkn ω
  have hL := cellDropL_winPath hn hkn ω
  simp only [levelSet, mem_inter_iff, mem_ofPred_eq, tameEvent, hpast, hR, hL]

theorem measurableSet_levelSet (n k j : ℕ) (h : ℝ) (m : ℕ) : MeasurableSet (levelSet n k j h m) :=
  ((measurableSet_pastEvent n k).inter (measurableSet_tameEvent n k j)).inter
    ((Nat.measurable_floor.comp ((measurable_cellDropR n k).div_const h))
      (measurableSet_singleton m))

theorem levelSet_disjoint (n k j : ℕ) (h : ℝ) : Pairwise (Function.onFun Disjoint (levelSet n k j h)) := by
  intro m m' hne
  refine Set.disjoint_left.2 fun p hp hp' => hne ?_
  have h1 : ⌊cellDropR n k p / h⌋₊ = m := hp.2
  have h2 : ⌊cellDropR n k p / h⌋₊ = m' := hp'.2
  exact h1.symm.trans h2

/-! ### Measurability of the pieces -/

theorem isClosed_forall_Icc {a b : ℝ} {φ : Path2 → ℝ → Prop} (h : ∀ u, IsClosed {p | φ p u}) :
    IsClosed {p : Path2 | ∀ u ∈ Icc a b, φ p u} := by
  have : {p : Path2 | ∀ u ∈ Icc a b, φ p u} = ⋂ u ∈ Icc a b, {p | φ p u} := by
    ext p
    simp
  rw [this]
  exact isClosed_biInter fun u _ => h u

theorem isClosed_exists_Icc {a b : ℝ} {F G : Path2 → ℝ → ℝ}
    (hF : Continuous fun q : Path2 × ℝ => F q.1 q.2)
    (hG : Continuous fun q : Path2 × ℝ => G q.1 q.2) :
    IsClosed {p : Path2 | ∃ s ∈ Icc a b, F p s ≤ G p s} := by
  have hF' : Continuous fun q : Path2 × Icc a b => F q.1 q.2 :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hG' : Continuous fun q : Path2 × Icc a b => G q.1 q.2 :=
    hG.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have : {p : Path2 | ∃ s ∈ Icc a b, F p s ≤ G p s} =
      Prod.fst '' {q : Path2 × Icc a b | F q.1 q.2 ≤ G q.1 q.2} := by
    ext p
    constructor
    · rintro ⟨s, hs, h⟩
      exact ⟨(p, ⟨s, hs⟩), h, rfl⟩
    · rintro ⟨⟨p', ⟨s, hs⟩⟩, h, rfl⟩
      exact ⟨s, hs, h⟩
  rw [this]
  exact isClosedMap_fst_of_compactSpace _ (isClosed_le hF' hG')

theorem cont_fst (u : ℝ) : Continuous fun p : Path2 => (p u).1 :=
  continuous_fst.comp (continuous_eval_const u)

theorem cont_snd (u : ℝ) : Continuous fun p : Path2 => (p u).2 :=
  continuous_snd.comp (continuous_eval_const u)

theorem cont_fst_eval : Continuous fun q : Path2 × ℝ => (q.1 q.2).1 :=
  continuous_fst.comp continuous_eval

theorem cont_snd_eval : Continuous fun q : Path2 × ℝ => (q.1 q.2).2 :=
  continuous_snd.comp continuous_eval

theorem isClosed_gapSet (b A θ e s : ℝ) : IsClosed (gapSet b A θ e s) := by
  unfold gapSet
  simp only [Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · exact isClosed_forall_Icc (φ := fun p u => (p b).2 - θ ≤ (p u).2) fun u =>
      isClosed_le ((cont_snd b).sub continuous_const) (cont_snd u)
  · exact isClosed_le ((cont_snd b).add continuous_const) (cont_snd A)
  · exact isClosed_forall_Icc (φ := fun p u => (p A).1 - e ≤ (p u).1) fun u =>
      isClosed_le ((cont_fst A).sub continuous_const) (cont_fst u)
  · exact isClosed_le (cont_fst A) ((cont_fst b).sub continuous_const)

theorem isClosed_polySet (a a' e : ℝ) : IsClosed (polySet a a' e) := by
  unfold polySet
  simp only [Set.ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · exact isClosed_exists_Icc (F := fun p s => (p s).1) (G := fun p _ => (p a).1 - 2 * e)
      cont_fst_eval (((cont_fst a).sub continuous_const).comp continuous_fst)
  · exact isClosed_exists_Icc (F := fun p s => (p s).2) (G := fun p _ => (p a').2 - 2 * e)
      cont_snd_eval (((cont_snd a').sub continuous_const).comp continuous_fst)
  · exact isClosed_forall_Icc (φ := fun p s => (p a).2 - 4 * e ≤ (p s).2) fun u =>
      isClosed_le ((cont_snd a).sub continuous_const) (cont_snd u)
  · exact isClosed_le ((cont_snd a).sub continuous_const) (cont_snd a')

theorem isClosed_survSet (c0 T x : ℝ) : IsClosed (survSet c0 T x) := by
  unfold survSet
  exact isClosed_forall_Icc (φ := fun p u => (p c0).2 - x ≤ (p u).2) fun u =>
    isClosed_le ((cont_snd c0).sub continuous_const) (cont_snd u)

/-! ### The real inequality -/

theorem real_ineq {c c₂ θ e sd J T' : ℝ} (hc : 0 < c) (hc₂ : 0 < c₂) (hθ : 0 < θ) (he : 0 < e)
    (_hsd : 0 < sd) (hJ : 0 < J) (hss : sd * sd = J * e ^ 2) (hT : 0 < T') (hT2 : T' ≤ 2) :
    c * c₂ / (8 * Real.sqrt 2) * θ / J ≤
      c * (θ / sd) * (e / sd) * c₂ * (2 * e / (16 * Real.sqrt T')) := by
  have hsT : 0 < Real.sqrt T' := Real.sqrt_pos.2 hT
  have hs2 : Real.sqrt T' ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hT2
  have hs2p : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h1 : (θ / sd) * (e / sd) = θ / (J * e) := by
    rw [div_mul_div_comm, hss]
    field_simp
  have h2 : c * (θ / sd) * (e / sd) * c₂ * (2 * e / (16 * Real.sqrt T')) =
      c * c₂ * θ / (8 * Real.sqrt T' * J) := by
    rw [mul_assoc c (θ / sd) (e / sd), h1]
    field_simp
    ring
  have h3 : c * c₂ / (8 * Real.sqrt 2) * θ / J = c * c₂ * θ / (8 * Real.sqrt 2 * J) := by
    field_simp
  rw [h2, h3]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 (by norm_num)) hJ.le

/-! ### The bound -/

/-- The gap piece at the cell `k` and the later cell `k + j`. -/
def gapEv (n k j : ℕ) (θ e : ℝ) : Set Path2 :=
  gapSet ((k : ℝ) / n) (((k : ℝ) + j - 1) / n) θ e (Real.sqrt (((j : ℝ) - 1) / n))

/-- The cell piece on the cell `k + j`. -/
def polyEv (n k j : ℕ) (e : ℝ) : Set Path2 :=
  polySet (((k : ℝ) + j - 1) / n) (((k : ℝ) + j) / n) e

/-- The survival piece after the cell `k + j`. -/
def survEv (n k j : ℕ) (e : ℝ) : Set Path2 :=
  survSet (((k : ℝ) + j) / n) (2 - 1 / (n : ℝ)) (2 * e)

theorem measure_level_inter {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {n k j : ℕ}
    (hn : 1 ≤ n) (hkn : k ≤ n) (hj : 1 ≤ j) (h : ℝ) (m : ℕ) (θ e : ℝ) :
    μ (levelSet n k j h m ∩ gapEv n k j θ e ∩ polyEv n k j e ∩ survEv n k j e) =
      μ (levelSet n k j h m) * μ (gapEv n k j θ e) * μ (polyEv n k j e) *
        μ (survEv n k j e) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h1n : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact hn1
  have hbA : (k : ℝ) / n ≤ ((k : ℝ) + j - 1) / n :=
    div_le_div_of_nonneg_right (by linarith) hnR.le
  have hABl : ((k : ℝ) + j - 1) / n ≤ ((k : ℝ) + j) / n :=
    div_le_div_of_nonneg_right (by linarith) hnR.le
  have hT' : 0 ≤ 2 - 1 / (n : ℝ) := by linarith
  let l : Fin 4 → ℝ := ![(k : ℝ) / n - 3, (k : ℝ) / n, ((k : ℝ) + j - 1) / n, ((k : ℝ) + j) / n]
  let r : Fin 4 → ℝ := ![(k : ℝ) / n, ((k : ℝ) + j - 1) / n, ((k : ℝ) + j) / n,
    ((k : ℝ) + j) / n + (2 - 1 / (n : ℝ))]
  have hle : ∀ i, l i ≤ r i := by
    intro i
    fin_cases i
    · show (k : ℝ) / n - 3 ≤ (k : ℝ) / n
      linarith
    · exact hbA
    · exact hABl
    · show ((k : ℝ) + j) / n ≤ ((k : ℝ) + j) / n + (2 - 1 / (n : ℝ))
      linarith
  have hsep : ∀ i j : Fin 4, i ≠ j → r i ≤ l j ∨ r j ≤ l i := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Or.inl le_rfl
    · exact Or.inl hbA
    · exact Or.inl (hbA.trans hABl)
    · exact Or.inr le_rfl
    · exact absurd rfl hij
    · exact Or.inl le_rfl
    · exact Or.inl hABl
    · exact Or.inr hbA
    · exact Or.inr le_rfl
    · exact absurd rfl hij
    · exact Or.inl le_rfl
    · exact Or.inr (hbA.trans hABl)
    · exact Or.inr hABl
    · exact Or.inr le_rfl
    · exact absurd rfl hij
  let E : Fin 4 → Set Path2 :=
    ![levelSet n k j h m, gapEv n k j θ e, polyEv n k j e, survEv n k j e]
  have hE : ∀ i, MeasurableSet (E i) := by
    intro i
    fin_cases i
    · exact measurableSet_levelSet n k j h m
    · exact (isClosed_gapSet _ _ _ _ _).measurableSet
    · exact (isClosed_polySet _ _ _).measurableSet
    · exact (isClosed_survSet _ _ _).measurableSet
  have key := indep_windows hμ l r hle hsep E hE
  have inv0 : ∀ ω, winPath ((k : ℝ) / n - 3) ((k : ℝ) / n) ω ∈ levelSet n k j h m ↔
      ω ∈ levelSet n k j h m := level_win_iff hn hkn j h m
  have inv1 : ∀ ω, winPath ((k : ℝ) / n) (((k : ℝ) + j - 1) / n) ω ∈ gapEv n k j θ e ↔
      ω ∈ gapEv n k j θ e := winPath_mem_gapSet hbA θ e _
  have inv2 : ∀ ω, winPath (((k : ℝ) + j - 1) / n) (((k : ℝ) + j) / n) ω ∈ polyEv n k j e ↔
      ω ∈ polyEv n k j e := winPath_mem_polySet hABl e
  have inv3 : ∀ ω, winPath (((k : ℝ) + j) / n) (((k : ℝ) + j) / n + (2 - 1 / (n : ℝ))) ω ∈
      survEv n k j e ↔ ω ∈ survEv n k j e := winPath_mem_survSet hT' (2 * e)
  have hcap : (⋂ i, winPath (l i) (r i) ⁻¹' E i) =
      levelSet n k j h m ∩ gapEv n k j θ e ∩ polyEv n k j e ∩ survEv n k j e := by
    ext ω
    simp only [mem_iInter, mem_preimage, mem_inter_iff]
    constructor
    · intro hω
      exact ⟨⟨⟨(inv0 ω).1 (hω 0), (inv1 ω).1 (hω 1)⟩, (inv2 ω).1 (hω 2)⟩, (inv3 ω).1 (hω 3)⟩
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ i
      fin_cases i
      · exact (inv0 ω).2 h0
      · exact (inv1 ω).2 h1
      · exact (inv2 ω).2 h2
      · exact (inv3 ω).2 h3
  have e0 : winPath (l 0) (r 0) ⁻¹' E 0 = levelSet n k j h m := Set.ext inv0
  have e1 : winPath (l 1) (r 1) ⁻¹' E 1 = gapEv n k j θ e := Set.ext inv1
  have e2 : winPath (l 2) (r 2) ⁻¹' E 2 = polyEv n k j e := Set.ext inv2
  have e3 : winPath (l 3) (r 3) ⁻¹' E 3 = survEv n k j e := Set.ext inv3
  rw [hcap, Fin.prod_univ_four, e0, e1, e2, e3] at key
  exact key

/-- The core of the lower bound, for a single law. -/
theorem lower_core {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {c c₂ : ℝ}
    (hc : 0 < c) (hc₂ : 0 < c₂)
    (hgap : ∀ b d Δ δ : ℝ, 0 < d → 0 < Δ → Δ ≤ 1 → 0 < δ → δ ≤ 1 →
      ENNReal.ofReal (c * Δ * δ) ≤
        μ (gapSet b (b + d) (Δ * Real.sqrt d) (δ * Real.sqrt d) (Real.sqrt d)))
    (hpoly : ∀ a e : ℝ, 0 < e → ENNReal.ofReal c₂ ≤ μ (polySet a (a + e ^ 2) e))
    {n k j : ℕ} (hn : 30 ≤ n) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hj : 1 + 6 * Real.log n < j)
    (hkj : k + j ≤ 2 * n) :
    ENNReal.ofReal (c * c₂ / (8 * Real.sqrt 2) / ((j : ℝ) - 1)) *
        ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ ≤
      μ (firstCellEvent n k ∩ cellEvent n (k + j)) := by
  have := hμ.isProbabilityMeasure
  have hn1 : 1 ≤ n := by omega
  have hnR : (30 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  -- numerics
  have hlog : 3 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 3
    have h4 : (2.7182818286 : ℝ) ^ 3 ≤ 30 := by norm_num
    linarith
  have hjR : (19 : ℝ) < j := by linarith
  have hj2 : 2 ≤ j := by
    have : (2 : ℝ) < j := by linarith
    exact_mod_cast this.le
  have hJ : (18 : ℝ) < (j : ℝ) - 1 := by linarith
  have hJ0 : (0 : ℝ) < (j : ℝ) - 1 := by linarith
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = (Real.sqrt n)⁻¹ := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [hedef]; exact inv_pos.2 (Real.sqrt_pos.2 hnpos)
  have hen : e ^ 2 = 1 / (n : ℝ) := by
    rw [hedef, inv_pow, Real.sq_sqrt hnpos.le, one_div]
  have hd0 : (0 : ℝ) < ((j : ℝ) - 1) / n := by positivity
  have hsd0 : 0 < Real.sqrt (((j : ℝ) - 1) / n) := Real.sqrt_pos.2 hd0
  have hss : Real.sqrt (((j : ℝ) - 1) / n) * Real.sqrt (((j : ℝ) - 1) / n) =
      ((j : ℝ) - 1) * e ^ 2 := by
    rw [Real.mul_self_sqrt hd0.le, hen]
    ring
  have h4e : 4 * e ≤ Real.sqrt (((j : ℝ) - 1) / n) := by
    rw [show 4 * e = Real.sqrt ((4 * e) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, hen, show ((4 : ℝ) ^ 2) * (1 / (n : ℝ)) = 16 / n by ring]
    exact div_le_div_of_nonneg_right (by linarith) hnpos.le
  have hesd : e ≤ Real.sqrt (((j : ℝ) - 1) / n) := by linarith
  have hT'0 : 0 < 2 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnpos]; linarith
    linarith
  have hT'2 : 2 - 1 / (n : ℝ) ≤ 2 := by
    have : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith
  have hxT : (2 * e) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
    rw [mul_pow, hen, show ((2 : ℝ) ^ 2) * (1 / (n : ℝ)) = 4 / n by ring]
    have : 5 / (n : ℝ) ≤ 1 := by rw [div_le_one hnpos]; linarith
    have h5 : (4 : ℝ) / n + 1 / n = 5 / n := by ring
    have h6 : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  set κ : ℝ := c * c₂ / (8 * Real.sqrt 2) with hκ
  have hκ0 : 0 < κ := by positivity
  have hBl : ((k : ℝ) + j - 1) / n + e ^ 2 = ((k : ℝ) + j) / n := by
    rw [hen]
    field_simp
    ring
  -- the pieces
  have hP : ENNReal.ofReal c₂ ≤ μ (polyEv n k j e) := by
    have := hpoly (((k : ℝ) + j - 1) / n) e he0
    rw [hBl] at this
    exact this
  have hS : ENNReal.ofReal (2 * e / (16 * Real.sqrt (2 - 1 / (n : ℝ)))) ≤ μ (survEv n k j e) :=
    le_measure_survivalR hμ (((k : ℝ) + j) / n) hT'0 (by positivity) hxT
  have hGbound : ∀ θ : ℝ, 0 < θ → θ ≤ Real.sqrt (((j : ℝ) - 1) / n) →
      ENNReal.ofReal (c * (θ / Real.sqrt (((j : ℝ) - 1) / n)) *
          (e / Real.sqrt (((j : ℝ) - 1) / n))) ≤ μ (gapEv n k j θ e) := by
    intro θ hθ hθsd
    have h1 := hgap ((k : ℝ) / n) (((j : ℝ) - 1) / n) (θ / Real.sqrt (((j : ℝ) - 1) / n))
      (e / Real.sqrt (((j : ℝ) - 1) / n)) hd0 (div_pos hθ hsd0) ((div_le_one hsd0).2 hθsd)
      (div_pos he0 hsd0) ((div_le_one hsd0).2 hesd)
    have hA : (k : ℝ) / n + ((j : ℝ) - 1) / n = ((k : ℝ) + j - 1) / n := by ring
    have e1 : θ / Real.sqrt (((j : ℝ) - 1) / n) * Real.sqrt (((j : ℝ) - 1) / n) = θ :=
      div_mul_cancel₀ _ hsd0.ne'
    have e2 : e / Real.sqrt (((j : ℝ) - 1) / n) * Real.sqrt (((j : ℝ) - 1) / n) = e :=
      div_mul_cancel₀ _ hsd0.ne'
    rw [hA, e1, e2] at h1
    exact h1
  -- levels
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hJ1 : (1 : ℝ) ≤ (j : ℝ) - 1 := by linarith
  have main : ∀ h : ℝ, 0 < h →
      ENNReal.ofReal (κ / ((j : ℝ) - 1)) *
          ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ ≤
        μ (firstCellEvent n k ∩ cellEvent n (k + j)) + ENNReal.ofReal (κ * h) := by
    intro h hh
    have hAm : ∀ m, MeasurableSet (levelSet n k j h m) := measurableSet_levelSet n k j h
    have hAd : Pairwise (Function.onFun Disjoint (levelSet n k j h)) := levelSet_disjoint n k j h
    have hDm : ∀ m : ℕ, MeasurableSet (levelSet n k j h m ∩ gapEv n k j ((m : ℝ) * h) e ∩
        polyEv n k j e ∩ survEv n k j e) := fun m =>
      (((hAm m).inter (isClosed_gapSet _ _ _ _ _).measurableSet).inter
        (isClosed_polySet _ _ _).measurableSet).inter (isClosed_survSet _ _ _).measurableSet
    have hDd : Pairwise (Function.onFun Disjoint (fun m : ℕ => levelSet n k j h m ∩
        gapEv n k j ((m : ℝ) * h) e ∩ polyEv n k j e ∩ survEv n k j e)) := by
      intro m m' hne
      exact (hAd hne).mono (fun p hp => hp.1.1.1) (fun p hp => hp.1.1.1)
    -- the deterministic inclusion
    have hDsub : ∀ m : ℕ, (levelSet n k j h m ∩ gapEv n k j ((m : ℝ) * h) e ∩
        polyEv n k j e ∩ survEv n k j e) ⊆ firstCellEvent n k ∩ cellEvent n (k + j) := by
      intro m p hp
      obtain ⟨⟨⟨hA, hG⟩, hPp⟩, hSp⟩ := hp
      have hpm : ⌊cellDropR n k p / h⌋₊ = m := hA.2
      have hfl : (m : ℝ) ≤ cellDropR n k p / h := by
        rw [← hpm]
        exact Nat.floor_le (div_nonneg (cellDropR_nonneg n k p) hh.le)
      have hlev : (m : ℝ) * h ≤ cellDropR n k p := by rwa [le_div_iff₀ hh] at hfl
      exact mem_firstCell_inter_cell_of_pieces hn1 hk1 hkn hkj hj2 he0 hen h4e hA.1.1 hA.1.2
        (by positivity) hlev hG hPp hSp
    -- the level bound
    have hlevel : ∀ m : ℕ, ENNReal.ofReal (κ * ((m : ℝ) * h) / ((j : ℝ) - 1)) *
        μ (levelSet n k j h m) ≤ μ (levelSet n k j h m ∩ gapEv n k j ((m : ℝ) * h) e ∩
          polyEv n k j e ∩ survEv n k j e) := by
      intro m
      by_cases hm0 : m = 0
      · subst hm0
        simp
      rcases (levelSet n k j h m).eq_empty_or_nonempty with hemp | ⟨p0, hp0⟩
      · rw [hemp]
        simp
      have hpm : ⌊cellDropR n k p0 / h⌋₊ = m := hp0.2
      have hfl : (m : ℝ) ≤ cellDropR n k p0 / h := by
        rw [← hpm]
        exact Nat.floor_le (div_nonneg (cellDropR_nonneg n k p0) hh.le)
      have hlev0 : (m : ℝ) * h ≤ cellDropR n k p0 := by rwa [le_div_iff₀ hh] at hfl
      have hθsd : (m : ℝ) * h ≤ Real.sqrt (((j : ℝ) - 1) / n) := hlev0.trans hp0.1.2.1
      have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
      have hθ0 : 0 < (m : ℝ) * h := by positivity
      have hG := hGbound ((m : ℝ) * h) hθ0 hθsd
      have hind := measure_level_inter hμ hn1 hkn (by omega : 1 ≤ j) h m ((m : ℝ) * h) e
      have hreal := real_ineq hc hc₂ hθ0 he0 hsd0 hJ0 hss hT'0 hT'2
      have hX : 0 ≤ c * ((m : ℝ) * h / Real.sqrt (((j : ℝ) - 1) / n)) *
          (e / Real.sqrt (((j : ℝ) - 1) / n)) := by positivity
      have hXc : 0 ≤ c * ((m : ℝ) * h / Real.sqrt (((j : ℝ) - 1) / n)) *
          (e / Real.sqrt (((j : ℝ) - 1) / n)) * c₂ := by positivity
      calc ENNReal.ofReal (κ * ((m : ℝ) * h) / ((j : ℝ) - 1)) * μ (levelSet n k j h m)
          = μ (levelSet n k j h m) * ENNReal.ofReal (κ * ((m : ℝ) * h) / ((j : ℝ) - 1)) :=
            mul_comm _ _
        _ ≤ μ (levelSet n k j h m) * ENNReal.ofReal (c * ((m : ℝ) * h / Real.sqrt (((j : ℝ) - 1) / n)) *
              (e / Real.sqrt (((j : ℝ) - 1) / n)) * c₂ *
              (2 * e / (16 * Real.sqrt (2 - 1 / (n : ℝ))))) :=
            mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hreal)
        _ = μ (levelSet n k j h m) * (ENNReal.ofReal (c * ((m : ℝ) * h /
              Real.sqrt (((j : ℝ) - 1) / n)) * (e / Real.sqrt (((j : ℝ) - 1) / n))) *
              ENNReal.ofReal c₂ *
              ENNReal.ofReal (2 * e / (16 * Real.sqrt (2 - 1 / (n : ℝ))))) := by
            rw [ENNReal.ofReal_mul hXc, ENNReal.ofReal_mul hX]
        _ ≤ μ (levelSet n k j h m) * (μ (gapEv n k j ((m : ℝ) * h) e) * μ (polyEv n k j e) *
              μ (survEv n k j e)) :=
            mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' hG hP) hS)
        _ = μ (levelSet n k j h m ∩ gapEv n k j ((m : ℝ) * h) e ∩ polyEv n k j e ∩
              survEv n k j e) := by
            rw [hind]
            ring
    have hsumD : ∑' m : ℕ, μ (levelSet n k j h m ∩ gapEv n k j ((m : ℝ) * h) e ∩
        polyEv n k j e ∩ survEv n k j e) ≤ μ (firstCellEvent n k ∩ cellEvent n (k + j)) := by
      rw [← measure_iUnion hDd hDm]
      exact measure_mono (iUnion_subset hDsub)
    have hsumA : ∑' m : ℕ, μ (levelSet n k j h m) ≤ 1 := by
      rw [← measure_iUnion hAd hAm]
      exact prob_le_one
    have hunion : pastEvent n k ∩ tameEvent n k j = ⋃ m : ℕ, levelSet n k j h m := by
      ext p
      constructor
      · intro hp
        exact mem_iUnion.2 ⟨⌊cellDropR n k p / h⌋₊, hp, rfl⟩
      · intro hp
        obtain ⟨m, hm⟩ := mem_iUnion.1 hp
        exact hm.1
    have hint : ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ ≤
        ∑' m : ℕ, ENNReal.ofReal ((m : ℝ) * h) * μ (levelSet n k j h m) + ENNReal.ofReal h := by
      calc ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ
          = ∫⁻ p in ⋃ m : ℕ, levelSet n k j h m, ENNReal.ofReal (cellDropR n k p) ∂μ := by
            rw [hunion]
        _ = ∑' m : ℕ, ∫⁻ p in levelSet n k j h m, ENNReal.ofReal (cellDropR n k p) ∂μ :=
            lintegral_iUnion hAm hAd _
        _ ≤ ∑' m : ℕ, ENNReal.ofReal (((m : ℝ) + 1) * h) * μ (levelSet n k j h m) := by
            refine ENNReal.tsum_le_tsum fun m => ?_
            calc ∫⁻ p in levelSet n k j h m, ENNReal.ofReal (cellDropR n k p) ∂μ
                ≤ ∫⁻ p in levelSet n k j h m, ENNReal.ofReal (((m : ℝ) + 1) * h) ∂μ := by
                  refine setLIntegral_mono' (hAm m) fun p hp => ?_
                  refine ENNReal.ofReal_le_ofReal ?_
                  have hpm : ⌊cellDropR n k p / h⌋₊ = m := hp.2
                  have := Nat.lt_floor_add_one (cellDropR n k p / h)
                  rw [hpm, div_lt_iff₀ hh] at this
                  exact this.le
              _ = ENNReal.ofReal (((m : ℝ) + 1) * h) * μ (levelSet n k j h m) :=
                  setLIntegral_const _ _
        _ = ∑' m : ℕ, (ENNReal.ofReal ((m : ℝ) * h) * μ (levelSet n k j h m) +
              ENNReal.ofReal h * μ (levelSet n k j h m)) := by
            refine tsum_congr fun m => ?_
            have hmh : ((m : ℝ) + 1) * h = (m : ℝ) * h + h := by ring
            rw [hmh, ENNReal.ofReal_add (p := (m : ℝ) * h) (q := h) (by positivity) hh.le,
              add_mul]
        _ = ∑' m : ℕ, ENNReal.ofReal ((m : ℝ) * h) * μ (levelSet n k j h m) +
              ENNReal.ofReal h * ∑' m : ℕ, μ (levelSet n k j h m) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        _ ≤ ∑' m : ℕ, ENNReal.ofReal ((m : ℝ) * h) * μ (levelSet n k j h m) +
              ENNReal.ofReal h * 1 := add_le_add le_rfl (mul_le_mul' le_rfl hsumA)
        _ = _ := by rw [mul_one]
    have hκJ : 0 ≤ κ / ((j : ℝ) - 1) := by positivity
    have hterm : ∀ m : ℕ, ENNReal.ofReal (κ / ((j : ℝ) - 1)) *
        (ENNReal.ofReal ((m : ℝ) * h) * μ (levelSet n k j h m)) =
        ENNReal.ofReal (κ * ((m : ℝ) * h) / ((j : ℝ) - 1)) * μ (levelSet n k j h m) := by
      intro m
      have hmul : κ / ((j : ℝ) - 1) * ((m : ℝ) * h) = κ * ((m : ℝ) * h) / ((j : ℝ) - 1) := by
        ring
      rw [← mul_assoc, ← ENNReal.ofReal_mul hκJ, hmul]
    calc ENNReal.ofReal (κ / ((j : ℝ) - 1)) *
          ∫⁻ p in pastEvent n k ∩ tameEvent n k j, ENNReal.ofReal (cellDropR n k p) ∂μ
        ≤ ENNReal.ofReal (κ / ((j : ℝ) - 1)) *
          (∑' m : ℕ, ENNReal.ofReal ((m : ℝ) * h) * μ (levelSet n k j h m) + ENNReal.ofReal h) :=
          mul_le_mul' le_rfl hint
      _ = ∑' m : ℕ, ENNReal.ofReal (κ * ((m : ℝ) * h) / ((j : ℝ) - 1)) * μ (levelSet n k j h m) +
          ENNReal.ofReal (κ / ((j : ℝ) - 1) * h) := by
          rw [mul_add, ← ENNReal.tsum_mul_left, ENNReal.ofReal_mul hκJ]
          congr 1
          exact tsum_congr hterm
      _ ≤ μ (firstCellEvent n k ∩ cellEvent n (k + j)) + ENNReal.ofReal (κ * h) := by
          refine add_le_add ((ENNReal.tsum_le_tsum hlevel).trans hsumD) ?_
          refine ENNReal.ofReal_le_ofReal ?_
          exact mul_le_mul_of_nonneg_right (div_le_self hκ0.le hJ1) hh.le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hmain := main ((ε : ℝ) / κ) (by positivity)
  have e1 : κ * ((ε : ℝ) / κ) = ε := by field_simp
  rw [e1, ENNReal.ofReal_coe_nnreal] at hmain
  exact hmain

/-- **The lower bound for the occupation of a later cell**: `P(B_k ∩ A_{k+j}) ≥
c/(j - 1) E[1_{C_k ∩ F} U_k]` for `1 + 6 log n < j`, from Shimura's Lemma 2 on the gap, a straight tube in
whitened coordinates on the cell `k + j` and the survival of `R` after it. -/
theorem occupancyLower_holds {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hL2 : ShimuraLemmaTwo γ)
    (hT : PlanarTubePositive) : OccupancyLower γ := by
  obtain ⟨c, hc, hgap⟩ := exists_le_measure_gap hL2
  obtain ⟨c₂, hc₂, hpoly⟩ := exists_pos_le_measure_polygon hγ0 hγ2 hT
  refine ⟨c * c₂ / (8 * Real.sqrt 2), by positivity, 30,
    fun μ hμ n hn k j hk1 hkn hj hkj => ?_⟩
  exact lower_core hμ hc hc₂ (fun b d Δ δ hd hΔ hΔ1 hδ hδ1 => hgap μ hμ b d Δ δ hd hΔ hΔ1 hδ hδ1)
    (fun a e he => hpoly μ hμ a e he) hn hk1 hkn hj hkj

end MatedCRT.PeanosphereTriplePoints
