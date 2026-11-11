import MatedCRT.FirstPass.S3i.ExitProbability
import MatedCRT.Proofs.WalkPotential.MarkovFixedTime

/-!
# Almost-sure exit from a finite set (plan 3.6 Lemma 1, conjunct 1)

For a finite set `A` with `FiniteExitData m A`, simple random walk started in `A` leaves `A` almost surely:
`srwLaw m a {x | vExitTime A x < ⊤} = 1` for `a ∈ A` (`srwLaw_vExitTime_lt_top_fp36`). This is the corrected first
conjunct of plan Lemma 1 (the printed `UsesEdges` conjunct is false at zero-degree boundary vertices).
The proof uses Armitage-Gardiner style geometric trials:

* A. finite exit routes: a directed positive-edge path from `a ∈ A` to `vBoundary`, truncated at its first vertex outside `A`
  (`exists_isExitRoute`);
* B. the route has positive probability, by the one-step Markov property (`srwLaw_routeCyl_pos`);
* C. uniform one-block survival `srwLaw m a (fpSurvives A N) ≤ r < 1` for `a ∈ A` (`finiteExitData_uniform_survival`);
* D. deterministic-time Markov iteration `P^a(survive kN) ≤ r^k` (`srwLaw_fpSurvives_mul_le`), hence `P^a(τ_A = ∞) = 0`.

Also packaged: `FP36LemmaOneCorrected` and `fp36LemmaOneCorrected_holds`.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

/-! ### A. Finite exit routes -/

/-- An exit route from `a` of length `n`: `pos 0 = a`, the first `n` positions lie in `A`,
consecutive positions up to `n` are joined by edges of `m`, and `pos n` is the first position outside `A`. -/
def IsExitRoute (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) (n : ℕ) (pos : ℕ → ℤ) : Prop :=
  pos 0 = a ∧ (∀ i < n, pos i ∈ A) ∧ (∀ i < n, m (pos i) (pos (i + 1)) ≠ 0) ∧ pos n ∉ A

/-- Truncating a directed path at its first vertex outside `A` gives an exit route. -/
theorem exists_isExitRoute_of_chain (m : ℤ → ℤ → ℕ) (A : Set ℤ) :
    ∀ (p : List ℤ) (a : ℤ), p.head? = some a → p.IsChain (fun c d => m c d ≠ 0) →
      (∃ c ∈ p, c ∉ A) → ∃ n pos, IsExitRoute m A a n pos := by
  intro p
  induction p with
  | nil => intro a h; simp at h
  | cons c q ih =>
    intro a hhead hchain hout
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    by_cases hca : c ∈ A
    · obtain ⟨d, hd, hdA⟩ := hout
      rcases List.mem_cons.1 hd with rfl | hdq
      · exact absurd hca hdA
      cases q with
      | nil => simp at hdq
      | cons b r =>
        have hedge : m c b ≠ 0 := (List.isChain_cons_cons.1 hchain).1
        have hchain' := (List.isChain_cons_cons.1 hchain).2
        obtain ⟨n, pos, h0, hA', hE, hout'⟩ := ih b rfl hchain' ⟨d, hdq, hdA⟩
        refine ⟨n + 1, fun i => if i = 0 then c else pos (i - 1), by simp, ?_, ?_, ?_⟩
        · intro i _
          by_cases hi0 : i = 0
          · simp [hi0, hca]
          · simp only [hi0, ite_false]
            exact hA' (i - 1) (by omega)
        · intro i hi
          by_cases hi0 : i = 0
          · simp [hi0, h0, hedge]
          · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            simpa using hE j (by omega)
        · simpa using hout'
    · exact ⟨0, fun _ => c, rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _), hca⟩

/-- Every point `a ∈ A` of a finite exit datum starts an exit route. -/
theorem exists_isExitRoute {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hA : FiniteExitData m A) {a : ℤ} (ha : a ∈ A) :
    ∃ n pos, IsExitRoute m A a n pos := by
  obtain ⟨b, hb, p, hp⟩ := hA.2.2 a ha
  obtain ⟨hhead, hlast, -, hchain⟩ := hp
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hlast
  refine exists_isExitRoute_of_chain m A p a hhead hchain ⟨b, ?_, hb.1⟩
  rw [hys]
  simp

/-! ### B. Positive probability of a route -/

/-- The cylinder of a route prefix: the first `n + 1` positions are prescribed. -/
def fpRouteCyl (n : ℕ) (pos : ℕ → ℤ) : Set (ℕ → ℤ) := {x | ∀ i ≤ n, x i = pos i}

theorem measurableSet_fpRouteCyl (n : ℕ) (pos : ℕ → ℤ) : MeasurableSet (fpRouteCyl n pos) := by
  have h : fpRouteCyl n pos = ⋂ i ∈ Set.Iic n, (fun x : ℕ → ℤ => x i) ⁻¹' {pos i} := by
    ext x
    simp [fpRouteCyl]
  rw [h]
  exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
    (measurable_pi_apply i) (measurableSet_singleton _)

/-- The paths that stay in `A` up to time `N`. -/
def fpSurvives (A : Set ℤ) (N : ℕ) : Set (ℕ → ℤ) := {x | ∀ j ≤ N, x j ∈ A}

theorem measurableSet_fpSurvives (A : Set ℤ) (N : ℕ) : MeasurableSet (fpSurvives A N) := by
  have h : fpSurvives A N = ⋂ j ∈ Set.Iic N, (fun x : ℕ → ℤ => x j) ⁻¹' A := by
    ext x
    simp [fpSurvives]
  rw [h]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
    (measurable_pi_apply j) (Set.to_countable A).measurableSet

/-- One step from a vertex of positive degree reaches a neighbour `v` with positive probability. -/
theorem srwStep_singleton_pos {m : ℤ → ℤ → ℕ} {u v : ℤ} (hdeg : 0 < mdeg m u) (huv : m u v ≠ 0) :
    0 < srwStep m u {v} := by
  have hfin := finite_nbrs_of_mdeg_ne_zero (ne_of_gt hdeg)
  have hmem : v ∈ hfin.toFinset := hfin.mem_toFinset.2 huv
  have h := lintegral_indicator_one (μ := srwStep m u) (measurableSet_singleton v)
  have hv1 : ({v} : Set ℤ).indicator (1 : ℤ → ℝ≥0∞) v = 1 := by simp
  have hsum : (m u v : ℝ≥0∞) * ({v} : Set ℤ).indicator (1 : ℤ → ℝ≥0∞) v ≤
      ∑ b ∈ hfin.toFinset, (m u b : ℝ≥0∞) * ({v} : Set ℤ).indicator (1 : ℤ → ℝ≥0∞) b :=
    Finset.single_le_sum (f := fun b => (m u b : ℝ≥0∞) * ({v} : Set ℤ).indicator (1 : ℤ → ℝ≥0∞) b)
      (fun b _ => zero_le) hmem
  have hS : (0 : ℝ≥0∞) < ∑ b ∈ hfin.toFinset, (m u b : ℝ≥0∞) * ({v} : Set ℤ).indicator (1 : ℤ → ℝ≥0∞) b := by
    refine lt_of_lt_of_le ?_ hsum
    rw [hv1, mul_one]
    exact pos_iff_ne_zero.2 (by exact_mod_cast huv)
  rw [← h, lintegral_srwStep_of_finite hfin (ne_of_gt hdeg)]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)) hS.ne'

/-- A route cylinder has positive probability from its start (by induction on the length,
using the one-step decomposition `srwLaw_apply_eq_lintegral` at the first step). -/
theorem srwLaw_fpRouteCyl_pos {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hdeg : ∀ u ∈ A, 0 < mdeg m u) :
    ∀ (n : ℕ) (pos : ℕ → ℤ) (b : ℤ), pos 0 = b → (∀ i < n, pos i ∈ A) →
      (∀ i < n, m (pos i) (pos (i + 1)) ≠ 0) → 0 < srwLaw m b (fpRouteCyl n pos) := by
  intro n
  induction n with
  | zero =>
    intro pos b hb _ _
    have hset : fpRouteCyl 0 pos = {x : ℕ → ℤ | x 0 = b} := by
      ext x
      simp [fpRouteCyl, hb]
    have hm : MeasurableSet {x : ℕ → ℤ | x 0 = b} := by
      have h : MeasurableSet ((fun x : ℕ → ℤ => x 0) ⁻¹' {b}) := (measurable_pi_apply 0) (measurableSet_singleton b)
      exact h
    have h0 : srwLaw m b {x : ℕ → ℤ | x 0 = b}ᶜ = 0 := ae_iff.1 (srwLaw_ae_start m b)
    have h1 := prob_add_prob_compl (μ := srwLaw m b) hm
    rw [h0, add_zero] at h1
    rw [hset, h1]
    exact one_pos
  | succ n ih =>
    intro pos b hb hA hE
    subst hb
    have hcyl := srwLaw_apply_eq_lintegral m (pos 0) (measurableSet_fpRouteCyl (n + 1) pos)
    have hset : pathCons (pos 0) ⁻¹' fpRouteCyl (n + 1) pos = fpRouteCyl n (fun i => pos (i + 1)) := by
      ext x
      simp only [Set.mem_preimage, fpRouteCyl, Set.mem_ofPred_eq]
      constructor
      · intro h i hi
        simpa [pathCons] using h (i + 1) (by omega)
      · intro h i hi
        rcases i with _ | j
        · simp [pathCons]
        · simpa [pathCons] using h j (by omega)
    rw [hset] at hcyl
    have hpos1 : 0 < srwLaw m (pos 1) (fpRouteCyl n (fun i => pos (i + 1))) :=
      ih (fun i => pos (i + 1)) (pos 1) rfl (fun i hi => hA (i + 1) (by omega))
        (fun i hi => hE (i + 1) (by omega))
    have hstep : 0 < srwStep m (pos 0) {pos 1} :=
      srwStep_singleton_pos (hdeg (pos 0) (hA 0 (by omega))) (hE 0 (by omega))
    rw [hcyl]
    have hind : ∫⁻ c, ({pos 1} : Set ℤ).indicator
          (fun _ => srwLaw m (pos 1) (fpRouteCyl n (fun i => pos (i + 1)))) c ∂srwStep m (pos 0)
        ≤ ∫⁻ c, srwLaw m c (fpRouteCyl n (fun i => pos (i + 1))) ∂srwStep m (pos 0) := by
      refine lintegral_mono fun c => ?_
      by_cases hc : c = pos 1
      · subst hc
        simp
      · simp [hc]
    rw [lintegral_indicator_const (measurableSet_singleton _)] at hind
    exact lt_of_lt_of_le (ENNReal.mul_pos hpos1.ne' hstep.ne') hind

/-- A route prefix of length `n` with `pos n ∉ A` is disjoint from the survival event up to time `N ≥ n`. -/
theorem fpSurvives_subset_compl_routeCyl {A : Set ℤ} {n N : ℕ} (hn : n ≤ N) {pos : ℕ → ℤ} (hpos : pos n ∉ A) :
    fpSurvives A N ⊆ (fpRouteCyl n pos)ᶜ := by
  intro x hx hcyl
  apply hpos
  rw [← hcyl n le_rfl]
  exact hx n hn

/-! ### C. Uniform one-block survival -/

/-- **Uniform one-block contraction.** For a finite exit datum there are a block length `N` and `r < 1` with
`P^a(stay in A up to time N) ≤ r` for every `a ∈ A`. -/
theorem finiteExitData_uniform_survival {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hA : FiniteExitData m A) :
    ∃ N : ℕ, ∃ r : ℝ≥0∞, r < 1 ∧ ∀ a ∈ A, srwLaw m a (fpSurvives A N) ≤ r := by
  have hroute : ∀ a : ℤ, ∃ n pos, a ∈ A → IsExitRoute m A a n pos := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨n, pos, h⟩ := exists_isExitRoute hA ha
      exact ⟨n, pos, fun _ => h⟩
    · exact ⟨0, fun _ => a, fun h => absurd h ha⟩
  choose nr posr hr using hroute
  obtain ⟨N, hN⟩ : ∃ N, N = 1 + ∑ a ∈ hA.1.toFinset, nr a := ⟨_, rfl⟩
  have hNle : ∀ a ∈ A, nr a ≤ N := fun a ha => by
    have : nr a ≤ ∑ b ∈ hA.1.toFinset, nr b :=
      Finset.single_le_sum (f := nr) (fun b _ => Nat.zero_le _) (hA.1.mem_toFinset.2 ha)
    omega
  have hblock : ∀ a ∈ A, srwLaw m a (fpSurvives A N) < 1 := by
    intro a ha
    obtain ⟨h0, hA', hE, hout⟩ := hr a ha
    have hpos := srwLaw_fpRouteCyl_pos hA.2.1 (nr a) (posr a) a h0 hA' hE
    calc srwLaw m a (fpSurvives A N)
        ≤ srwLaw m a (fpRouteCyl (nr a) (posr a))ᶜ :=
          measure_mono (fpSurvives_subset_compl_routeCyl (hNle a ha) hout)
      _ = 1 - srwLaw m a (fpRouteCyl (nr a) (posr a)) :=
          prob_compl_eq_one_sub (measurableSet_fpRouteCyl _ _)
      _ < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'
  refine ⟨N, hA.1.toFinset.sup (fun a => srwLaw m a (fpSurvives A N)), ?_, ?_⟩
  · rw [Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞) < 1)]
    intro a ha
    exact hblock a (hA.1.mem_toFinset.1 ha)
  · intro a ha
    exact Finset.le_sup (f := fun a => srwLaw m a (fpSurvives A N)) (hA.1.mem_toFinset.2 ha)

/-! ### D. Deterministic-time Markov iteration -/

/-- The survival event splits at a deterministic time `n`: `P^a(survive n+N) = ∫_{survive n} P^{x_n}(survive N) dP^a`. -/
theorem srwLaw_fpSurvives_add (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) (n N : ℕ) :
    srwLaw m a (fpSurvives A (n + N)) =
      ∫⁻ x in fpSurvives A n, srwLaw m (x n) (fpSurvives A N) ∂srwLaw m a := by
  have h := MatedCRT.srwLaw_markov m a n {f : Fin (n + 1) → ℤ | ∀ i, f i ∈ A}
    (measurableSet_fpSurvives A N)
  have hL : {x : ℕ → ℤ | MatedCRT.pathHist n x ∈ {f : Fin (n + 1) → ℤ | ∀ i, f i ∈ A} ∧
      WalkPotential.pathShift n x ∈ fpSurvives A N} = fpSurvives A (n + N) := by
    ext x
    simp only [Set.mem_ofPred_eq, MatedCRT.pathHist, WalkPotential.pathShift, fpSurvives]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      by_cases hjn : j ≤ n
      · exact h1 ⟨j, by omega⟩
      · have := h2 (j - n) (by omega)
        rwa [show n + (j - n) = j by omega] at this
    · intro h
      refine ⟨fun i => h (i : ℕ) (by have := i.isLt; omega), fun j hj => ?_⟩
      exact h (n + j) (by omega)
  have hR : {x : ℕ → ℤ | MatedCRT.pathHist n x ∈ {f : Fin (n + 1) → ℤ | ∀ i, f i ∈ A}} =
      fpSurvives A n := by
    ext x
    simp only [Set.mem_ofPred_eq, MatedCRT.pathHist, fpSurvives]
    constructor
    · intro h j hj
      exact h ⟨j, by omega⟩
    · intro h i
      exact h i (by have := i.isLt; omega)
  rw [← hL, h, hR]

/-- The geometric bound `P^a(stay in A up to time kN) ≤ r^k`. -/
theorem srwLaw_fpSurvives_mul_le {m : ℤ → ℤ → ℕ} {A : Set ℤ} {N : ℕ} {r : ℝ≥0∞}
    (hblock : ∀ a ∈ A, srwLaw m a (fpSurvives A N) ≤ r) (a : ℤ) :
    ∀ k : ℕ, srwLaw m a (fpSurvives A (k * N)) ≤ r ^ k := by
  intro k
  induction k with
  | zero =>
    rw [pow_zero]
    exact prob_le_one
  | succ k ih =>
    rw [Nat.succ_mul, srwLaw_fpSurvives_add]
    calc ∫⁻ x in fpSurvives A (k * N), srwLaw m (x (k * N)) (fpSurvives A N) ∂srwLaw m a
        ≤ ∫⁻ x in fpSurvives A (k * N), r ∂srwLaw m a := by
          refine setLIntegral_mono' (measurableSet_fpSurvives A (k * N)) fun x hx => ?_
          exact hblock (x (k * N)) (hx (k * N) le_rfl)
      _ = r * srwLaw m a (fpSurvives A (k * N)) := by
          rw [setLIntegral_const]
      _ ≤ r * r ^ k := mul_le_mul_of_nonneg_left ih zero_le
      _ = r ^ (k + 1) := by rw [pow_succ, mul_comm]

/-! ### Almost-sure exit (final step) -/

/-- **Almost-sure exit from a finite exit datum** (plan 3.6 Lemma 1, conjunct 1, corrected): for `a ∈ A`,
the walk started at `a` leaves `A` with probability one. -/
theorem srwLaw_vExitTime_lt_top_fp36 {m : ℤ → ℤ → ℕ} {A : Set ℤ} (hA : FiniteExitData m A) :
    ∀ a ∈ A, srwLaw m a {x | vExitTime A x < ⊤} = 1 := by
  obtain ⟨N, r, hr, hblock⟩ := finiteExitData_uniform_survival hA
  intro a ha
  have hsub : ∀ k : ℕ, {x : ℕ → ℤ | vExitTime A x = ⊤} ⊆ fpSurvives A (k * N) := fun k x hx =>
    natCast_lt_vExitTime_iff.1 (by
      rw [show vExitTime A x = ⊤ from hx]
      exact ENat.natCast_lt_top _)
  have hnever : srwLaw m a {x : ℕ → ℤ | vExitTime A x = ⊤} = 0 := by
    have hle : ∀ k : ℕ, srwLaw m a {x : ℕ → ℤ | vExitTime A x = ⊤} ≤ r ^ k := fun k =>
      (measure_mono (hsub k)).trans (srwLaw_fpSurvives_mul_le hblock a k)
    exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) hle) (zero_le)
  have hmeas : MeasurableSet {x : ℕ → ℤ | vExitTime A x = ⊤} :=
    measurable_vExitTime A (measurableSet_singleton ⊤)
  have hcompl : {x : ℕ → ℤ | vExitTime A x < ⊤} = {x : ℕ → ℤ | vExitTime A x = ⊤}ᶜ := by
    ext x
    simp [lt_top_iff_ne_top]
  rw [hcompl]
  exact (prob_compl_eq_one_iff hmeas).2 hnever

/-! ### The corrected interface of plan Lemma 1 -/

open Classical in
/-- The corrected interface of plan Lemma 1: the first conjunct is almost-sure exit from `A`, in place of
the `UsesEdges` conjunct of `FP36LemmaOne` (QuenchedBounds.lean:26), which is false at zero-degree boundary vertices.
The old `FP36LemmaOne` is left untouched. -/
def FP36LemmaOneCorrected : Prop :=
  ∀ {m : ℤ → ℤ → ℕ} {A B : Set ℤ},
    FiniteExitData m A →
      (∀ a ∈ A,
        srwLaw m a {x | vExitTime A x < ⊤} = 1) ∧
      (∀ a : ℤ,
        0 ≤ exitHitProb m A B a ∧
        exitHitProb m A B a ≤ 1) ∧
      (∀ a ∈ A,
        mLaplacian m (exitHitProb m A B) a = 0) ∧
      (∀ a ∉ A,
        exitHitProb m A B a =
          if a ∈ B then 1 else 0)

/-- The corrected plan Lemma 1 holds: almost-sure exit (this file) and conjuncts 2-4 (ExitProbability.lean). -/
theorem fp36LemmaOneCorrected_holds : FP36LemmaOneCorrected := by
  intro m A B hA
  exact ⟨srwLaw_vExitTime_lt_top_fp36 hA, fun a => exitHitProb_nonneg_le_one m A B a,
    fun a ha => exitHitProb_mLaplacian_eq_zero m hA ha, fun _ ha => exitHitProb_of_not_mem m ha⟩

end FirstPass36
end MatedCRT

#print axioms MatedCRT.FirstPass36.srwLaw_vExitTime_lt_top_fp36
#print axioms MatedCRT.FirstPass36.fp36LemmaOneCorrected_holds
