import MatedCRT.Proofs.IDLA.StrongMarkov
import MatedCRT.Proofs.Sec6.ChanceOfBeingAbsorbed.Chernoff

/-!
# Lemma 6.3: the exchangeability of IDLA (Diaconis-Fulton 1991, Section 4)

On any multigraph `m` on `ℤ`, write `F_G(A; z₁, …, z_n) = E[G(A(A; z₁, …, z_n))]` for the expected value of a weight
`G ≥ 0` of the IDLA aggregate obtained from the occupied set `A` by releasing independent simple random walks from
`z₁, …, z_n`, in this order (`aggValue`). The main result of this file is the **exchangeability of IDLA**:
`F_G(A; z₁, …, z_n)` depends on the starting sites only as a multiset (`aggValue_perm`).

The proof is the two-walker exchange (`aggValue_swap`), from two facts on the first exit site `o(x)` of a path `x`
from `A` (`firstExitSite`):
* the **strong Markov property at the exit time of `A`** (`lintegral_firstExitSite_of_subset`): for `A ⊆ A'`, the
  first exit site from `A'` is the first exit site `c` from `A` if `c ∉ A'`, and otherwise that of a fresh walk
  started at `c`;
* hence, releasing the walkers from `z` and `w` in turn, the joint law of `(o(x), o(y))` (`x` from `z`, `y` from `w`,
  both first exit sites from `A`) determines the final aggregate through a kernel `pairKernel` which is symmetric in
  its two arguments; Tonelli's theorem exchanges the walkers.

Neither termination of the walks nor any property of `m` (symmetry, local finiteness, connectedness) is used: a walker
which never leaves the occupied set leaves the aggregate unchanged.

The general recursion `runValue` evaluates `E[H(state)]` for the stopped process of Definition 6.2 (state = occupied
set and stopped positions); `lintegral_walkersLaw_foldl` identifies it with the integral against `walkersLaw`.
-/

namespace MatedCRT

namespace AbelianIDLA

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ### One walker as a function of its first exit site -/

open Classical in
/-- The state (occupied set, stopped positions) after one walker of the stopped process of Definition 6.2, as a
function of the first exit site of the walker from the occupied set. -/
noncomputable def stepOpt (U : Set ℤ) (s : Set ℤ × List ℤ) : Option ℤ → Set ℤ × List ℤ
  | some b => if b ∈ U then (s.1 ∪ {b}, s.2) else (s.1, s.2 ++ [b])
  | none => s

theorem idlaStep_eq_stepOpt (U : Set ℤ) (s : Set ℤ × List ℤ) (x : ℕ → ℤ) :
    idlaStep U s x = stepOpt U s (firstExitSite s.1 x) := by
  unfold idlaStep stepOpt
  cases firstExitSite s.1 x with
  | none => rfl
  | some b => rfl

theorem nextAgg_univ_some (A : Set ℤ) (b : ℤ) : Absorption.nextAgg univ A (some b) = A ∪ {b} :=
  ite_eq_left (mem_univ b)

theorem idlaStep_univ (A : Set ℤ) (P : List ℤ) (x : ℕ → ℤ) :
    idlaStep univ (A, P) x = (Absorption.nextAgg univ A (firstExitSite A x), P) := by
  rw [idlaStep_eq_stepOpt]
  cases firstExitSite A x with
  | none => rfl
  | some b => exact (ite_eq_left (mem_univ b)).trans (by rw [nextAgg_univ_some])

/-- A path started outside `A` leaves `A` at its starting site. -/
theorem firstExitSite_of_start_not_mem {A : Set ℤ} {x : ℕ → ℤ} (h : x 0 ∉ A) : firstExitSite A x = some (x 0) :=
  Absorption.firstExitSite_eq_some_iff.2 ⟨0, rfl, h, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- If the path stays in `A'` up to time `n`, its first exit site from `A'` is that of the path shifted by `n`. -/
theorem firstExitSite_pathShift {A' : Set ℤ} {x : ℕ → ℤ} {n : ℕ} (h : ∀ j < n, x j ∈ A') :
    firstExitSite A' (pathShift n x) = firstExitSite A' x := by
  cases ho : firstExitSite A' x with
  | none =>
    rw [Absorption.firstExitSite_eq_none_iff] at ho ⊢
    exact fun k => ho (k + n)
  | some c =>
    obtain ⟨k, hk, hc, hlt⟩ := Absorption.firstExitSite_eq_some_iff.1 ho
    have hnk : n ≤ k := by
      by_contra hkn
      exact hc (hk ▸ h k (by omega))
    refine Absorption.firstExitSite_eq_some_iff.2 ⟨k - n, ?_, hc, fun j hj => hlt (j + n) (by omega)⟩
    show x (k - n + n) = c
    rw [Nat.sub_add_cancel hnk]
    exact hk

theorem vHitTime_compl (A : Set ℤ) (x : ℕ → ℤ) : vHitTime Aᶜ x = vExitTime A x := by
  rw [vHitTime, compl_compl]

/-- At the hitting time `n` of `Aᶜ`, the path has stayed in `A` before `n` and is outside `A` at `n`. -/
theorem hitTime_compl_facts {A : Set ℤ} {x : ℕ → ℤ} {n : ℕ} (hx : vHitTime Aᶜ x = n) :
    (∀ j < n, x j ∈ A) ∧ x n ∉ A := by
  rw [vHitTime_compl] at hx
  refine ⟨fun j hj => mem_of_lt_vExitTime (by rw [hx]; exact_mod_cast hj), apply_vExitTime_not_mem hx⟩

/-! ### Measurability -/

/-- A function of the first exit site from `A` is a measurable function of the path. -/
theorem measurable_firstExitSite_comp (A : Set ℤ) {β : Type*} [MeasurableSpace β] (c : Option ℤ → β) :
    Measurable fun x : ℕ → ℤ => c (firstExitSite A x) := by
  refine fun t _ => ?_
  have h : (fun x : ℕ → ℤ => c (firstExitSite A x)) ⁻¹' t =
      ⋃ o : Option ℤ, ⋃ (_ : c o ∈ t), {x : ℕ → ℤ | firstExitSite A x = o} := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq, exists_prop]
    exact ⟨fun hx => ⟨_, hx, rfl⟩, fun ⟨o, ho, hxo⟩ => hxo ▸ ho⟩
  rw [h]
  exact MeasurableSet.iUnion fun o => MeasurableSet.iUnion fun _ =>
    Absorption.measurableSet_firstExitSite_eq A o

/-- A function of the first exit sites from `A` of two paths is measurable on pairs of paths. -/
theorem measurable_firstExitSite_comp₂ (A : Set ℤ) (K : Option ℤ → Option ℤ → ℝ≥0∞) :
    Measurable fun p : (ℕ → ℤ) × (ℕ → ℤ) => K (firstExitSite A p.1) (firstExitSite A p.2) := by
  refine fun t _ => ?_
  have h : (fun p : (ℕ → ℤ) × (ℕ → ℤ) => K (firstExitSite A p.1) (firstExitSite A p.2)) ⁻¹' t =
      ⋃ o : Option ℤ, ⋃ o' : Option ℤ, ⋃ (_ : K o o' ∈ t),
        {x : ℕ → ℤ | firstExitSite A x = o} ×ˢ {y : ℕ → ℤ | firstExitSite A y = o'} := by
    ext p
    simp only [mem_preimage, mem_iUnion, mem_prod, mem_ofPred_eq, exists_prop]
    exact ⟨fun hp => ⟨_, _, hp, rfl, rfl⟩, fun ⟨o, o', ho, h1, h2⟩ => h1 ▸ h2 ▸ ho⟩
  rw [h]
  exact MeasurableSet.iUnion fun o => MeasurableSet.iUnion fun o' => MeasurableSet.iUnion fun _ =>
    (Absorption.measurableSet_firstExitSite_eq A o).prod (Absorption.measurableSet_firstExitSite_eq A o')

/-- Every event of the state of the stopped process after the walkers `xs` is measurable. -/
theorem measurableSet_foldl_idlaStep (U : Set ℤ) :
    ∀ (k : ℕ) (s : Set ℤ × List ℤ) (p : Set ℤ × List ℤ → Prop),
      MeasurableSet {xs : Fin k → ℕ → ℤ | p ((List.ofFn xs).foldl (idlaStep U) s)}
  | 0, s, p => by
    have h0 : ∀ xs : Fin 0 → ℕ → ℤ, List.ofFn xs = [] := fun _ => List.ofFn_zero
    simp only [h0, List.foldl_nil]
    exact MeasurableSet.const _
  | k + 1, s, p => by
    have h : {xs : Fin (k + 1) → ℕ → ℤ | p ((List.ofFn xs).foldl (idlaStep U) s)} =
        ⋃ o : Option ℤ, (fun xs : Fin (k + 1) → ℕ → ℤ => xs 0) ⁻¹' {x | firstExitSite s.1 x = o} ∩
          (fun xs : Fin (k + 1) → ℕ → ℤ => fun i : Fin k => xs i.succ) ⁻¹'
            {ys | p ((List.ofFn ys).foldl (idlaStep U) (stepOpt U s o))} := by
      ext xs
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, List.ofFn_succ, List.foldl_cons,
        idlaStep_eq_stepOpt]
      constructor
      · intro hx
        exact ⟨_, rfl, hx⟩
      · rintro ⟨o, ho, hx⟩
        rw [ho]
        exact hx
    rw [h]
    exact MeasurableSet.iUnion fun o =>
      ((Absorption.measurableSet_firstExitSite_eq s.1 o).preimage (measurable_pi_apply 0)).inter
        ((measurableSet_foldl_idlaStep U k (stepOpt U s o) p).preimage
          (Measurable.of_eval fun i => measurable_pi_apply _))

/-- Every function of the state of the stopped process after the walkers `xs` is measurable. -/
theorem measurable_foldl_idlaStep (U : Set ℤ) {β : Type*} [MeasurableSpace β] (g : Set ℤ × List ℤ → β) (k : ℕ)
    (s : Set ℤ × List ℤ) : Measurable fun xs : Fin k → ℕ → ℤ => g ((List.ofFn xs).foldl (idlaStep U) s) :=
  fun t _ => measurableSet_foldl_idlaStep U k s fun s' => g s' ∈ t

/-! ### The walker recursions -/

/-- `E[H(state)]` for the stopped process (absorption region `U`) from the state `s`, fresh independent simple random
walks being released from the sites `L` in order. -/
noncomputable def runValue (m : ℤ → ℤ → ℕ) (U : Set ℤ) (H : Set ℤ × List ℤ → ℝ≥0∞) :
    Set ℤ × List ℤ → List ℤ → ℝ≥0∞
  | s, [] => H s
  | s, z :: L => ∫⁻ x, runValue m U H (idlaStep U s x) L ∂srwLaw m z

/-- `F_G(A; L) = E[G(A(A; L))]`: IDLA (no stopping) from the occupied set `A`, fresh independent simple random walks
being released from the sites `L` in order. -/
noncomputable def aggValue (m : ℤ → ℤ → ℕ) (G : Set ℤ → ℝ≥0∞) : Set ℤ → List ℤ → ℝ≥0∞
  | A, [] => G A
  | A, z :: L => ∫⁻ x, aggValue m G (Absorption.nextAgg univ A (firstExitSite A x)) L ∂srwLaw m z

@[simp] theorem runValue_nil (m : ℤ → ℤ → ℕ) (U : Set ℤ) (H : Set ℤ × List ℤ → ℝ≥0∞) (s : Set ℤ × List ℤ) :
    runValue m U H s [] = H s := by
  rw [runValue]

theorem runValue_cons (m : ℤ → ℤ → ℕ) (U : Set ℤ) (H : Set ℤ × List ℤ → ℝ≥0∞) (s : Set ℤ × List ℤ) (z : ℤ)
    (L : List ℤ) : runValue m U H s (z :: L) = ∫⁻ x, runValue m U H (idlaStep U s x) L ∂srwLaw m z := by
  rw [runValue]

@[simp] theorem aggValue_nil (m : ℤ → ℤ → ℕ) (G : Set ℤ → ℝ≥0∞) (A : Set ℤ) : aggValue m G A [] = G A := by
  rw [aggValue]

theorem aggValue_cons (m : ℤ → ℤ → ℕ) (G : Set ℤ → ℝ≥0∞) (A : Set ℤ) (z : ℤ) (L : List ℤ) :
    aggValue m G A (z :: L) = ∫⁻ x, aggValue m G (Absorption.nextAgg univ A (firstExitSite A x)) L ∂srwLaw m z := by
  rw [aggValue]

/-- The integral against `walkersLaw` of a function of the final state is the walker recursion `runValue`. -/
theorem lintegral_walkersLaw_foldl (m : ℤ → ℤ → ℕ) (U : Set ℤ) (H : Set ℤ × List ℤ → ℝ≥0∞) :
    ∀ (k : ℕ) (s : Set ℤ × List ℤ) (a : Fin k → ℤ),
      ∫⁻ xs, H ((List.ofFn xs).foldl (idlaStep U) s) ∂walkersLaw m a = runValue m U H s (List.ofFn a)
  | 0, s, a => by
    have h0 : ∀ xs : Fin 0 → ℕ → ℤ, List.ofFn xs = [] := fun _ => List.ofFn_zero
    simp only [h0, List.foldl_nil, List.ofFn_zero, runValue_nil, lintegral_const, measure_univ, mul_one]
  | k + 1, s, a => by
    rw [Absorption.lintegral_walkersLaw_succ m a _ (measurable_foldl_idlaStep U H (k + 1) s),
      show List.ofFn a = a 0 :: List.ofFn (fun i : Fin k => a i.succ) from List.ofFn_succ, runValue_cons]
    refine lintegral_congr fun x => ?_
    simp only [Absorption.ofFn_cons', List.foldl_cons]
    exact lintegral_walkersLaw_foldl m U H k (idlaStep U s x) fun i => a i.succ

/-- Without stopping (`U = univ`), the recursion only sees the occupied set. -/
theorem runValue_univ (m : ℤ → ℤ → ℕ) (G : Set ℤ → ℝ≥0∞) :
    ∀ (L : List ℤ) (A : Set ℤ) (P : List ℤ), runValue m univ (fun s => G s.1) (A, P) L = aggValue m G A L
  | [], A, P => by rw [runValue_nil, aggValue_nil]
  | z :: L, A, P => by
    rw [runValue_cons, aggValue_cons]
    refine lintegral_congr fun x => ?_
    rw [idlaStep_univ, runValue_univ m G L]

/-! ### The strong Markov property at the exit time -/

/-- Splitting an integral over paths according to the value of the hitting time of `D`. -/
theorem lintegral_eq_top_add_tsum (μ : Measure (ℕ → ℤ)) (D : Set ℤ) {f : (ℕ → ℤ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, {x : ℕ → ℤ | vHitTime D x = ⊤}.indicator f x ∂μ +
      ∑' n : ℕ, ∫⁻ x, {x : ℕ → ℤ | vHitTime D x = n}.indicator f x ∂μ := by
  have hmeas : ∀ n : ℕ, Measurable ({x : ℕ → ℤ | vHitTime D x = n}.indicator f) := fun n =>
    hf.indicator (measurableSet_vHitTime_eq D n)
  have htop : Measurable ({x : ℕ → ℤ | vHitTime D x = ⊤}.indicator f) :=
    hf.indicator (show MeasurableSet {x : ℕ → ℤ | vHitTime D x = ⊤} from
      measurable_vHitTime D (measurableSet_singleton ⊤))
  rw [← lintegral_tsum fun n => (hmeas n).aemeasurable, ← lintegral_add_left htop]
  refine lintegral_congr fun x => ?_
  by_cases h : vHitTime D x = ⊤
  · have h0 : ∀ n : ℕ, {x : ℕ → ℤ | vHitTime D x = n}.indicator f x = 0 := fun n =>
      indicator_of_notMem (show x ∉ {x : ℕ → ℤ | vHitTime D x = n} from fun hx =>
        ENat.top_ne_natCast n (h.symm.trans (show vHitTime D x = n from hx))) _
    rw [indicator_of_mem (show x ∈ {x : ℕ → ℤ | vHitTime D x = ⊤} from h), ENNReal.tsum_eq_zero.2 h0, add_zero]
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h
    have h0 : ∀ n : ℕ, n ≠ k → {x : ℕ → ℤ | vHitTime D x = n}.indicator f x = 0 := fun n hn =>
      indicator_of_notMem (show x ∉ {x : ℕ → ℤ | vHitTime D x = n} from fun hx =>
        hn (Nat.cast_inj.1 (hk.trans (show vHitTime D x = n from hx))).symm) _
    rw [tsum_eq_single k h0, indicator_of_mem (show x ∈ {x : ℕ → ℤ | vHitTime D x = k} from hk.symm),
      indicator_of_notMem (show x ∉ {x : ℕ → ℤ | vHitTime D x = ⊤} from h), zero_add]

open Classical in
/-- The continuation, at the first exit site `o` from `A ⊆ A'`, of a functional `Ψ` of the first exit site from
`A'`: the walker has left `A'` at `c` if `c ∉ A'`, and otherwise continues as a fresh walk from `c`. -/
noncomputable def exitCont (m : ℤ → ℤ → ℕ) (A' : Set ℤ) (Ψ : Option ℤ → ℝ≥0∞) : Option ℤ → ℝ≥0∞
  | none => Ψ none
  | some c => if c ∈ A' then ∫⁻ y, Ψ (firstExitSite A' y) ∂srwLaw m c else Ψ (some c)

theorem hitSplit_left {A A' : Set ℤ} (hA : A ⊆ A') (Ψ : Option ℤ → ℝ≥0∞) (n : ℕ) (y : ℕ → ℤ) :
    {y : ℕ → ℤ | vHitTime Aᶜ y = n}.indicator (fun y => Ψ (firstExitSite A' y)) y =
      {y : ℕ → ℤ | vHitTime Aᶜ y = n}.indicator
          (fun y => A'.indicator 1 (y n) * Ψ (firstExitSite A' (pathShift n y))) y +
        {y : ℕ → ℤ | vHitTime Aᶜ y = n}.indicator (fun y => A'ᶜ.indicator (fun c => Ψ (some c)) (y n)) y := by
  by_cases hy : vHitTime Aᶜ y = n
  · have hyE : y ∈ {y : ℕ → ℤ | vHitTime Aᶜ y = n} := hy
    rw [indicator_of_mem hyE, indicator_of_mem hyE, indicator_of_mem hyE]
    obtain ⟨hpre, -⟩ := hitTime_compl_facts hy
    by_cases hc : y n ∈ A'
    · rw [indicator_of_mem hc, indicator_of_notMem (fun h => h hc : y n ∉ A'ᶜ), Pi.one_apply, one_mul, add_zero,
        firstExitSite_pathShift fun j hj => hA (hpre j hj)]
    · rw [indicator_of_notMem hc, indicator_of_mem (hc : y n ∈ A'ᶜ), zero_mul, zero_add,
        Absorption.firstExitSite_eq_some_iff.2 ⟨n, rfl, hc, fun j hj => hA (hpre j hj)⟩]
  · have hyE : y ∉ {y : ℕ → ℤ | vHitTime Aᶜ y = n} := hy
    rw [indicator_of_notMem hyE, indicator_of_notMem hyE, indicator_of_notMem hyE, add_zero]

theorem hitSplit_right (m : ℤ → ℤ → ℕ) {A A' : Set ℤ} (Ψ : Option ℤ → ℝ≥0∞) (n : ℕ) (y : ℕ → ℤ) :
    {y : ℕ → ℤ | vHitTime Aᶜ y = n}.indicator (fun y => exitCont m A' Ψ (firstExitSite A y)) y =
      {y : ℕ → ℤ | vHitTime Aᶜ y = n}.indicator
          (fun y => A'.indicator 1 (y n) * ∫⁻ y', Ψ (firstExitSite A' y') ∂srwLaw m (y n)) y +
        {y : ℕ → ℤ | vHitTime Aᶜ y = n}.indicator (fun y => A'ᶜ.indicator (fun c => Ψ (some c)) (y n)) y := by
  by_cases hy : vHitTime Aᶜ y = n
  · have hyE : y ∈ {y : ℕ → ℤ | vHitTime Aᶜ y = n} := hy
    rw [indicator_of_mem hyE, indicator_of_mem hyE, indicator_of_mem hyE]
    obtain ⟨hpre, hyn⟩ := hitTime_compl_facts hy
    rw [Absorption.firstExitSite_eq_some_iff.2 ⟨n, rfl, hyn, hpre⟩]
    by_cases hc : y n ∈ A'
    · rw [indicator_of_mem hc, indicator_of_notMem (fun h => h hc : y n ∉ A'ᶜ), Pi.one_apply, one_mul, add_zero]
      exact ite_eq_left hc
    · rw [indicator_of_notMem hc, indicator_of_mem (hc : y n ∈ A'ᶜ), zero_mul, zero_add]
      exact ite_eq_right hc
  · have hyE : y ∉ {y : ℕ → ℤ | vHitTime Aᶜ y = n} := hy
    rw [indicator_of_notMem hyE, indicator_of_notMem hyE, indicator_of_notMem hyE, add_zero]

theorem lintegral_eq_of_split {μ : Measure (ℕ → ℤ)} {L R f g c : (ℕ → ℤ) → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hL : ∀ y, L y = f y + c y) (hR : ∀ y, R y = g y + c y)
    (hfg : ∫⁻ y, f y ∂μ = ∫⁻ y, g y ∂μ) : ∫⁻ y, L y ∂μ = ∫⁻ y, R y ∂μ := by
  rw [lintegral_congr hL, lintegral_congr hR, lintegral_add_left hf, lintegral_add_left hg, hfg]

/-- **Strong Markov property at the exit time of `A`**, for first exit sites: for `A ⊆ A'` and `Ψ ≥ 0`,
`E^w[Ψ(o_{A'}(X))] = E^w[exitCont Ψ (o_A(X))]`. -/
theorem lintegral_firstExitSite_of_subset (m : ℤ → ℤ → ℕ) {A A' : Set ℤ} (hA : A ⊆ A') (Ψ : Option ℤ → ℝ≥0∞)
    (w : ℤ) :
    ∫⁻ y, Ψ (firstExitSite A' y) ∂srwLaw m w = ∫⁻ y, exitCont m A' Ψ (firstExitSite A y) ∂srwLaw m w := by
  have hF : Measurable fun y => Ψ (firstExitSite A' y) := measurable_firstExitSite_comp A' Ψ
  have hG : Measurable fun y => exitCont m A' Ψ (firstExitSite A y) := measurable_firstExitSite_comp A _
  rw [lintegral_eq_top_add_tsum _ Aᶜ hF, lintegral_eq_top_add_tsum _ Aᶜ hG]
  congr 1
  · refine lintegral_congr fun y => ?_
    by_cases hy : vHitTime Aᶜ y = ⊤
    · have hyE : y ∈ {y : ℕ → ℤ | vHitTime Aᶜ y = ⊤} := hy
      rw [indicator_of_mem hyE, indicator_of_mem hyE]
      have hall : ∀ n, y n ∈ A := by
        rw [vHitTime_compl, vExitTime_eq_top_iff] at hy
        exact hy
      rw [Absorption.firstExitSite_eq_none_iff.2 hall,
        Absorption.firstExitSite_eq_none_iff.2 fun n => hA (hall n)]
      rfl
    · have hyE : y ∉ {y : ℕ → ℤ | vHitTime Aᶜ y = ⊤} := hy
      rw [indicator_of_notMem hyE, indicator_of_notMem hyE]
  · refine tsum_congr fun n => ?_
    have m1 : Measurable ({y : ℕ → ℤ | vHitTime Aᶜ y = n}.indicator
        (fun y => A'.indicator 1 (y n) * Ψ (firstExitSite A' (pathShift n y)))) :=
      (((measurable_of_countable (A'.indicator (1 : ℤ → ℝ≥0∞))).comp (measurable_pi_apply n)).mul
        (hF.comp (measurable_pathShift n))).indicator (measurableSet_vHitTime_eq Aᶜ n)
    have m2 : Measurable ({y : ℕ → ℤ | vHitTime Aᶜ y = n}.indicator
        (fun y => A'.indicator 1 (y n) * ∫⁻ y', Ψ (firstExitSite A' y') ∂srwLaw m (y n))) :=
      ((measurable_of_countable (fun c => A'.indicator (1 : ℤ → ℝ≥0∞) c *
        ∫⁻ y', Ψ (firstExitSite A' y') ∂srwLaw m c)).comp (measurable_pi_apply n)).indicator
          (measurableSet_vHitTime_eq Aᶜ n)
    exact lintegral_eq_of_split m1 m2 (hitSplit_left hA Ψ n) (hitSplit_right m Ψ n)
      (lintegral_hitTime_eq m Aᶜ (A'.indicator 1) hF n w)

/-! ### The two-walker exchange -/

open Classical in
/-- The final weight `G'` of the aggregate after two walkers released from `A`, as a function of their first exit
sites `o`, `o'` from `A`. It is symmetric (`pairKernel_comm`). -/
noncomputable def pairKernel (m : ℤ → ℤ → ℕ) (G' : Set ℤ → ℝ≥0∞) (A : Set ℤ) : Option ℤ → Option ℤ → ℝ≥0∞
  | none, o' => G' (Absorption.nextAgg univ A o')
  | some b, none => G' (A ∪ {b})
  | some b, some c =>
    if c = b then ∫⁻ y, G' (Absorption.nextAgg univ (A ∪ {b}) (firstExitSite (A ∪ {b}) y)) ∂srwLaw m b
    else G' (A ∪ {b} ∪ {c})

theorem pairKernel_comm (m : ℤ → ℤ → ℕ) (G' : Set ℤ → ℝ≥0∞) (A : Set ℤ) (o o' : Option ℤ) :
    pairKernel m G' A o o' = pairKernel m G' A o' o := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some c => exact congrArg G' (nextAgg_univ_some A c)
  | some b =>
    cases o' with
    | none => exact congrArg G' (nextAgg_univ_some A b).symm
    | some c =>
      by_cases h : c = b
      · subst h
        rfl
      · rw [show pairKernel m G' A (some b) (some c) = G' (A ∪ {b} ∪ {c}) from ite_eq_right h,
          show pairKernel m G' A (some c) (some b) = G' (A ∪ {c} ∪ {b}) from ite_eq_right (Ne.symm h),
          union_right_comm]

/-- The second walker, from `w`, after the first one has left `A` at `o`. -/
theorem lintegral_pairKernel (m : ℤ → ℤ → ℕ) (G' : Set ℤ → ℝ≥0∞) (A : Set ℤ) (w : ℤ) (o : Option ℤ) :
    ∫⁻ y, G' (Absorption.nextAgg univ (Absorption.nextAgg univ A o)
        (firstExitSite (Absorption.nextAgg univ A o) y)) ∂srwLaw m w =
      ∫⁻ y, pairKernel m G' A o (firstExitSite A y) ∂srwLaw m w := by
  cases o with
  | none => rfl
  | some b =>
    rw [nextAgg_univ_some,
      lintegral_firstExitSite_of_subset m subset_union_left (fun o => G' (Absorption.nextAgg univ (A ∪ {b}) o)) w]
    refine lintegral_congr fun y => ?_
    cases hy : firstExitSite A y with
    | none => rfl
    | some c =>
      have hcA : c ∉ A := Absorption.not_mem_of_firstExitSite_eq_some hy
      by_cases hcb : c = b
      · subst hcb
        rw [show pairKernel m G' A (some c) (some c) =
            ∫⁻ y, G' (Absorption.nextAgg univ (A ∪ {c}) (firstExitSite (A ∪ {c}) y)) ∂srwLaw m c from ite_eq_left rfl]
        exact ite_eq_left (mem_union_right A (mem_singleton c))
      · have hc : c ∉ A ∪ {b} := fun h => h.elim hcA hcb
        rw [show pairKernel m G' A (some b) (some c) = G' (A ∪ {b} ∪ {c}) from ite_eq_right hcb,
          ← nextAgg_univ_some (A ∪ {b}) c]
        exact ite_eq_right hc

/-- **Two-walker exchange**: `F_G(A; z, w, L) = F_G(A; w, z, L)`. -/
theorem aggValue_swap (m : ℤ → ℤ → ℕ) (G : Set ℤ → ℝ≥0∞) (A : Set ℤ) (z w : ℤ) (L : List ℤ) :
    aggValue m G A (z :: w :: L) = aggValue m G A (w :: z :: L) := by
  have key : ∀ z w : ℤ, aggValue m G A (z :: w :: L) =
      ∫⁻ x, ∫⁻ y, pairKernel m (fun A' => aggValue m G A' L) A (firstExitSite A x) (firstExitSite A y)
        ∂srwLaw m w ∂srwLaw m z := by
    intro z w
    rw [aggValue_cons]
    refine lintegral_congr fun x => ?_
    rw [aggValue_cons]
    exact lintegral_pairKernel m (fun A' => aggValue m G A' L) A w (firstExitSite A x)
  rw [key z w, key w z,
    lintegral_lintegral_swap (f := fun x y => pairKernel m (fun A' => aggValue m G A' L) A (firstExitSite A x)
      (firstExitSite A y)) (measurable_firstExitSite_comp₂ A _).aemeasurable]
  exact lintegral_congr fun y => lintegral_congr fun x => pairKernel_comm m _ A _ _

/-- **Exchangeability of IDLA** (Diaconis-Fulton 1991, Section 4): `F_G(A; L)` depends on the starting sites `L` only
as a multiset. -/
theorem aggValue_perm (m : ℤ → ℤ → ℕ) (G : Set ℤ → ℝ≥0∞) {L₁ L₂ : List ℤ} (h : L₁.Perm L₂) :
    ∀ A : Set ℤ, aggValue m G A L₁ = aggValue m G A L₂ := by
  induction h with
  | nil => exact fun _ => rfl
  | cons z _ ih =>
    intro A
    rw [aggValue_cons, aggValue_cons]
    exact lintegral_congr fun x => ih _
  | swap z w L => exact fun A => aggValue_swap m G A w z L
  | trans _ _ ih₁ ih₂ => exact fun A => (ih₁ A).trans (ih₂ A)

end AbelianIDLA

end MatedCRT
