import Mathlib
import MatedCRT.FirstPass.S6r.Constants

/-!
# 6.8 redesign, S8': strong-Markov shell amplification (steps 10-14)


Index convention: the notes' shells and tests `j = 1, ..., N` are the Lean indices
`k = 0, ..., n` with `N = n + 1`; `shell_chain_bound` has `n + 1` tests.

Named inputs (hypotheses of the statements that use them, not proved here):
* `hone`: the one-test estimate (7.50) with the strong Markov property at `T_k`, i.e.
  `P(F_k | F_{T_k}) <= 1 - q` on `P_k` (notes (8.4));
* `hTT`, `hLT`: shell spacing `T_k <= T_{k+1}` and `L_k <= T_{k+1}` (steps 4-9);
* `hcross`, `hend`: on the bad event the path crosses shell `n` before `tau_U` and
  the last test ends before `tau_U` (notes (8.2), (8.8)).
No independence is used: only the strong-Markov conditional bound at the stopping times `T_k`.
-/

open MeasureTheory

namespace MatedCRT
namespace Lemma68Window

variable {Ω : Type*}

/-- Notes (8.1): the prefix event `P_j = {T_j < τ_U, X_n ∈ A for all n < T_j}`. -/
def prefixSet {E : Type*} (X : ℕ → Ω → E) (A : Set E) (T τU : Ω → ℕ∞) : Set Ω :=
  {ω | T ω < τU ω ∧ ∀ n : ℕ, (n : ℕ∞) < T ω → X n ω ∈ A}

/-- Notes (8.3): the test-failure event `F_j = {X_n ∈ A for all T_j ≤ n < L_j}`. -/
def testFailSet {E : Type*} (X : ℕ → Ω → E) (A : Set E) (T L : Ω → ℕ∞) : Set Ω :=
  {ω | ∀ n : ℕ, T ω ≤ (n : ℕ∞) → (n : ℕ∞) < L ω → X n ω ∈ A}

/-- The bad event `B = {X_n ∈ A for all n < τ_U}` of the 6.8 probability bound. -/
def noEscapeSet {E : Type*} (X : ℕ → Ω → E) (A : Set E) (τU : Ω → ℕ∞) : Set Ω :=
  {ω | ∀ n : ℕ, (n : ℕ∞) < τU ω → X n ω ∈ A}

variable [mΩ : MeasurableSpace Ω]

/-! ### Step 10: `P_j` is `𝓕_{T_j}`-measurable -/

/-- Step 10 (notes (8.1)): `P_j` is measurable for the stopped sigma-algebra `𝓕_{T_j}`. -/
theorem measurableSet_prefixSet {E : Type*} [MeasurableSpace E] (𝓕 : Filtration ℕ mΩ)
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable[𝓕 n] (X n)) {A : Set E} (hA : MeasurableSet A)
    {T τU : Ω → ℕ∞} (hT : IsStoppingTime 𝓕 T) (hτ : IsStoppingTime 𝓕 τU) :
    MeasurableSet[hT.measurableSpace] (prefixSet X A T τU) := by
  have hpart : ∀ i : ℕ, MeasurableSet[𝓕 i] (prefixSet X A T τU ∩ {ω | T ω ≤ (i : ℕ∞)}) := by
    intro i
    have hset : prefixSet X A T τU ∩ {ω | T ω ≤ (i : ℕ∞)} =
        (⋃ m ∈ Finset.range (i + 1), ({ω | T ω = (m : ℕ∞)} ∩ {ω | (m : ℕ∞) < τU ω})) ∩
          ⋂ n ∈ Finset.range (i + 1), {ω | (n : ℕ∞) < T ω → X n ω ∈ A} := by
      ext ω
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top i) h3)
        have hmi : m < i + 1 := by
          have h4 : (m : ℕ∞) ≤ (i : ℕ∞) := by rw [hm]; exact h3
          exact Nat.lt_succ_of_le (by exact_mod_cast h4)
        refine ⟨Set.mem_iUnion₂.mpr ⟨m, Finset.mem_range.mpr hmi, ⟨hm.symm, ?_⟩⟩, ?_⟩
        · rw [hm]; exact h1
        · exact Set.mem_iInter₂.mpr fun n _ => h2 n
      · rintro ⟨hU, hI⟩
        obtain ⟨m, hmr, hmS⟩ := Set.mem_iUnion₂.mp hU
        have e1 : T ω = (m : ℕ∞) := hmS.1
        have hmi : m < i + 1 := Finset.mem_range.mp hmr
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [e1]; exact hmS.2
        · intro n hn
          have hnm : n < m := by
            have h5 := hn
            rw [e1] at h5
            exact_mod_cast h5
          have hnr : n ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
          exact Set.mem_iInter₂.mp hI n hnr hn
        · show T ω ≤ (i : ℕ∞)
          rw [e1]; exact_mod_cast (Nat.lt_succ_iff.mp hmi)
    rw [hset]
    refine MeasurableSet.inter ?_ ?_
    · refine Finset.measurableSet_biUnion _ fun m hm => ?_
      have hmi : m ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      exact (𝓕.mono hmi _ (hT.measurableSet_eq_of_countable m)).inter
        (𝓕.mono hmi _ (hτ.measurableSet_gt m))
    · refine Finset.measurableSet_biInter _ fun n hn => ?_
      have hni : n ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have e : {ω | (n : ℕ∞) < T ω → X n ω ∈ A} =
          {ω | (n : ℕ∞) < T ω}ᶜ ∪ X n ⁻¹' A := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_preimage,
          imp_iff_not_or]
      rw [e]
      exact (𝓕.mono hni _ (hT.measurableSet_gt n)).compl.union (𝓕.mono hni _ (hX n hA))
  have hsup : MeasurableSet[⨆ t, 𝓕 t] (prefixSet X A T τU) := by
    have hunion : prefixSet X A T τU = ⋃ i : ℕ, prefixSet X A T τU ∩ {ω | T ω ≤ (i : ℕ∞)} := by
      ext ω
      constructor
      · intro h
        have hh := h
        obtain ⟨h1, _⟩ := hh
        have hne : T ω ≠ ⊤ := (lt_of_lt_of_le h1 le_top).ne
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
        exact Set.mem_iUnion.mpr ⟨m, ⟨h, hm.symm.le⟩⟩
      · intro h
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
        exact hi.1
    rw [hunion]
    exact MeasurableSet.iUnion fun i => (le_iSup (fun t => 𝓕 t) i) _ (hpart i)
  exact (hT.measurableSet _).mpr ⟨hsup, hpart⟩

/-- The test-failure event `F_j` is measurable (for the stopping times `T_j`, `L_j`). -/
theorem measurableSet_testFailSet {E : Type*} [MeasurableSpace E] (𝓕 : Filtration ℕ mΩ)
    {X : ℕ → Ω → E} (hX : ∀ n, Measurable[𝓕 n] (X n)) {A : Set E} (hA : MeasurableSet A)
    {T L : Ω → ℕ∞} (hT : IsStoppingTime 𝓕 T) (hL : IsStoppingTime 𝓕 L) :
    MeasurableSet (testFailSet X A T L) := by
  have e : testFailSet X A T L = ⋂ n : ℕ,
      ((({ω | T ω ≤ (n : ℕ∞)}) ∩ {ω | (n : ℕ∞) < L ω})ᶜ ∪ X n ⁻¹' A) := by
    ext ω
    simp only [testFailSet, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff,
      Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h n
      by_cases hc : T ω ≤ (n : ℕ∞) ∧ (n : ℕ∞) < L ω
      · exact Or.inr (h n hc.1 hc.2)
      · exact Or.inl hc
    · intro h n h1 h2
      rcases h n with h' | h'
      · exact absurd ⟨h1, h2⟩ h'
      · exact h'
  rw [e]
  refine MeasurableSet.iInter fun n => 𝓕.le n _ ?_
  exact (((hT.measurableSet_le n).inter (hL.measurableSet_gt n)).compl).union (hX n hA)

/-! ### Step 11: nesting `P_{j+1} ⊆ P_j ∩ F_j` (notes (8.5)) -/

omit mΩ in
/-- Step 11 (notes (8.5)): on `P_{j+1}`, the prefix `P_j` holds and the `j`-th test fails. -/
theorem prefixSet_succ_subset {E : Type*} {X : ℕ → Ω → E} {A : Set E} {Tj Tj1 Lj : Ω → ℕ∞}
    {τU : Ω → ℕ∞} (h1 : ∀ ω, Tj ω ≤ Tj1 ω) (h2 : ∀ ω, Lj ω ≤ Tj1 ω) :
    prefixSet X A Tj1 τU ⊆ prefixSet X A Tj τU ∩ testFailSet X A Tj Lj := by
  intro ω hω
  simp only [prefixSet, testFailSet, Set.mem_inter_iff, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨hlt, hpre⟩ := hω
  refine ⟨⟨lt_of_le_of_lt (h1 ω) hlt, fun n hn => hpre n (lt_of_lt_of_le hn (h1 ω))⟩,
    fun n _ hnL => hpre n (lt_of_lt_of_le hnL (h2 ω))⟩

/-! ### Step 12: the bad event sits in the last shell and the last test (notes (8.8)-(8.9)) -/

omit mΩ in
/-- Notes (8.2) and (8.8): `B ⊆ P_n ∩ F_n`. -/
theorem noEscapeSet_subset {E : Type*} {X : ℕ → Ω → E} {A : Set E} {T L : ℕ → Ω → ℕ∞}
    {τU : Ω → ℕ∞} (n : ℕ) (hcross : ∀ ω ∈ noEscapeSet X A τU, T n ω < τU ω)
    (hend : ∀ ω ∈ noEscapeSet X A τU, L n ω ≤ τU ω) :
    noEscapeSet X A τU ⊆ prefixSet X A (T n) τU ∩ testFailSet X A (T n) (L n) := by
  intro ω hω
  have hB : ∀ m : ℕ, (m : ℕ∞) < τU ω → X m ω ∈ A := hω
  have hT' : T n ω < τU ω := hcross ω hω
  simp only [prefixSet, testFailSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨⟨hT', fun m hm => hB m (lt_trans hm hT')⟩,
    fun m _ hmL => hB m (lt_of_lt_of_le hmL (hend ω hω))⟩

/-- One strong-Markov step (notes (8.4), (8.6)): if `P` is `𝓖`-measurable and the conditional
failure probability of `F` given `𝓖` is at most `1 - q` on `P`, then every `S ⊆ P ∩ F` has
`μ(S) ≤ (1 - q) μ(P)`. No independence is used. -/
theorem oneTest_step {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ mΩ) {P F S : Set Ω} (hP : MeasurableSet[𝓖] P) (hF : MeasurableSet[mΩ] F) {q : ℝ}
    (hone : ∀ᵐ ω ∂μ, ω ∈ P → μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω ≤ 1 - q)
    (hS : S ⊆ P ∩ F) :
    μ.real S ≤ (1 - q) * μ.real P := by
  have hPm : MeasurableSet[mΩ] P := h𝓖 _ hP
  have hind : Integrable (F.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hF
  have e : ∫ x in P, F.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real (P ∩ F) := by
    rw [← integral_indicator hPm, Set.indicator_indicator,
      integral_indicator_const _ (hPm.inter hF), smul_eq_mul, mul_one]
  have h2 : ∫ x in P, F.indicator (fun _ => (1 : ℝ)) x ∂μ =
      ∫ x in P, μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] x ∂μ :=
    (setIntegral_condExp h𝓖 hind hP).symm
  have h3 : ∫ x in P, μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] x ∂μ ≤ ∫ x in P, (1 - q) ∂μ := by
    refine setIntegral_mono_ae_restrict integrable_condExp.integrableOn
      (integrable_const _).integrableOn ?_
    filter_upwards [ae_restrict_mem hPm, ae_restrict_of_ae hone] with ω hωP hωone
    exact hωone hωP
  have h4 : ∫ x in P, (1 - q) ∂μ = (1 - q) * μ.real P := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  have h1 : μ.real S ≤ μ.real (P ∩ F) := measureReal_mono hS
  linarith

/-- Steps 11-12 (notes (8.5)-(8.9)): for the chain of prefix events `P_k` with tests `F_k`,
`k = 0, ..., n` (so `n + 1` tests), `P(B) ≤ (1 - q)^(n+1)`. -/
theorem shell_chain_bound {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : ℕ → MeasurableSpace Ω}
    (h𝓖 : ∀ k, 𝓖 k ≤ mΩ) {P F : ℕ → Set Ω} {B : Set Ω} {q : ℝ} (hq1 : q ≤ 1)
    (n : ℕ) (hPm : ∀ k ≤ n, MeasurableSet[𝓖 k] (P k)) (hFm : ∀ k ≤ n, MeasurableSet (F k))
    (hone : ∀ k ≤ n, ∀ᵐ ω ∂μ, ω ∈ P k → μ[(F k).indicator (fun _ => (1 : ℝ)) | 𝓖 k] ω ≤ 1 - q)
    (hnest : ∀ k < n, P (k + 1) ⊆ P k ∩ F k) (hB : B ⊆ P n ∩ F n) :
    μ.real B ≤ (1 - q) ^ (n + 1) := by
  have key : ∀ k, k ≤ n → μ.real (P k) ≤ (1 - q) ^ k := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hs := oneTest_step (h𝓖 k) (hPm k (by omega)) (hFm k (by omega)) (hone k (by omega))
        (hnest k (by omega))
      calc μ.real (P (k + 1)) ≤ (1 - q) * μ.real (P k) := hs
        _ ≤ (1 - q) * (1 - q) ^ k := mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
        _ = (1 - q) ^ (k + 1) := by ring
  have hs := oneTest_step (h𝓖 n) (hPm n le_rfl) (hFm n le_rfl) (hone n le_rfl) hB
  calc μ.real B ≤ (1 - q) * μ.real (P n) := hs
    _ ≤ (1 - q) * (1 - q) ^ n := mul_le_mul_of_nonneg_left (key n le_rfl) (by linarith)
    _ = (1 - q) ^ (n + 1) := by ring

/-- Steps 10-12 for the concrete events of 6.8: `P(B) ≤ (1 - q)^(n+1)`, with the strong-Markov
one-test bound `hone` at the stopping times `T_k` and the shell geometry as named hypotheses. -/
theorem prefix_bad_bound {E : Type*} [MeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) {X : ℕ → Ω → E} (hX : ∀ n, Measurable[𝓕 n] (X n)) {A : Set E}
    (hA : MeasurableSet A) {T L : ℕ → Ω → ℕ∞} {τU : Ω → ℕ∞}
    (hT : ∀ k, IsStoppingTime 𝓕 (T k)) (hL : ∀ k, IsStoppingTime 𝓕 (L k))
    (hτ : IsStoppingTime 𝓕 τU) {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ ω ∂μ, ω ∈ prefixSet X A (T k) τU →
      μ[(testFailSet X A (T k) (L k)).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] ω
        ≤ 1 - q)
    (hTT : ∀ j < n, ∀ ω, T j ω ≤ T (j + 1) ω) (hLT : ∀ j < n, ∀ ω, L j ω ≤ T (j + 1) ω)
    (hcross : ∀ ω ∈ noEscapeSet X A τU, T n ω < τU ω)
    (hend : ∀ ω ∈ noEscapeSet X A τU, L n ω ≤ τU ω) :
    μ.real (noEscapeSet X A τU) ≤ (1 - q) ^ (n + 1) :=
  shell_chain_bound (P := fun k => prefixSet X A (T k) τU)
    (F := fun k => testFailSet X A (T k) (L k)) (B := noEscapeSet X A τU)
    (𝓖 := fun k => (hT k).measurableSpace) (fun k => (hT k).measurableSpace_le) hq1 n
    (fun k _ => measurableSet_prefixSet 𝓕 hX hA (hT k) hτ)
    (fun k _ => measurableSet_testFailSet 𝓕 hX hA (hT k) (hL k)) hone
    (fun k hk => prefixSet_succ_subset (hTT k hk) (hLT k hk))
    (noEscapeSet_subset n hcross hend)

/-! ### Step 12 (continued): the exponential form (notes (8.10)-(8.11)) -/

theorem one_sub_pow_le_exp {q : ℝ} (hq1 : q ≤ 1) (N : ℕ) :
    (1 - q) ^ N ≤ Real.exp (-(q * N)) := by
  have h1 : 1 - q ≤ Real.exp (-q) := by linarith [Real.add_one_le_exp (-q)]
  have h0 : 0 ≤ 1 - q := by linarith
  calc (1 - q) ^ N ≤ (Real.exp (-q)) ^ N := pow_le_pow_left₀ h0 h1 N
    _ = Real.exp (-(q * N)) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Notes (7.10), (7.51), (8.10)-(8.11): with `N ≥ c_N r^{-ζ}` tests and `q ≥ q_0 (1 + log(1/r))^{-2}`,
`exp(-q N) ≤ exp(-c_N q_0 r^{-ζ} / (1 + log(1/r))^2)`. -/
theorem exp_le_of_counts {cN q0 r ζ q : ℝ} {N : ℕ} (hcN : 0 ≤ cN) (hq0 : 0 ≤ q0) (hr : 0 < r)
    (hr1 : r ≤ 1) (hN : cN * r ^ (-ζ) ≤ (N : ℝ)) (hq : q0 / (1 + Real.log (1 / r)) ^ 2 ≤ q) :
    Real.exp (-(q * N)) ≤ Real.exp (-(cN * q0 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) := by
  have hL : 0 ≤ Real.log (1 / r) := Real.log_nonneg (one_le_one_div hr hr1)
  have hD : 0 < (1 + Real.log (1 / r)) ^ 2 := pow_pos (by linarith) 2
  have hA : 0 ≤ q0 / (1 + Real.log (1 / r)) ^ 2 := div_nonneg hq0 hD.le
  have hB0 : 0 ≤ cN * r ^ (-ζ) := mul_nonneg hcN (Real.rpow_nonneg hr.le _)
  have hNq : 0 ≤ (N : ℝ) := hB0.trans hN
  have key : cN * q0 * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2 =
      (cN * r ^ (-ζ)) * (q0 / (1 + Real.log (1 / r)) ^ 2) := by ring
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  rw [key]
  calc (cN * r ^ (-ζ)) * (q0 / (1 + Real.log (1 / r)) ^ 2) ≤ (N : ℝ) * q :=
        mul_le_mul hN hq hA hNq
    _ = q * N := mul_comm _ _

/-! ### Step 13: the constant-order conclusion (notes (8.12)) -/

/-- Step 13 (notes (8.12)): for `c, ζ > 0` there is `r_amp ∈ (0, 1]`, depending only on `c, ζ`,
such that `r ≤ r_amp` gives `exp(-c r^{-ζ} / (1 + log(1/r))^2) ≤ 1/2`. -/
theorem constant_order_conclusion {c ζ : ℝ} (hc : 0 < c) (hζ : 0 < ζ) :
    ∃ r_amp : ℝ, 0 < r_amp ∧ r_amp ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r_amp →
      Real.exp (-(c * r ^ (-ζ) / (1 + Real.log (1 / r)) ^ 2)) ≤ 1 / 2 := by
  have hK : 0 < c * ζ ^ 3 := by positivity
  set u0 : ℝ := max 1 (24 / (c * ζ ^ 3)) with hu0
  have hu1 : 1 ≤ u0 := le_max_left _ _
  have hu2 : 24 / (c * ζ ^ 3) ≤ u0 := le_max_right _ _
  refine ⟨Real.exp (-u0), Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith),
    fun r hr hrle => ?_⟩
  have hlogr : Real.log r ≤ -u0 := by
    have h := Real.log_le_log hr hrle
    rwa [Real.log_exp] at h
  have hLneg : Real.log (1 / r) = -Real.log r := by rw [one_div, Real.log_inv]
  have hLu : u0 ≤ Real.log (1 / r) := by rw [hLneg]; linarith
  have hrpow : r ^ (-ζ) = Real.exp (ζ * Real.log (1 / r)) := by
    rw [Real.rpow_def_of_pos hr, hLneg]; congr 1; ring
  rw [hrpow]
  set L : ℝ := Real.log (1 / r) with hL
  have hKL : 24 ≤ c * ζ ^ 3 * L := by
    have h := hu2.trans hLu
    rw [div_le_iff₀ hK] at h
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hx : 0 ≤ ζ * L := mul_nonneg hζ.le (by linarith)
  have hE : (ζ * L) ^ 3 / 6 ≤ Real.exp (ζ * L) := by
    have h := Real.pow_div_factorial_le_exp (ζ * L) hx 3
    simpa [Nat.factorial] using h
  have h3 : c * ((ζ * L) ^ 3 / 6) ≤ c * Real.exp (ζ * L) := mul_le_mul_of_nonneg_left hE hc.le
  have h4 : (1 + L) ^ 2 ≤ c * Real.exp (ζ * L) := by
    have e : c * ((ζ * L) ^ 3 / 6) = c * ζ ^ 3 * L ^ 3 / 6 := by ring
    have h5 : (1 + L) ^ 2 ≤ 4 * L ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ L - 1) (by linarith : (0 : ℝ) ≤ L)]
    have h6 : 4 * L ^ 2 ≤ c * ζ ^ 3 * L ^ 3 / 6 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hKL) (sq_nonneg L)]
    linarith
  have hX : 1 ≤ c * Real.exp (ζ * L) / (1 + L) ^ 2 := by
    rw [le_div_iff₀ (pow_pos (by linarith) 2)]
    linarith
  have hexp1 : Real.exp (-(c * Real.exp (ζ * L) / (1 + L) ^ 2)) ≤ Real.exp (-1) :=
    Real.exp_le_exp.mpr (by linarith)
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hexp2 : Real.exp (-1) ≤ 1 / 2 := by
    calc Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
      _ ≤ 2⁻¹ := inv_anti₀ (by norm_num) he
      _ = 1 / 2 := by norm_num
  exact hexp1.trans hexp2

/-! ### Step 14: constants, and the assembled bound -/

/-- Notes step 14: `s2 = 1/2`. -/
theorem s2_eq_half : Constants68.s2 = 1 / 2 := rfl

/-- Steps 13-14: the shell product bound. The threshold `r_amp` depends only on the constants
`cN, q0` and on `ζ = K.ζ` (not on `s_0`); the bound is `s2 = 1/2`. -/
theorem shell_product_le_half {γ ρ : ℝ} (K : Constants68 γ ρ) {cN q0 : ℝ} (hcN : 0 < cN)
    (hq0 : 0 < q0) :
    ∃ r_amp : ℝ, 0 < r_amp ∧ r_amp ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r_amp → ∀ (n : ℕ) (q μB : ℝ),
      0 ≤ q → q ≤ 1 → cN * r ^ (-K.ζ) ≤ ((n + 1 : ℕ) : ℝ) →
      q0 / (1 + Real.log (1 / r)) ^ 2 ≤ q → μB ≤ (1 - q) ^ (n + 1) → μB ≤ Constants68.s2 := by
  obtain ⟨r_amp, hr, hr1, hbd⟩ :=
    constant_order_conclusion (c := cN * q0) (ζ := K.ζ) (mul_pos hcN hq0) K.hζ0
  refine ⟨r_amp, hr, hr1, fun r hr0 hrle n q μB hq0' hq1' hN hq hμB => ?_⟩
  have hr1' : r ≤ 1 := hrle.trans hr1
  calc μB ≤ (1 - q) ^ (n + 1) := hμB
    _ ≤ Real.exp (-(q * ((n + 1 : ℕ) : ℝ))) := one_sub_pow_le_exp hq1' (n + 1)
    _ ≤ Real.exp (-(cN * q0 * r ^ (-K.ζ) / (1 + Real.log (1 / r)) ^ 2)) :=
        exp_le_of_counts hcN.le hq0.le hr0 hr1' hN hq
    _ ≤ 1 / 2 := hbd r hr0 hrle
    _ = Constants68.s2 := s2_eq_half.symm

end Lemma68Window
end MatedCRT
