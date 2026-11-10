import Mathlib
import MatedCRT.FirstPass.S6r.Amplification

/-!
# Almost-sure form of the 6.8 shell chain bound (`ShellChainAe`)

`shell_chain_bound` and `prefix_bad_bound_of_lt` (S4S6c/WalkBridge68) take the shell-order inclusions
`P_{k+1} ⊆ P_k ∩ F_k` pointwise. The nearest-neighbour walk gives these inclusions only almost surely,
so here the chain bound is proved with the inclusions holding `μ`-almost everywhere:
`oneTest_step_ae`, `shell_chain_bound_ae`, and the prefix bound `prefix_bad_bound_ae` on a general
filtration (prefix events and test events of notes (8.1), (8.3); one-test step of the strong Markov
property at the stopping times `T_k`, as in Armstrong-Kuusi-Mourrat).
-/

open MeasureTheory

namespace MatedCRT
namespace Lemma68ChainAe

open Lemma68Window

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `oneTest_step` with the inclusion `S ⊆ P ∩ F` required only `μ`-almost everywhere. -/
theorem oneTest_step_ae {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ mΩ) {P F S : Set Ω} (hP : MeasurableSet[𝓖] P) (hF : MeasurableSet[mΩ] F) {q : ℝ}
    (hone : ∀ᵐ ω ∂μ, ω ∈ P → μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω ≤ 1 - q)
    (hS : ∀ᵐ ω ∂μ, ω ∈ S → ω ∈ P ∩ F) :
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
  have h1 : μ.real S ≤ μ.real (P ∩ F) := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae (hS.mono fun ω hω => hω))
  linarith

omit mΩ in
/-- Pointwise form of the shell-order inclusion: if `T_{j+1} < τ_U` forces `T_j ≤ T_{j+1}` and
`L_j ≤ T_{j+1}` at a path `ω`, then `P_{j+1}(ω)` implies `P_j(ω)` and `F_j(ω)`. -/
theorem mem_prefix_succ_of_lt {E : Type*} {X : ℕ → Ω → E} {A : Set E} {Tj Tj1 Lj : Ω → ℕ∞}
    {τU : Ω → ℕ∞} {ω : Ω} (h1 : Tj1 ω < τU ω → Tj ω ≤ Tj1 ω) (h2 : Tj1 ω < τU ω → Lj ω ≤ Tj1 ω)
    (hω : ω ∈ prefixSet X A Tj1 τU) :
    ω ∈ prefixSet X A Tj τU ∧ ω ∈ testFailSet X A Tj Lj := by
  simp only [prefixSet, testFailSet, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨hlt, hpre⟩ := hω
  refine ⟨⟨lt_of_le_of_lt (h1 hlt) hlt, fun n hn => hpre n (lt_of_lt_of_le hn (h1 hlt))⟩,
    fun n _ hnL => hpre n (lt_of_lt_of_le hnL (h2 hlt))⟩

/-- `shell_chain_bound` with the inclusions `P_{k+1} ⊆ P_k ∩ F_k` and `B ⊆ P_n ∩ F_n` only
`μ`-almost everywhere. Same bound `(1 - q)^(n+1)`. -/
theorem shell_chain_bound_ae {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : ℕ → MeasurableSpace Ω}
    (h𝓖 : ∀ k, 𝓖 k ≤ mΩ) {P F : ℕ → Set Ω} {B : Set Ω} {q : ℝ} (hq1 : q ≤ 1)
    (n : ℕ) (hPm : ∀ k ≤ n, MeasurableSet[𝓖 k] (P k)) (hFm : ∀ k ≤ n, MeasurableSet (F k))
    (hone : ∀ k ≤ n, ∀ᵐ ω ∂μ, ω ∈ P k → μ[(F k).indicator (fun _ => (1 : ℝ)) | 𝓖 k] ω ≤ 1 - q)
    (hnest : ∀ k < n, ∀ᵐ ω ∂μ, ω ∈ P (k + 1) → ω ∈ P k ∧ ω ∈ F k)
    (hB : ∀ᵐ ω ∂μ, ω ∈ B → ω ∈ P n ∩ F n) :
    μ.real B ≤ (1 - q) ^ (n + 1) := by
  have key : ∀ k, k ≤ n → μ.real (P k) ≤ (1 - q) ^ k := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hs := oneTest_step_ae (h𝓖 k) (hPm k (by omega)) (hFm k (by omega)) (hone k (by omega))
        (hnest k (by omega))
      calc μ.real (P (k + 1)) ≤ (1 - q) * μ.real (P k) := hs
        _ ≤ (1 - q) * (1 - q) ^ k := mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
        _ = (1 - q) ^ (k + 1) := by ring
  have hs := oneTest_step_ae (h𝓖 n) (hPm n le_rfl) (hFm n le_rfl) (hone n le_rfl) hB
  calc μ.real B ≤ (1 - q) * μ.real (P n) := hs
    _ ≤ (1 - q) * (1 - q) ^ n := mul_le_mul_of_nonneg_left (key n le_rfl) (by linarith)
    _ = (1 - q) ^ (n + 1) := by ring

/-- `prefix_bad_bound_of_lt` with the four shell-order hypotheses `hTT`, `hLT`, `hcross`, `hend`
required only `μ`-almost surely (the nearest-neighbour walk gives them a.s.). The bound is the same
`μ(B) ≤ (1 - q)^(n+1)` for the no-escape event; `{τ_U = ⊤}` is the null set `hnull`. -/
theorem prefix_bad_bound_ae {E : Type*} [MeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) {X : ℕ → Ω → E} (hX : ∀ n, Measurable[𝓕 n] (X n)) {A : Set E}
    (hA : MeasurableSet A) {T L : ℕ → Ω → ℕ∞} {τU : Ω → ℕ∞}
    (hT : ∀ k, IsStoppingTime 𝓕 (T k)) (hL : ∀ k, IsStoppingTime 𝓕 (L k))
    (hτ : IsStoppingTime 𝓕 τU) {q : ℝ} (hq1 : q ≤ 1) (n : ℕ)
    (hone : ∀ k ≤ n, ∀ᵐ ω ∂μ, ω ∈ prefixSet X A (T k) τU →
      μ[(testFailSet X A (T k) (L k)).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] ω
        ≤ 1 - q)
    (hTT : ∀ j < n, ∀ᵐ ω ∂μ, T (j + 1) ω < τU ω → T j ω ≤ T (j + 1) ω)
    (hLT : ∀ j < n, ∀ᵐ ω ∂μ, T (j + 1) ω < τU ω → L j ω ≤ T (j + 1) ω)
    (hcross : ∀ᵐ ω ∂μ, ω ∈ noEscapeSet X A τU → τU ω ≠ ⊤ → T n ω < τU ω)
    (hend : ∀ᵐ ω ∂μ, ω ∈ noEscapeSet X A τU → τU ω ≠ ⊤ → L n ω ≤ τU ω)
    (hnull : μ {ω | τU ω = ⊤} = 0) :
    μ.real (noEscapeSet X A τU) ≤ (1 - q) ^ (n + 1) := by
  have hnest : ∀ k < n, ∀ᵐ ω ∂μ, ω ∈ prefixSet X A (T (k + 1)) τU →
      ω ∈ prefixSet X A (T k) τU ∧ ω ∈ testFailSet X A (T k) (L k) := by
    intro k hk
    filter_upwards [hTT k hk, hLT k hk] with ω h1 h2 hω
    exact mem_prefix_succ_of_lt h1 h2 hω
  have hB : ∀ᵐ ω ∂μ, ω ∈ noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤} →
      ω ∈ prefixSet X A (T n) τU ∩ testFailSet X A (T n) (L n) := by
    filter_upwards [hcross, hend] with ω hc he hω
    have hT' : T n ω < τU ω := hc hω.1 hω.2
    have hL' : L n ω ≤ τU ω := he hω.1 hω.2
    have hB' : ∀ m : ℕ, (m : ℕ∞) < τU ω → X m ω ∈ A := hω.1
    exact ⟨⟨hT', fun m hm => hB' m (lt_trans hm hT')⟩, fun m _ hmL => hB' m (lt_of_lt_of_le hmL hL')⟩
  have hchain : μ.real (noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤}) ≤ (1 - q) ^ (n + 1) :=
    shell_chain_bound_ae (P := fun k => prefixSet X A (T k) τU)
      (F := fun k => testFailSet X A (T k) (L k))
      (B := noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤})
      (𝓖 := fun k => (hT k).measurableSpace) (fun k => (hT k).measurableSpace_le) hq1 n
      (fun k _ => measurableSet_prefixSet 𝓕 hX hA (hT k) hτ)
      (fun k _ => measurableSet_testFailSet 𝓕 hX hA (hT k) (hL k)) hone hnest hB
  have hcov : noEscapeSet X A τU ⊆ (noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤}) ∪ {ω | τU ω = ⊤} := by
    intro ω hω
    by_cases h : τU ω = ⊤
    · exact Or.inr h
    · exact Or.inl ⟨hω, h⟩
  have hnull' : μ.real {ω | τU ω = ⊤} = 0 := by
    rw [measureReal_def, hnull, ENNReal.toReal_zero]
  calc μ.real (noEscapeSet X A τU)
      ≤ μ.real ((noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤}) ∪ {ω | τU ω = ⊤}) := measureReal_mono hcov
    _ ≤ μ.real (noEscapeSet X A τU ∩ {ω | τU ω ≠ ⊤}) + μ.real {ω | τU ω = ⊤} :=
        measureReal_union_le _ _
    _ ≤ (1 - q) ^ (n + 1) := by rw [hnull', add_zero]; exact hchain

end Lemma68ChainAe
end MatedCRT
