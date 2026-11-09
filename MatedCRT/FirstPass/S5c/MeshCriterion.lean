import MatedCRT.Defs.Notation
import MatedCRT.FirstPass.S5c.SeqCriterion

/-!
# FIRST PASS, Lemma 5.3: continuous-mesh criterion for `TendsToOneOn` (CHATGPT-5-3-remaining §6.2)

Along every sequence `e n → 0⁺` a subsequence `φ` gives, almost surely on `F`, eventual membership of
`E (e (φ k))`; and the good events `E ε` are null measurable for all small `ε`. Then `P[F ∩ (E ε)ᶜ] → 0`
as `ε ↓ 0`, i.e. `TendsToOneOn P F E` (Defs/Notation.lean:40). `F` need not be measurable (outer measure).
Proof: `Filter.tendsto_of_subseq_tendsto` on `𝓝[>] 0`; for each input sequence discard the finitely many initial
indices where null measurability may fail, then apply the sequence form `tendsto_measure_inter_compl_of_ae_eventually`.
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Topology Set

/-- **Continuous-mesh criterion for `TendsToOneOn`** (CHATGPT-5-3-remaining §6.2): see the module docstring. -/
theorem tendsToOneOn_of_subsequence_ae_eventually {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Set Ω} {E : ℝ → Set Ω}
    (hnull : ∀ᶠ ε in 𝓝[>] (0 : ℝ), NullMeasurableSet (E ε) P)
    (hsub : ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝[>] (0 : ℝ)) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ ω ∂P, ω ∈ F → ∀ᶠ k in atTop, ω ∈ E (e (φ k))) :
    TendsToOneOn P F E := by
  unfold TendsToOneOn
  refine Filter.tendsto_of_subseq_tendsto fun e he => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (he.eventually hnull)
  obtain ⟨φ, hφ, hae⟩ := hsub e he
  have hE : ∀ n : ℕ, NullMeasurableSet (E (e (φ (n + N)))) P := fun n => by
    have hid : n + N ≤ φ (n + N) := hφ.id_le (n + N)
    exact hN (φ (n + N)) (by omega)
  have hAE : ∀ᵐ ω ∂P, ω ∈ F → ∀ᶠ n in atTop, ω ∈ E (e (φ (n + N))) := by
    filter_upwards [hae] with ω hω hF
    obtain ⟨a, ha⟩ := eventually_atTop.1 (hω hF)
    exact eventually_atTop.2 ⟨a, fun n hn => ha (n + N) (by omega)⟩
  exact ⟨fun n => φ (n + N),
    tendsto_measure_inter_compl_of_ae_eventually (E := fun n : ℕ => E (e (φ (n + N)))) hE hAE⟩

end MatedCRT.S5c
