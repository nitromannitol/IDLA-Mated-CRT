import Mathlib

/-!
# Unbounded stopping horizons almost surely (FIRST PASS, S4d, B2 part II, probabilistic)

Base horizon `T0` and rescaled horizons `Tn n` (weights `b n = n + 1`)
are related by the law equality of Lemma 2.5 (`ConeScaleInvarianceUpToFixedTimeStmt`), evaluated on the event
`{s < T}`, which is the coordinate `(s, 0)` of the family process (the origin lies in every positive-time slice).
Then `P(T_n ≤ s) = P(T0 ≤ s)` and `T0 > 0` a.s. give: almost surely `sup_n (n+1) T_n = ∞`.

Only measure theory enters: continuity from above of a decreasing sequence of null-measurable sets.
-/

open MeasureTheory Set Filter Topology

namespace MatedCRT

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Horizons are unbounded almost surely.** Let `Φ0`, `Φn n` be the joint laws (circle part and family process)
of the base and rescaled stopped families, with the law equality `P.map Φ0 = P.map (Φn n)`, the membership
`(Φ · ).2 (s, 0) ↔ s < T` almost surely for each `s > 0`, and `T0 > 0` almost surely. Then almost surely, for every
`M : ℕ`, some `n` has `M + 1 < (n + 1) * Tn n`. -/
theorem ae_horizon_unbounded {P : Measure Ω} [IsProbabilityMeasure P]
    {Φ0 : Ω → (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop)}
    {Φn : ℕ → Ω → (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop)}
    {T0 : Ω → ℝ} {Tn : ℕ → Ω → ℝ}
    (hT0 : ∀ᵐ ω ∂P, 0 < T0 ω)
    (hΦ0 : AEMeasurable Φ0 P) (hΦn : ∀ n, AEMeasurable (Φn n) P)
    (hlaw : ∀ n, P.map Φ0 = P.map (Φn n))
    (hF0 : ∀ s : ℝ, 0 < s → ∀ᵐ ω ∂P, (Φ0 ω).2 (s, 0) ↔ s < T0 ω)
    (hFn : ∀ n, ∀ s : ℝ, 0 < s → ∀ᵐ ω ∂P, (Φn n ω).2 (s, 0) ↔ s < Tn n ω) :
    ∀ᵐ ω ∂P, ∀ M : ℕ, ∃ n : ℕ, (M : ℝ) + 1 < ((n : ℝ) + 1) * Tn n ω := by
  -- the coordinate event `{q | q.2 (s, 0)}` is measurable in the product space
  have hS : ∀ s : ℝ, MeasurableSet {q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop) | q.2 (s, 0)} :=
    fun s => measurableSet_setOfPred.2 ((measurable_pi_apply (s, 0)).comp measurable_snd)
  have hnull : ∀ M : ℕ, P {ω | ∀ n : ℕ, ¬ ((M : ℝ) + 1 < ((n : ℝ) + 1) * Tn n ω)} = 0 := by
    intro M
    -- the thresholds `s n = (M + 1) / (n + 1)` decrease to `0`
    set s : ℕ → ℝ := fun n => ((M : ℝ) + 1) / ((n : ℝ) + 1) with hs_def
    have hspos : ∀ n, 0 < s n := fun n => div_pos (by positivity) (by positivity)
    have key : ∀ n (ω : Ω), s n < Tn n ω ↔ (M : ℝ) + 1 < ((n : ℝ) + 1) * Tn n ω := by
      intro n ω
      simp only [hs_def]
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1), mul_comm]
    -- the sets `A n = {T0 ≤ s n}` and `B n = {Tn n ≤ s n}`
    set A : ℕ → Set Ω := fun n => {ω | ¬ (s n < T0 ω)} with hA_def
    set B : ℕ → Set Ω := fun n => {ω | ¬ (s n < Tn n ω)} with hB_def
    have hAeq : ∀ n, A n =ᵐ[P] (Φ0) ⁻¹' ({q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop) |
        q.2 (s n, 0)}ᶜ) := by
      intro n
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hF0 (s n) (hspos n)] with ω hω
      exact not_congr hω.symm
    have hBeq : ∀ n, B n =ᵐ[P] (Φn n) ⁻¹' ({q : (Set.Ioi (0 : ℝ) × ℂ → ℝ) × (ℝ × ℂ → Prop) |
        q.2 (s n, 0)}ᶜ) := by
      intro n
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hFn n (s n) (hspos n)] with ω hω
      exact not_congr hω.symm
    have hBA : ∀ n, P (B n) = P (A n) := by
      intro n
      rw [measure_congr (hBeq n), measure_congr (hAeq n),
        ← Measure.map_apply_of_aemeasurable (hΦn n) (hS (s n)).compl,
        ← Measure.map_apply_of_aemeasurable hΦ0 (hS (s n)).compl, hlaw n]
    -- the event is contained in each `B n`
    have hsub : ∀ n, {ω | ∀ m : ℕ, ¬ ((M : ℝ) + 1 < ((m : ℝ) + 1) * Tn m ω)} ⊆ B n := by
      intro n ω hω hlt
      exact hω n ((key n ω).1 hlt)
    -- `A n` decreases, is null-measurable, and its intersection is null
    have hAanti : Antitone A := by
      intro n m hnm ω hω
      have hsm : s m ≤ s n := by
        simp only [hs_def]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
        linarith
      intro hlt
      exact hω (lt_of_le_of_lt hsm hlt)
    have hAmeas : ∀ n, NullMeasurableSet (A n) P := fun n =>
      (hΦ0.nullMeasurableSet_preimage (hS (s n)).compl).congr (hAeq n).symm
    have hlim : Tendsto (fun n => P (A n)) atTop (𝓝 (P (⋂ n, A n))) :=
      tendsto_measure_iInter_atTop hAmeas hAanti ⟨0, measure_ne_top P _⟩
    have hinter : P (⋂ n, A n) = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hT0)
      intro hpos
      have hω' : ω ∈ A ⌈((M : ℝ) + 1) / T0 ω⌉₊ := Set.mem_iInter.1 hω _
      have hn : ((M : ℝ) + 1) / T0 ω ≤ (⌈((M : ℝ) + 1) / T0 ω⌉₊ : ℝ) := Nat.le_ceil _
      have hlt : s ⌈((M : ℝ) + 1) / T0 ω⌉₊ < T0 ω := by
        simp only [hs_def]
        rw [div_lt_iff₀ (by positivity)]
        rw [div_le_iff₀ hpos] at hn
        nlinarith
      exact hω' hlt
    rw [hinter] at hlim
    have hle : ∀ n, P {ω | ∀ m : ℕ, ¬ ((M : ℝ) + 1 < ((m : ℝ) + 1) * Tn m ω)} ≤ P (A n) :=
      fun n => (measure_mono (hsub n)).trans (hBA n).le
    exact le_zero_iff.1 (ge_of_tendsto' hlim hle)
  have hae : ∀ᵐ ω ∂P, ∀ M : ℕ, ω ∉ {ω | ∀ n : ℕ, ¬ ((M : ℝ) + 1 < ((n : ℝ) + 1) * Tn n ω)} :=
    ae_all_iff.2 fun M => measure_eq_zero_iff_ae_notMem.1 (hnull M)
  filter_upwards [hae] with ω hω M
  have h := hω M
  simp only [not_forall, not_not] at h
  exact h

end MatedCRT
