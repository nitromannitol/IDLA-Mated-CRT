import Mathlib

/-!
# FIRST PASS: the universal event over the radii (LEMMA68 D3)

Two parts.
(i) Deterministic: a property `Φ` of the radius that is constant on every closed interval free of a finite set `C`
of critical radii holds on `[α, β]` as soon as it holds at the rational radii of `[α, β]` and at the points of `C`
(the write-up: "a violation occurs either at a critical radius or on an interval containing a rational violation").
(ii) Measurable: for countably many configurations `i` and rational radii, the event that `Φ ω q i` holds at every
rational radius `q ∈ [α, β ω]` is measurable when `β` is measurable.
Not proved here, and taken as hypotheses: the constancy `hconst` between the critical radii (D5 and the killed-vertex
structure, which the write-up asserts from `V(K + B_r) = {v ∈ F : d_v < r}`), the critical radii being finitely many
and measurable, and the measurability `hΦ` of the quenched events at fixed rational radii (asserted in D3 as
"cylinder-event approximation"; no argument is written there).
-/

open MeasureTheory Set Metric

namespace MatedCRT

namespace Lemma68Universal

/-- (D3, deterministic core) A property constant on every closed interval free of the finite set `C` holds on
`[α, β]` as soon as it holds at the rational radii of `[α, β]` and at the critical radii in `C ∩ [α, β]`.
The hypothesis `α < β ∨ α ∈ C` excludes the degenerate interval `[α, α]` with `α` not critical. -/
theorem forall_Icc_of_rat_and_crit {Φ : ℝ → Prop} {C : Set ℝ} (hC : C.Finite) {α β : ℝ}
    (hαβ : α < β ∨ α ∈ C)
    (hconst : ∀ r s : ℝ, r ≤ s → (∀ c ∈ C, c ∉ Icc r s) → (Φ r ↔ Φ s))
    (hrat : ∀ q : ℚ, α ≤ (q : ℝ) → (q : ℝ) ≤ β → Φ (q : ℝ))
    (hcrit : ∀ c ∈ C, α ≤ c → c ≤ β → Φ c) :
    ∀ r : ℝ, α ≤ r → r ≤ β → Φ r := by
  intro r hαr hrβ
  by_cases hrC : r ∈ C
  · exact hcrit r hrC hαr hrβ
  have hopen : IsOpen Cᶜ := hC.isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen r hrC
  have hfree : ∀ x : ℝ, dist x r < ε → x ∉ C := fun x hx hxC => hball hx hxC
  rcases lt_or_eq_of_le hrβ with hlt | heq
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (show r < r + ε / 2 by linarith) hlt)
    have hqr : (q : ℝ) < r + ε / 2 := lt_of_lt_of_le hq2 (min_le_left _ _)
    have hqβ : (q : ℝ) ≤ β := (lt_of_lt_of_le hq2 (min_le_right _ _)).le
    have hfreeI : ∀ c ∈ C, c ∉ Icc r (q : ℝ) := by
      intro c hc hcI
      exact hfree c (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hcI.1, hcI.2]) hc
    exact (hconst r q hq1.le hfreeI).2 (hrat q (by linarith) hqβ)
  · have hαr' : α < r := by
      rcases hαβ with h | h
      · linarith
      · rcases lt_or_eq_of_le hαr with h' | h'
        · exact h'
        · rw [h'] at h
          exact absurd h hrC
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (show r - ε / 2 < r by linarith) hαr')
    have hqr : r - ε / 2 < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq1
    have hqα : α ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hq1)
    have hfreeI : ∀ c ∈ C, c ∉ Icc (q : ℝ) r := by
      intro c hc hcI
      exact hfree c (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hcI.1, hcI.2]) hc
    exact (hconst (q : ℝ) r hq2.le hfreeI).1 (hrat q hqα (by linarith))

/-- (D3, measurable core) For countably many configurations `i` and measurable upper bounds `β`, the event that
`Φ ω q i` holds at every rational radius `q ∈ [α, β ω]` and every `i` is measurable, when each event
`{ω | Φ ω q i}` is measurable (the quenched events at fixed rational radii, D3 p. 2: hypothesis). -/
theorem measurableSet_forall_rat {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {α : ℝ} {β : Ω → ℝ}
    (hβ : Measurable β) {Φ : Ω → ℝ → ι → Prop} (hΦ : ∀ (q : ℚ) (i : ι), MeasurableSet {ω | Φ ω (q : ℝ) i}) :
    MeasurableSet {ω | ∀ (q : ℚ) (i : ι), α ≤ (q : ℝ) → (q : ℝ) ≤ β ω → Φ ω (q : ℝ) i} := by
  have key : ∀ (q : ℚ) (i : ι), MeasurableSet {ω | α ≤ (q : ℝ) → (q : ℝ) ≤ β ω → Φ ω (q : ℝ) i} := by
    intro q i
    have hset : {ω | α ≤ (q : ℝ) → (q : ℝ) ≤ β ω → Φ ω (q : ℝ) i} =
        ({ω | α ≤ (q : ℝ)} ∩ {ω | (q : ℝ) ≤ β ω})ᶜ ∪ {ω | Φ ω (q : ℝ) i} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
      tauto
    rw [hset]
    exact ((MeasurableSet.const _).inter (measurableSet_le measurable_const hβ)).compl.union (hΦ q i)
  have hset2 : {ω | ∀ (q : ℚ) (i : ι), α ≤ (q : ℝ) → (q : ℝ) ≤ β ω → Φ ω (q : ℝ) i} =
      ⋂ (q : ℚ), ⋂ (i : ι), {ω | α ≤ (q : ℝ) → (q : ℝ) ≤ β ω → Φ ω (q : ℝ) i} := by
    ext ω
    exact ⟨fun h => Set.mem_iInter.2 fun q => Set.mem_iInter.2 fun i => h q i,
      fun h q i => Set.mem_iInter.1 (Set.mem_iInter.1 h q) i⟩
  rw [hset2]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun i => key q i

end Lemma68Universal

end MatedCRT
