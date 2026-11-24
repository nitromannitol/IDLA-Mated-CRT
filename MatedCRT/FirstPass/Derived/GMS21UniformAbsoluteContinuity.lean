import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import LatticeProb.Prob.FiniteACContiguity

/-!
# Uniform absolute continuity in the limit (GMS21, Definition 3.2)

Gwynne–Miller–Sheffield, *The Tutte embedding of the mated-CRT map converges to Liouville quantum
gravity* (arXiv 1705.11161), Section 3.2. For sequences `P₁ n`, `P₂ n` of probability measures on
common measurable spaces `(Ω n, M n)`, Definition 3.2 calls `{P₁ n}` *uniformly absolutely
continuous as `n → ∞` with respect to `{P₂ n}`* if for each `p ∈ (0, 1)` there are
`q = q(p) ∈ (0, 1)` and `n* = n*(p)` such that `P₁ n E ≤ q` for each `n ≥ n*` and each measurable
event `E ⊆ Ω n` with `P₂ n E ≤ p`; the sequences are *uniformly mutually absolutely continuous as
`n → ∞`* if each is uniformly absolutely continuous with respect to the other. Lemma 3.3 asserts
this for the laws of the cell configurations near an open set `U` of two locally absolutely
continuous `γ`-LQG measures, and the proof of Theorem 3.4 (case 1) uses it, together with
Lemma 3.5, to pass statements holding "with probability tending to `1`" from the `0`-quantum cone
to the `γ`-quantum cone.

## Main results

* `UniformlyAbsolutelyContinuous.tendsto_measure_zero`: if `{Q n}` is uniformly absolutely
  continuous with respect to `{P n}` and `Q n (E n) → 0`, then `P n (E n) → 0`. (Applied to the
  complements `(E n)ᶜ`, the definition says that an event of `P n`-probability at least `1 - p` has
  `Q n`-probability at least `1 - q > 0`.) The events need not be measurable.
* `UniformlyMutuallyAbsolutelyContinuous.tendsto_measure_zero_iff`: under uniform mutual absolute
  continuity, `P n (E n) → 0` if and only if `Q n (E n) → 0`.
* `UniformlyAbsolutelyContinuous.tendsto_measure_preimage_zero` and
  `UniformlyMutuallyAbsolutelyContinuous.tendsto_measure_preimage_zero_iff`: the same for events
  `{X n ∈ A n}` defined through random configurations `X₁ n`, `X₂ n` on two probability spaces
  whose laws are uniformly (mutually) absolutely continuous. This is the form in which Lemma 3.3
  enters the proof of Theorem 3.4: the bad events of the invariance principle are events of the
  cell configuration near `U`.
* `uniformlyMutuallyAbsolutelyContinuous_const`: two mutually absolutely continuous probability
  measures, viewed as constant sequences, are uniformly mutually absolutely continuous.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRT

open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- A positive extended real bounds from above a number in `(0, 1)`. -/
private theorem exists_pos_lt_one_le_of_pos {c : ℝ≥0∞} (hc : 0 < c) :
    ∃ c' : ℝ≥0∞, 0 < c' ∧ c' < 1 ∧ c' ≤ c := by
  obtain ⟨c', hc'0, hc'⟩ := exists_between (lt_min hc zero_lt_one)
  exact ⟨c', hc'0, hc'.trans_le (min_le_right _ _), (hc'.trans_le (min_le_left _ _)).le⟩

/-- The probability of a measurable event is one minus the probability of its complement. -/
private theorem prob_eq_one_sub_prob_compl {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet s) : μ s = 1 - μ sᶜ := by
  rw [← prob_compl_eq_one_sub hs.compl, compl_compl]

section Sequences

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Uniform absolute continuity in the limit** (GMS21, Definition 3.2). `{P n}` is uniformly
absolutely continuous as `n → ∞` with respect to `{Q n}`: for each `p ∈ (0, 1)` there are
`q ∈ (0, 1)` and `n*` such that `P n E ≤ q` for every `n ≥ n*` and every measurable event
`E ⊆ Ω n` with `Q n E ≤ p`. -/
def UniformlyAbsolutelyContinuous (P Q : ∀ n, Measure (Ω n)) : Prop :=
  ∀ p : ℝ≥0∞, 0 < p → p < 1 → ∃ q : ℝ≥0∞, 0 < q ∧ q < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    ∀ E : Set (Ω n), MeasurableSet E → Q n E ≤ p → P n E ≤ q

/-- **Uniform mutual absolute continuity in the limit** (GMS21, Definition 3.2): each of `{P n}`
and `{Q n}` is uniformly absolutely continuous as `n → ∞` with respect to the other. -/
def UniformlyMutuallyAbsolutelyContinuous (P Q : ∀ n, Measure (Ω n)) : Prop :=
  UniformlyAbsolutelyContinuous P Q ∧ UniformlyAbsolutelyContinuous Q P

theorem UniformlyMutuallyAbsolutelyContinuous.symm {P Q : ∀ n, Measure (Ω n)}
    (h : UniformlyMutuallyAbsolutelyContinuous P Q) :
    UniformlyMutuallyAbsolutelyContinuous Q P :=
  ⟨h.2, h.1⟩

/-- **Vanishing probabilities, measurable events.** If `{Q n}` is uniformly absolutely continuous
as `n → ∞` with respect to `{P n}` and `Q n (E n) → 0` for measurable events `E n`, then
`P n (E n) → 0`. If `P n (E n) ≥ c > 0` infinitely often, then `P n (E n)ᶜ ≤ 1 - c`, so
`Q n (E n)ᶜ ≤ q(1 - c) < 1` for large `n`, and `Q n (E n) ≥ 1 - q(1 - c) > 0`. -/
theorem UniformlyAbsolutelyContinuous.tendsto_measure_zero_of_measurableSet
    {P Q : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (hQP : UniformlyAbsolutelyContinuous Q P)
    {E : ∀ n, Set (Ω n)} (hE : ∀ n, MeasurableSet (E n))
    (hQ : Tendsto (fun n => Q n (E n)) atTop (𝓝 0)) :
    Tendsto (fun n => P n (E n)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨c, hc0, hc1, hcε⟩ := exists_pos_lt_one_le_of_pos hε
  obtain ⟨q, -, hq1, N, hN⟩ := hQP (1 - c) (tsub_pos_of_lt hc1)
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc0.ne')
  filter_upwards [hQ.eventually (gt_mem_nhds (tsub_pos_of_lt hq1)), eventually_ge_atTop N]
    with n hQn hNn
  by_contra hPn
  have hPc : P n (E n)ᶜ ≤ 1 - c := by
    rw [prob_compl_eq_one_sub (hE n)]
    exact tsub_le_tsub_left (hcε.trans (not_le.1 hPn).le) 1
  have hQc : Q n (E n)ᶜ ≤ q := hN n hNn (E n)ᶜ (hE n).compl hPc
  have hQE : 1 - q ≤ Q n (E n) := by
    rw [prob_eq_one_sub_prob_compl (hE n)]
    exact tsub_le_tsub_left hQc 1
  exact absurd hQn (not_lt.2 hQE)

/-- **Vanishing probabilities.** If `{Q n}` is uniformly absolutely continuous as `n → ∞` with
respect to `{P n}` and the (outer) probabilities `Q n (E n)` tend to `0`, then so do the (outer)
probabilities `P n (E n)`; the events `E n` need not be measurable. -/
theorem UniformlyAbsolutelyContinuous.tendsto_measure_zero
    {P Q : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (hQP : UniformlyAbsolutelyContinuous Q P)
    {E : ∀ n, Set (Ω n)} (hQ : Tendsto (fun n => Q n (E n)) atTop (𝓝 0)) :
    Tendsto (fun n => P n (E n)) atTop (𝓝 0) := by
  have hS := hQP.tendsto_measure_zero_of_measurableSet
    (E := fun n => toMeasurable (Q n) (E n)) (fun n => measurableSet_toMeasurable _ _)
    (by simpa only [measure_toMeasurable] using hQ)
  rw [ENNReal.tendsto_nhds_zero] at hS ⊢
  intro ε hε
  filter_upwards [hS ε hε] with n hn
  exact (measure_mono (subset_toMeasurable _ _)).trans hn

/-- **Vanishing probabilities under uniform mutual absolute continuity.** -/
theorem UniformlyMutuallyAbsolutelyContinuous.tendsto_measure_zero_iff
    {P Q : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    [∀ n, IsProbabilityMeasure (Q n)] (h : UniformlyMutuallyAbsolutelyContinuous P Q)
    {E : ∀ n, Set (Ω n)} :
    Tendsto (fun n => P n (E n)) atTop (𝓝 0) ↔ Tendsto (fun n => Q n (E n)) atTop (𝓝 0) :=
  ⟨h.1.tendsto_measure_zero, h.2.tendsto_measure_zero⟩

end Sequences

section Laws

variable {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]

/-- Outer-measure transport along an almost everywhere measurable map. -/
private theorem measure_preimage_le_map_apply_of_aemeasurable {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) {f : α → β} (hf : AEMeasurable f μ) (B : Set β) :
    μ (f ⁻¹' B) ≤ μ.map f B :=
  calc μ (f ⁻¹' B) ≤ μ (f ⁻¹' toMeasurable (μ.map f) B) :=
        measure_mono (preimage_mono (subset_toMeasurable _ _))
    _ = μ.map f (toMeasurable (μ.map f) B) :=
        (Measure.map_apply_of_aemeasurable hf (measurableSet_toMeasurable _ _)).symm
    _ = μ.map f B := measure_toMeasurable B

/-- **Transfer of vanishing probabilities through laws of configurations.** Let `X₁ n` and `X₂ n`
be random configurations on probability spaces `(Ω₁, P₁)` and `(Ω₂, P₂)`, taking values in a
common measurable space `S n`, such that the laws of `X₂ n` are uniformly absolutely continuous as
`n → ∞` with respect to the laws of `X₁ n`. If the law of `X₂ n` puts vanishing (outer) mass on
`A n`, then `P₁ {X₁ n ∈ A n} → 0`. -/
theorem UniformlyAbsolutelyContinuous.tendsto_measure_preimage_zero
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {X₁ : ∀ n, Ω₁ → S n} {X₂ : ∀ n, Ω₂ → S n}
    (hX₁ : ∀ n, AEMeasurable (X₁ n) P₁) (hX₂ : ∀ n, AEMeasurable (X₂ n) P₂)
    (h : UniformlyAbsolutelyContinuous (fun n => P₂.map (X₂ n)) (fun n => P₁.map (X₁ n)))
    {A : ∀ n, Set (S n)} (hA : Tendsto (fun n => P₂.map (X₂ n) (A n)) atTop (𝓝 0)) :
    Tendsto (fun n => P₁ (X₁ n ⁻¹' A n)) atTop (𝓝 0) := by
  have h₁ : ∀ n, IsProbabilityMeasure (P₁.map (X₁ n)) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hX₁ n)).2 inferInstance
  have h₂ : ∀ n, IsProbabilityMeasure (P₂.map (X₂ n)) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hX₂ n)).2 inferInstance
  have hlaw := h.tendsto_measure_zero hA
  rw [ENNReal.tendsto_nhds_zero] at hlaw ⊢
  intro ε hε
  filter_upwards [hlaw ε hε] with n hn
  exact (measure_preimage_le_map_apply_of_aemeasurable P₁ (hX₁ n) (A n)).trans hn

/-- **Transfer of vanishing probabilities through laws of configurations, mutual form.** If the
laws of the configurations `X₁ n` and `X₂ n` are uniformly mutually absolutely continuous as
`n → ∞` and the events `A n` are measurable, then `P₁ {X₁ n ∈ A n} → 0` if and only if
`P₂ {X₂ n ∈ A n} → 0`. -/
theorem UniformlyMutuallyAbsolutelyContinuous.tendsto_measure_preimage_zero_iff
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {X₁ : ∀ n, Ω₁ → S n} {X₂ : ∀ n, Ω₂ → S n}
    (hX₁ : ∀ n, AEMeasurable (X₁ n) P₁) (hX₂ : ∀ n, AEMeasurable (X₂ n) P₂)
    (h : UniformlyMutuallyAbsolutelyContinuous (fun n => P₁.map (X₁ n))
      (fun n => P₂.map (X₂ n)))
    {A : ∀ n, Set (S n)} (hA : ∀ n, MeasurableSet (A n)) :
    Tendsto (fun n => P₁ (X₁ n ⁻¹' A n)) atTop (𝓝 0) ↔
      Tendsto (fun n => P₂ (X₂ n ⁻¹' A n)) atTop (𝓝 0) := by
  have h₁ : ∀ n, IsProbabilityMeasure (P₁.map (X₁ n)) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hX₁ n)).2 inferInstance
  have h₂ : ∀ n, IsProbabilityMeasure (P₂.map (X₂ n)) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hX₂ n)).2 inferInstance
  have e₁ : (fun n => P₁ (X₁ n ⁻¹' A n)) = fun n => P₁.map (X₁ n) (A n) :=
    funext fun n => (Measure.map_apply_of_aemeasurable (hX₁ n) (hA n)).symm
  have e₂ : (fun n => P₂ (X₂ n ⁻¹' A n)) = fun n => P₂.map (X₂ n) (A n) :=
    funext fun n => (Measure.map_apply_of_aemeasurable (hX₂ n) (hA n)).symm
  rw [e₁, e₂]
  exact h.tendsto_measure_zero_iff

end Laws

section Constant

variable {α : Type*} [MeasurableSpace α]

/-- **Fixed laws.** If `Q ≪ P` for probability measures `P` and `Q`, then the constant sequence
`P` is uniformly absolutely continuous as `n → ∞` with respect to the constant sequence `Q`: an
event with `Q E ≤ p < 1` has complement of `Q`-probability at least `1 - p`, hence of
`P`-probability at least some `d > 0` (absolute continuity of `Q` with respect to `P`), so
`P E ≤ 1 - d`. -/
theorem uniformlyAbsolutelyContinuous_const {P Q : Measure α} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hQP : Q ≪ P) :
    UniformlyAbsolutelyContinuous (Ω := fun _ => α) (fun _ => P) (fun _ => Q) := by
  intro p _ hp1
  have hp0' : 1 - p ≠ 0 := (tsub_pos_of_lt hp1).ne'
  have hp' : (1 - p) / 2 < 1 - p :=
    ENNReal.half_lt_self hp0' (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  obtain ⟨d, hd0, hd⟩ :=
    LatticeProb.exists_measure_le_of_absolutelyContinuous Q P hQP (ENNReal.half_pos hp0')
  obtain ⟨d', hd'0, hd'1, hd'd⟩ := exists_pos_lt_one_le_of_pos hd0
  refine ⟨1 - d', tsub_pos_of_lt hd'1,
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hd'0.ne', 0, fun _ _ E hE hQE => ?_⟩
  have hE' : MeasurableSet (E : Set α) := hE
  have hQE' : Q E ≤ p := hQE
  have hdE : d < P Eᶜ := by
    by_contra hle
    have h1 : Q Eᶜ ≤ (1 - p) / 2 := hd Eᶜ (not_lt.1 hle)
    have h2 : 1 - p ≤ Q Eᶜ := by
      rw [prob_compl_eq_one_sub hE']
      exact tsub_le_tsub_left hQE' 1
    exact absurd (h2.trans h1) (not_le.2 hp')
  show P E ≤ 1 - d'
  rw [prob_eq_one_sub_prob_compl hE']
  exact tsub_le_tsub_left (hd'd.trans hdE.le) 1

/-- **Fixed mutually absolutely continuous laws** are uniformly mutually absolutely continuous
as constant sequences. -/
theorem uniformlyMutuallyAbsolutelyContinuous_const {P Q : Measure α} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    UniformlyMutuallyAbsolutelyContinuous (Ω := fun _ => α) (fun _ => P) (fun _ => Q) :=
  ⟨uniformlyAbsolutelyContinuous_const hQP, uniformlyAbsolutelyContinuous_const hPQ⟩

end Constant

end MatedCRT
