import MatedCRT.Proofs.Sec4.ConvergenceDivisible.LaplacianMeasurable
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.GreenMeasurable
import MatedCRT.Proofs.Sec4.Equibounded

/-! # Measurability of discrete supersolution constraints -/

namespace MatedCRT

open Set MeasureTheory

/-- For a measurable candidate, all the inequalities in the discrete
obstacle problem form a measurable event. -/
theorem MatedCRTEnv.IsValid.measurableSet_discreteSupersolution
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (r φ u : Ω → ℤ → ℝ) (hr : ∀ b, Measurable fun ω => r ω b)
    (hφ : ∀ b, Measurable fun ω => φ ω b) (hu : ∀ b, Measurable fun ω => u ω b) :
    MeasurableSet {ω | (∀ b ∈ V ω, mLaplacian (S.mult ε ω) (u ω) b ≤ r ω b) ∧
      ∀ b ∈ W ω, φ ω b ≤ u ω b} := by
  have hVb : ∀ b, MeasurableSet {ω | b ∈ V ω} := fun b =>
    measurableSet_setOfPred.mpr ((measurable_set_mem b).comp hV)
  have hWb : ∀ b, MeasurableSet {ω | b ∈ W ω} := fun b =>
    measurableSet_setOfPred.mpr ((measurable_set_mem b).comp hW)
  have heq : {ω | (∀ b ∈ V ω, mLaplacian (S.mult ε ω) (u ω) b ≤ r ω b) ∧
      ∀ b ∈ W ω, φ ω b ≤ u ω b} =
      (⋂ b, (({ω | b ∈ V ω})ᶜ ∪ {ω | mLaplacian (S.mult ε ω) (u ω) b ≤ r ω b})) ∩
      (⋂ b, (({ω | b ∈ W ω})ᶜ ∪ {ω | φ ω b ≤ u ω b})) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
    classical
    simp only [← imp_iff_not_or]
  rw [heq]
  exact (MeasurableSet.iInter fun b => (hVb b).compl.union
    (measurableSet_le (hS.measurable_mLaplacian ε u hu b) (hr b))).inter
    (MeasurableSet.iInter fun b => (hWb b).compl.union (measurableSet_le (hφ b) (hu b)))

/-- A countable family of measurable supersolutions with arbitrarily good pointwise
values makes the least supersolution measurable. The approximation hypothesis
is stated separately because it requires analysis of the finite graph. -/
theorem MatedCRTEnv.IsValid.measurable_discreteLeastSupersolution_of_countable
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (r φ : Ω → ℤ → ℝ) (hr : ∀ b, Measurable fun ω => r ω b)
    (hφ : ∀ b, Measurable fun ω => φ ω b) (a : ℤ)
    (u : ℕ → Ω → ℤ → ℝ) (hu : ∀ n b, Measurable fun ω => u n ω b)
    (hne : ∀ ω, ∃ v : ℤ → ℝ,
      (∀ b ∈ V ω, mLaplacian (S.mult ε ω) v b ≤ r ω b) ∧
      ∀ b ∈ W ω, φ ω b ≤ v b)
    (hbdd : ∀ ω, BddBelow ((fun v : ℤ → ℝ => v a) ''
      {v | (∀ b ∈ V ω, mLaplacian (S.mult ε ω) v b ≤ r ω b) ∧
        ∀ b ∈ W ω, φ ω b ≤ v b}))
    (happrox : ∀ ω (v : ℤ → ℝ),
      ((∀ b ∈ V ω, mLaplacian (S.mult ε ω) v b ≤ r ω b) ∧
        ∀ b ∈ W ω, φ ω b ≤ v b) → ∀ q : ℝ, v a < q →
      ∃ n, ((∀ b ∈ V ω, mLaplacian (S.mult ε ω) (u n ω) b ≤ r ω b) ∧
        ∀ b ∈ W ω, φ ω b ≤ u n ω b) ∧ u n ω a < q) :
    Measurable fun ω => discreteLeastSupersolution (S.mult ε ω) (V ω) (W ω)
      (r ω) (φ ω) a := by
  apply measurable_of_Iio
  intro q
  have heq : {ω | discreteLeastSupersolution (S.mult ε ω) (V ω) (W ω)
      (r ω) (φ ω) a < q} =
      ⋃ n, ({ω | (∀ b ∈ V ω, mLaplacian (S.mult ε ω) (u n ω) b ≤ r ω b) ∧
        ∀ b ∈ W ω, φ ω b ≤ u n ω b} ∩ {ω | u n ω a < q}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    rw [discreteLeastSupersolution, csInf_lt_iff (hbdd ω) (by
      obtain ⟨v, hv⟩ := hne ω
      exact ⟨v a, ⟨v, hv, rfl⟩⟩)]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, hlt⟩
      exact happrox ω v hv q hlt
    · rintro ⟨n, hn, hlt⟩
      exact ⟨u n ω a, ⟨u n ω, hn, rfl⟩, hlt⟩
  change MeasurableSet {ω | discreteLeastSupersolution (S.mult ε ω) (V ω) (W ω)
    (r ω) (φ ω) a < q}
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    (hS.measurableSet_discreteSupersolution ε V W hV hW r φ (u n) hr hφ (hu n)).inter
      (measurableSet_lt (hu n a) measurable_const)

/-- For a nonpositive obstacle and a nonnegative threshold, the zero function
is admissible. This version of the countable criterion also covers vertices
outside the obstacle domain, where the real infimum is zero. -/
theorem MatedCRTEnv.IsValid.measurable_discreteLeastSupersolution_of_countable_on_domain
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε : ℝ) (V W : Ω → Set ℤ) (hV : Measurable V) (hW : Measurable W)
    (r φ : Ω → ℤ → ℝ) (hr : ∀ b, Measurable fun ω => r ω b)
    (hφ : ∀ b, Measurable fun ω => φ ω b) (a : ℤ)
    (u : ℕ → Ω → ℤ → ℝ) (hu : ∀ n b, Measurable fun ω => u n ω b)
    (hVW : ∀ ω, V ω ⊆ W ω) (hr0 : ∀ ω b, 0 ≤ r ω b)
    (hφ0 : ∀ ω b, φ ω b ≤ 0)
    (happrox : ∀ ω, a ∈ W ω → ∀ (v : ℤ → ℝ),
      ((∀ b ∈ V ω, mLaplacian (S.mult ε ω) v b ≤ r ω b) ∧
        ∀ b ∈ W ω, φ ω b ≤ v b) → ∀ q : ℝ, v a < q →
      ∃ n, ((∀ b ∈ V ω, mLaplacian (S.mult ε ω) (u n ω) b ≤ r ω b) ∧
        ∀ b ∈ W ω, φ ω b ≤ u n ω b) ∧ u n ω a < q) :
    Measurable fun ω => discreteLeastSupersolution (S.mult ε ω) (V ω) (W ω)
      (r ω) (φ ω) a := by
  apply measurable_of_Iio
  intro q
  have hWa : MeasurableSet {ω | a ∈ W ω} :=
    measurableSet_setOfPred.mpr ((measurable_set_mem a).comp hW)
  have heq : {ω | discreteLeastSupersolution (S.mult ε ω) (V ω) (W ω)
      (r ω) (φ ω) a < q} =
      ({ω | a ∈ W ω} ∩ ⋃ n, ({ω | (∀ b ∈ V ω,
        mLaplacian (S.mult ε ω) (u n ω) b ≤ r ω b) ∧
        ∀ b ∈ W ω, φ ω b ≤ u n ω b} ∩ {ω | u n ω a < q})) ∪
      ({ω | a ∈ W ω}ᶜ ∩ {ω | (0 : ℝ) < q}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iUnion, mem_compl_iff]
    by_cases ha : a ∈ W ω
    · simp only [ha, true_and, not_true_eq_false, false_and, or_false]
      have hne : ((fun v : ℤ → ℝ => v a) ''
          {v | (∀ b ∈ V ω, mLaplacian (S.mult ε ω) v b ≤ r ω b) ∧
            ∀ b ∈ W ω, φ ω b ≤ v b}).Nonempty := by
        refine ⟨0, ⟨fun _ => 0, ⟨?_, ?_⟩, rfl⟩⟩
        · intro b hb
          simpa [mLaplacian] using hr0 ω b
        · exact fun b _ => hφ0 ω b
      have hbdd : BddBelow ((fun v : ℤ → ℝ => v a) ''
          {v | (∀ b ∈ V ω, mLaplacian (S.mult ε ω) v b ≤ r ω b) ∧
            ∀ b ∈ W ω, φ ω b ≤ v b}) := by
        refine ⟨φ ω a, ?_⟩
        rintro _ ⟨v, hv, rfl⟩
        exact hv.2 a ha
      rw [discreteLeastSupersolution, csInf_lt_iff hbdd hne]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, hlt⟩
        exact happrox ω ha v hv q hlt
      · rintro ⟨n, hn, hlt⟩
        exact ⟨u n ω a, ⟨u n ω, hn, rfl⟩, hlt⟩
    · simp only [ha, false_and, not_false_eq_true, true_and, false_or]
      rw [Equibounded.discreteLeastSupersolution_eq_zero_of_not_mem
        (fun h => ha (hVW ω h)) ha]
  change MeasurableSet {ω | discreteLeastSupersolution (S.mult ε ω) (V ω) (W ω)
    (r ω) (φ ω) a < q}
  rw [heq]
  exact (hWa.inter (MeasurableSet.iUnion fun n =>
    (hS.measurableSet_discreteSupersolution ε V W hV hW r φ (u n) hr hφ (hu n)).inter
      (measurableSet_lt (hu n a) measurable_const))).union
    (hWa.compl.inter (MeasurableSet.const _))

end MatedCRT
