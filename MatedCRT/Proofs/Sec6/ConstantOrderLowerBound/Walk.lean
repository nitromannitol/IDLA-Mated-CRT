import MatedCRT.Steps.Sec6.ConstantOrderLowerBound
import MatedCRT.Proofs.WalkPotential.Markov

/-!
# Lemma 6.7: the walk steps

From the Markov property at the first step (`srwLaw_apply_eq_lintegral`, MatedCRT/Proofs/WalkPotential/Markov.lean):

* `srwAeAdjacentStep`: each step of simple random walk is along an edge or a (junk) stay, almost surely;
* `srwHitDecompositionStep`: the strong Markov property at the hitting time of a set `B`, in the form
  `P^a[X hits B and (X_{T+i})_i ∈ F] ≤ sup_{b ∈ B} P^b[F]`; by induction on a bound `N` for the hitting time.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace WalkSteps

/-- One step of the walk from `a` does not go to a non-neighbour other than `a`. -/
theorem srwStep_nonadjacent_null (m : ℤ → ℤ → ℕ) (a : ℤ) : srwStep m a {b | b ≠ a ∧ m a b = 0} = 0 := by
  have hT : MeasurableSet {b : ℤ | b ≠ a ∧ m a b = 0} := (Set.to_countable _).measurableSet
  unfold srwStep
  split_ifs with h
  · have hzero : edgeMeasure m a {b | b ≠ a ∧ m a b = 0} = 0 := by
      unfold edgeMeasure
      rw [Measure.sum_apply _ hT]
      refine ENNReal.tsum_eq_zero.2 fun b => ?_
      rw [Measure.smul_apply, smul_eq_mul]
      by_cases hb : b ∈ {b : ℤ | b ≠ a ∧ m a b = 0}
      · rw [hb.2]
        simp
      · rw [Measure.dirac_apply' _ hT, Set.indicator_of_notMem hb, mul_zero]
    rw [ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply, hzero, smul_zero]
  · rw [Measure.dirac_apply' _ hT, Set.indicator_of_notMem fun h => h.1 rfl]

theorem srwLaw_nonadjacent_null (m : ℤ → ℤ → ℕ) :
    ∀ (n : ℕ) (a : ℤ), srwLaw m a {x | ¬ (x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)} = 0 := by
  have hmeas : ∀ n : ℕ, MeasurableSet {x : ℕ → ℤ | ¬ (x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)} := by
    intro n
    have : {x : ℕ → ℤ | ¬ (x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)} =
        (fun x : ℕ → ℤ => fun i : Fin 2 => x (n + i)) ⁻¹' {z | ¬ (z 1 = z 0 ∨ m (z 0) (z 1) ≠ 0)} := by
      ext x
      simp
    rw [this]
    exact (Set.to_countable _).measurableSet.preimage (Measurable.of_eval fun i => measurable_pi_apply _)
  intro n
  induction n with
  | zero =>
    intro a
    rw [srwLaw_apply_eq_lintegral m a (hmeas 0)]
    refine le_antisymm ?_ zero_le
    have hT : MeasurableSet {b : ℤ | b ≠ a ∧ m a b = 0} := (Set.to_countable _).measurableSet
    calc ∫⁻ b, srwLaw m b (pathCons a ⁻¹' {x | ¬ (x (0 + 1) = x 0 ∨ m (x 0) (x (0 + 1)) ≠ 0)}) ∂srwStep m a
        ≤ ∫⁻ b, {b : ℤ | b ≠ a ∧ m a b = 0}.indicator 1 b ∂srwStep m a := by
          refine lintegral_mono fun b => ?_
          by_cases hb : b ∈ {b : ℤ | b ≠ a ∧ m a b = 0}
          · rw [Set.indicator_of_mem hb]
            exact prob_le_one
          · rw [Set.indicator_of_notMem hb]
            have hsub : pathCons a ⁻¹' {x : ℕ → ℤ | ¬ (x (0 + 1) = x 0 ∨ m (x 0) (x (0 + 1)) ≠ 0)} ⊆
                {y : ℕ → ℤ | ¬ y 0 = b} := by
              intro y hy hy0
              simp only [mem_preimage, mem_ofPred_eq, pathCons_zero, zero_add, pathCons_succ] at hy
              rw [hy0] at hy
              exact hy (by
                by_contra hcon
                push Not at hcon
                exact hb ⟨hcon.1, hcon.2⟩)
            exact le_of_eq (measure_mono_null hsub (ae_iff.1 (srwLaw_ae_start m b)))
      _ = srwStep m a {b | b ≠ a ∧ m a b = 0} := lintegral_indicator_one hT
      _ = 0 := srwStep_nonadjacent_null m a
  | succ n ih =>
    intro a
    rw [srwLaw_apply_eq_lintegral m a (hmeas (n + 1))]
    have hpre : pathCons a ⁻¹' {x : ℕ → ℤ | ¬ (x (n + 1 + 1) = x (n + 1) ∨ m (x (n + 1)) (x (n + 1 + 1)) ≠ 0)} =
        {x | ¬ (x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)} := by
      ext y
      simp only [mem_preimage, mem_ofPred_eq, pathCons_succ]
    rw [hpre]
    simp only [ih, lintegral_zero]

end WalkSteps

open WalkSteps in
/-- **`SrwAeAdjacentStep`**: simple random walk moves along edges (or stays, at junk vertices). -/
theorem srwAeAdjacentStep : SrwAeAdjacentStep := fun m a =>
  ae_all_iff.2 fun n => ae_iff.2 (srwLaw_nonadjacent_null m n a)

namespace WalkSteps

/-- The walk hits `B` at time `n` (for the first time) and from there lies in `F`. -/
def hitAt (B : Set ℤ) (F : Set (ℕ → ℤ)) (n : ℕ) : Set (ℕ → ℤ) :=
  (fun x : ℕ → ℤ => x n) ⁻¹' B ∩ (⋂ j ∈ Iio n, (fun x : ℕ → ℤ => x j) ⁻¹' Bᶜ) ∩
    (fun x : ℕ → ℤ => fun i => x (n + i)) ⁻¹' F

/-- The walk hits `B` by time `N` and from its hitting position lies in `F`. -/
def hitBy (B : Set ℤ) (F : Set (ℕ → ℤ)) (N : ℕ) : Set (ℕ → ℤ) :=
  ⋃ n ∈ Iic N, hitAt B F n

theorem mem_hitAt {B : Set ℤ} {F : Set (ℕ → ℤ)} {n : ℕ} {x : ℕ → ℤ} :
    x ∈ hitAt B F n ↔ x n ∈ B ∧ (∀ j < n, x j ∉ B) ∧ (fun i => x (n + i)) ∈ F := by
  simp [hitAt, and_assoc]

theorem measurableSet_hitAt (B : Set ℤ) {F : Set (ℕ → ℤ)} (hF : MeasurableSet F) (n : ℕ) :
    MeasurableSet (hitAt B F n) :=
  (((Set.to_countable B).measurableSet.preimage (measurable_pi_apply n)).inter
    (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      (Set.to_countable Bᶜ).measurableSet.preimage (measurable_pi_apply j))).inter
    (hF.preimage (Measurable.of_eval fun _ => measurable_pi_apply _))

theorem measurableSet_hitBy (B : Set ℤ) {F : Set (ℕ → ℤ)} (hF : MeasurableSet F) (N : ℕ) :
    MeasurableSet (hitBy B F N) :=
  MeasurableSet.biUnion (Set.to_countable _) fun n _ => measurableSet_hitAt B hF n

theorem srwLaw_hitBy_le (m : ℤ → ℤ → ℕ) (B : Set ℤ) {F : Set (ℕ → ℤ)} (hF : MeasurableSet F) {c : ℝ≥0∞}
    (hc : ∀ b ∈ B, srwLaw m b F ≤ c) : ∀ (N : ℕ) (a : ℤ), srwLaw m a (hitBy B F N) ≤ c := by
  have hstart : ∀ a : ℤ, srwLaw m a {x | x 0 ≠ a} = 0 := fun a => ae_iff.1 (srwLaw_ae_start m a)
  have hinB : ∀ (N : ℕ) (a : ℤ), a ∈ B → srwLaw m a (hitBy B F N) ≤ c := by
    intro N a ha
    have hsub : hitBy B F N ⊆ F ∪ {x | x 0 ≠ a} := by
      intro x hx
      obtain ⟨n, -, hxn⟩ := mem_iUnion₂.1 hx
      rw [mem_hitAt] at hxn
      by_cases hx0 : x 0 = a
      · left
        cases n with
        | zero =>
          have he : (fun i => x (0 + i)) = x := funext fun i => by rw [zero_add]
          rw [← he]
          exact hxn.2.2
        | succ k =>
          exact absurd (hx0 ▸ ha) (hxn.2.1 0 (Nat.succ_pos k))
      · right
        exact hx0
    calc srwLaw m a (hitBy B F N) ≤ srwLaw m a (F ∪ {x | x 0 ≠ a}) := measure_mono hsub
      _ ≤ srwLaw m a F + srwLaw m a {x | x 0 ≠ a} := measure_union_le _ _
      _ ≤ c := by rw [hstart a, add_zero]; exact hc a ha
  intro N
  induction N with
  | zero =>
    intro a
    by_cases ha : a ∈ B
    · exact hinB 0 a ha
    · have hsub : hitBy B F 0 ⊆ {x : ℕ → ℤ | x 0 ≠ a} := by
        intro x hx hx0
        obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.1 hx
        rw [mem_Iic, Nat.le_zero] at hn
        subst hn
        rw [mem_hitAt] at hxn
        exact ha (hx0 ▸ hxn.1)
      exact le_trans (le_of_eq (measure_mono_null hsub (hstart a))) zero_le
  | succ N ih =>
    intro a
    by_cases ha : a ∈ B
    · exact hinB (N + 1) a ha
    · rw [srwLaw_apply_eq_lintegral m a (measurableSet_hitBy B hF (N + 1))]
      have hpre : pathCons a ⁻¹' hitBy B F (N + 1) ⊆ hitBy B F N := by
        intro y hy
        obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.1 hy
        rw [mem_hitAt] at hyn
        cases n with
        | zero => exact absurd hyn.1 ha
        | succ k =>
          refine mem_iUnion₂.2 ⟨k, mem_Iic.2 (by rw [mem_Iic] at hn; omega), mem_hitAt.2 ⟨hyn.1, ?_, ?_⟩⟩
          · intro j hj
            exact hyn.2.1 (j + 1) (by omega)
          · have he : (fun i => pathCons a y (k + 1 + i)) = fun i => y (k + i) := by
              funext i
              rw [show k + 1 + i = (k + i) + 1 by omega]
              rfl
            rw [← he]
            exact hyn.2.2
      calc ∫⁻ b, srwLaw m b (pathCons a ⁻¹' hitBy B F (N + 1)) ∂srwStep m a
          ≤ ∫⁻ _, c ∂srwStep m a := lintegral_mono fun b => (measure_mono hpre).trans (ih b)
        _ = c := by rw [lintegral_const, measure_univ, mul_one]

end WalkSteps

open WalkSteps in
/-- **`SrwHitDecompositionStep`**: the strong Markov property at the hitting time of `B`. -/
theorem srwHitDecompositionStep : SrwHitDecompositionStep := by
  intro m a B F c hF hc
  have hsub : {x : ℕ → ℤ | ∃ n : ℕ, x n ∈ B ∧ (∀ j < n, x j ∉ B) ∧ (fun i => x (n + i)) ∈ F} ⊆
      ⋃ N, hitBy B F N := by
    rintro x ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, mem_iUnion₂.2 ⟨n, mem_Iic.2 le_rfl, mem_hitAt.2 hn⟩⟩
  have hmono : Monotone (hitBy B F) := fun N N' h =>
    biUnion_subset_biUnion_left (Iic_subset_Iic.2 h)
  calc srwLaw m a {x | ∃ n : ℕ, x n ∈ B ∧ (∀ j < n, x j ∉ B) ∧ (fun i => x (n + i)) ∈ F}
      ≤ srwLaw m a (⋃ N, hitBy B F N) := measure_mono hsub
    _ = ⨆ N, srwLaw m a (hitBy B F N) := hmono.measure_iUnion
    _ ≤ c := iSup_le fun N => srwLaw_hitBy_le m B hF hc N a

end MatedCRT
