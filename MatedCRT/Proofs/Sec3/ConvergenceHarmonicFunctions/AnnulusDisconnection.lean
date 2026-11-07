import MatedCRT.Defs.WalkDisconnection
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.AtAnnulus
import MatedCRT.Proofs.IDLA.StrongMarkov

/-! # Walk traces and annulus disconnection -/

namespace MatedCRT

open Set
open MeasureTheory
open scoped ENNReal

/-- A disconnecting vertex set intersects every graph walk from the separated
vertex to the target set. -/
theorem graphDisconnects_intersects_walk {V : Type*} {G : SimpleGraph V}
    {K A : Set V} {y a : V} (h : graphDisconnects G K y A) (ha : a ∈ A)
    (w : G.Walk y a) : ∃ v ∈ w.support, v ∈ K := by
  classical
  by_contra hn
  have hw : ∀ v ∈ w.support, v ∈ Kᶜ := by
    intro v hv
    simp only [mem_compl_iff]
    intro hvK
    exact hn ⟨v, hv, hvK⟩
  exact h (hw y w.start_mem_support) a ha (hw a w.end_mem_support)
    ⟨w.induce Kᶜ hw⟩

/-- If a walk disconnects a vertex from a target before hitting the target,
then every graph walk joining them contains a vertex visited before the hit. -/
theorem walkDisconnectsBeforeHit_intersects_walk
    {m : ℤ → ℤ → ℕ} {A : Set ℤ} {y a : ℤ} {x : ℕ → ℤ}
    (h : walkDisconnectsBeforeHit m A y x) (ha : a ∈ A)
    (w : (adjGraph m).Walk y a) :
    ∃ n : ℕ, (n : ℕ∞) < vHitTime A x ∧ x n ∈ w.support := by
  obtain ⟨v, hv, ⟨n, hn, hnv⟩⟩ := graphDisconnects_intersects_walk h ha w
  exact ⟨n, hn, hnv ▸ hv⟩

/-- A graph walk supported outside an open region rules out disconnection by
a trace contained in that region. This is the graph-theoretic part of the
planar separation step in the annulus argument. -/
theorem not_walkDisconnectsBeforeHit_of_avoiding_region
    {m : ℤ → ℤ → ℕ} {A U : Set ℤ} {y a : ℤ} {x : ℕ → ℤ}
    (ha : a ∈ A) (w : (adjGraph m).Walk y a)
    (hw : ∀ v ∈ w.support, v ∉ U)
    (hx : ∀ n : ℕ, (n : ℕ∞) < vHitTime A x → x n ∈ U) :
    ¬ walkDisconnectsBeforeHit m A y x := by
  intro h
  obtain ⟨n, hn, hnw⟩ := walkDisconnectsBeforeHit_intersects_walk h ha w
  exact hw (x n) hnw (hx n hn)

/-- Once a separating graph walk outside `U` has been constructed, the
annulus-disconnection event forces a visit outside `U` before the outer hit. -/
theorem measure_disconnection_le_visit_outside
    {m : ℤ → ℤ → ℕ} {A U : Set ℤ} {y a : ℤ}
    (ha : a ∈ A) (w : (adjGraph m).Walk y a)
    (hw : ∀ v ∈ w.support, v ∉ U) (μ : MeasureTheory.Measure (ℕ → ℤ)) :
    μ {x | walkDisconnectsBeforeHit m A y x} ≤
      μ {x | ∃ n : ℕ, (n : ℕ∞) < vHitTime A x ∧ x n ∉ U} := by
  apply MeasureTheory.measure_mono
  intro x hx
  obtain ⟨n, hn, hnw⟩ := walkDisconnectsBeforeHit_intersects_walk hx ha w
  exact ⟨n, hn, hw (x n) hnw⟩

/-- The simultaneous annulus-disconnection event controls the probability
of leaving a region before hitting the outer target, whenever there is a
connecting graph walk outside the region. -/
theorem measure_simultaneous_disconnection_le_visit_outside
    {m : ℤ → ℤ → ℕ} {A I U : Set ℤ} {y a : ℤ}
    (hy : y ∈ I) (ha : a ∈ A) (w : (adjGraph m).Walk y a)
    (hw : ∀ v ∈ w.support, v ∉ U) (μ : MeasureTheory.Measure (ℕ → ℤ)) :
    μ {x | ∀ y ∈ I, walkDisconnectsBeforeHit m A y x} ≤
      μ {x | ∃ n : ℕ, (n : ℕ∞) < vHitTime A x ∧ x n ∉ U} := by
  calc
    μ {x | ∀ y ∈ I, walkDisconnectsBeforeHit m A y x} ≤
        μ {x | walkDisconnectsBeforeHit m A y x} :=
      MeasureTheory.measure_mono (fun _ hx => hx y hy)
    _ ≤ _ := measure_disconnection_le_visit_outside ha w hw μ

/-- A uniform lower bound for annulus disconnection gives a one-stage
survival probability at most `1 - p`. The connecting graph walk is the
output of the planar separation construction. -/
theorem srwLaw_stay_le_of_annulus_disconnection
    {m : ℤ → ℤ → ℕ} {A I U : Set ℤ} {y a v : ℤ} {p : ℝ}
    (hy : y ∈ I) (ha : a ∈ A) (w : (adjGraph m).Walk y a)
    (hw : ∀ u ∈ w.support, u ∉ U) (hp : 0 ≤ p)
    (hdisc : ENNReal.ofReal p ≤ srwLaw m v
      {x | ∀ y ∈ I, walkDisconnectsBeforeHit m A y x}) :
    srwLaw m v {x | ∀ n : ℕ, (n : ℕ∞) < vHitTime A x → x n ∈ U} ≤
      ENNReal.ofReal (1 - p) := by
  have hvisit : ENNReal.ofReal p ≤ srwLaw m v
      {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime Aᶜ x ∧ x n ∈ Aᶜ \ U} := by
    refine (hdisc.trans (measure_simultaneous_disconnection_le_visit_outside hy ha w hw
      (srwLaw m v))).trans ?_
    apply MeasureTheory.measure_mono
    rintro x ⟨n, hn, hout⟩
    have hn' : (n : ℕ∞) < vExitTime Aᶜ x := hn
    exact ⟨n, hn', (ConstantOrderDiv.lt_vExitTime_iff'.1 hn') n le_rfl, hout⟩
  exact ConstantOrderDiv.prob_stay_le (W := Aᶜ) (U := Aᶜ) (A := U)
    (Subset.rfl) hp hvisit

/-- A uniform continuation bound can be applied at a finite hitting time.
The weight selects the admissible restart vertices. -/
theorem lintegral_hitTime_continuation_le
    (m : ℤ → ℤ → ℕ) (D : Set ℤ) (h : ℤ → ℝ≥0∞)
    {F : (ℕ → ℤ) → ℝ≥0∞} (hF : Measurable F) (k : ℕ) (z : ℤ) (c : ℝ≥0∞)
    (hbound : ∀ b, h b ≠ 0 → (∫⁻ x, F x ∂srwLaw m b) ≤ c) :
    (∫⁻ x, {x | vHitTime D x = k}.indicator
      (fun x => h (x k) * F (pathShift k x)) x ∂srwLaw m z) ≤
    (∫⁻ x, {x | vHitTime D x = k}.indicator (fun x => h (x k)) x
      ∂srwLaw m z) * c := by
  rw [lintegral_hitTime_eq m D h hF k z]
  have hg : Measurable ({x : ℕ → ℤ | vHitTime D x = k}.indicator
      (fun x => h (x k))) :=
    ((measurable_of_countable h).comp (measurable_pi_apply k)).indicator
      (measurableSet_vHitTime_eq D k)
  calc
    (∫⁻ x, {x | vHitTime D x = k}.indicator
        (fun x => h (x k) * ∫⁻ y, F y ∂srwLaw m (x k)) x ∂srwLaw m z) ≤
      ∫⁻ x, ({x | vHitTime D x = k}.indicator (fun x => h (x k)) x) * c
        ∂srwLaw m z := by
      apply lintegral_mono
      intro x
      dsimp only
      by_cases hx : x ∈ {x | vHitTime D x = k}
      · rw [indicator_of_mem hx, indicator_of_mem hx]
        by_cases hh : h (x k) = 0
        · simp [hh]
        · gcongr
          exact hbound (x k) hh
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    _ = _ := lintegral_mul_const c hg

/-- Summing the continuation bound over all finite hitting times yields the
restart estimate used in an annulus iteration. -/
theorem tsum_lintegral_hitTime_continuation_le
    (m : ℤ → ℤ → ℕ) (D : Set ℤ) (h : ℤ → ℝ≥0∞)
    {F : (ℕ → ℤ) → ℝ≥0∞} (hF : Measurable F) (z : ℤ) (c : ℝ≥0∞)
    (hbound : ∀ b, h b ≠ 0 → (∫⁻ x, F x ∂srwLaw m b) ≤ c) :
    (∑' k : ℕ, ∫⁻ x, {x | vHitTime D x = k}.indicator
      (fun x => h (x k) * F (pathShift k x)) x ∂srwLaw m z) ≤
    (∑' k : ℕ, ∫⁻ x, {x | vHitTime D x = k}.indicator
      (fun x => h (x k)) x ∂srwLaw m z) * c := by
  calc
    (∑' k : ℕ, ∫⁻ x, {x | vHitTime D x = k}.indicator
        (fun x => h (x k) * F (pathShift k x)) x ∂srwLaw m z) ≤
      ∑' k : ℕ, (∫⁻ x, {x | vHitTime D x = k}.indicator
        (fun x => h (x k)) x ∂srwLaw m z) * c :=
      ENNReal.tsum_le_tsum (fun k => lintegral_hitTime_continuation_le m D h hF k z c hbound)
    _ = _ := ENNReal.tsum_mul_right

/-- A continuation selected at a finite hitting time retains any uniform
bound valid at the selected restart vertices. -/
theorem tsum_lintegral_hitTime_indicator_continuation_le
    (m : ℤ → ℤ → ℕ) (D B : Set ℤ)
    {F : (ℕ → ℤ) → ℝ≥0∞} (hF : Measurable F) (z : ℤ) (c : ℝ≥0∞)
    (hbound : ∀ b ∈ B, (∫⁻ x, F x ∂srwLaw m b) ≤ c) :
    (∑' k : ℕ, ∫⁻ x, {x | vHitTime D x = k}.indicator
      (fun x => B.indicator 1 (x k) * F (pathShift k x)) x ∂srwLaw m z) ≤ c := by
  classical
  have hmeas : ∀ k : ℕ, MeasurableSet {x : ℕ → ℤ | vHitTime D x = k ∧ x k ∈ B} :=
    fun k => (measurableSet_vHitTime_eq D k).inter
      ((Set.to_countable B).measurableSet.preimage (measurable_pi_apply k))
  have hsum : (∑' k : ℕ, ∫⁻ x, {x | vHitTime D x = k}.indicator
      (fun x => B.indicator 1 (x k)) x ∂srwLaw m z) ≤ 1 := by
    calc
      _ = ∑' k : ℕ, srwLaw m z {x | vHitTime D x = k ∧ x k ∈ B} := by
        apply tsum_congr
        intro k
        have heq : (fun x : ℕ → ℤ => {x | vHitTime D x = k}.indicator
            (fun x => B.indicator (1 : ℤ → ℝ≥0∞) (x k)) x) =
            {x : ℕ → ℤ | vHitTime D x = k ∧ x k ∈ B}.indicator 1 := by
          funext x
          by_cases h₁ : vHitTime D x = k <;> by_cases h₂ : x k ∈ B <;>
            simp [h₁, h₂, Set.indicator]
        rw [heq, lintegral_indicator_one (hmeas k)]
      _ = srwLaw m z (⋃ k : ℕ, {x | vHitTime D x = k ∧ x k ∈ B}) := by
        rw [measure_iUnion ?_ hmeas]
        intro i j hij
        exact Set.disjoint_left.2 fun x hi hj => hij (by
          have h := hi.1.symm.trans hj.1
          exact_mod_cast h)
      _ ≤ 1 := by
        calc
          _ ≤ srwLaw m z Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
  have hc := tsum_lintegral_hitTime_continuation_le m D (B.indicator 1) hF z c
    (fun b hb => hbound b (by simpa [Set.indicator] using hb))
  exact hc.trans (by calc
    _ ≤ 1 * c := by gcongr
    _ = c := one_mul c)

end MatedCRT
