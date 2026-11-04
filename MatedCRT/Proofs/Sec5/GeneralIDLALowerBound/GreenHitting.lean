import MatedCRT.Steps.Sec5.GeneralIDLALowerBound
import MatedCRT.Proofs.IDLA.StrongMarkov
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Lemma 5.2: `G_O(z, a) = P^z[τ_a < T_O] G_O(a, a)` (eq:markov-chain-renewal, line 2176; LL10 Lemma 4.6.1)

With `D = {a} ∪ Oᶜ`, the visits to `a` before exiting `O` are, pathwise, `1{X_{τ_D} = a} · (visits of θ_{τ_D} X)`
(`visitsBeforeExit_eq_tsum_hit`); the strong Markov property at `τ_D` (`lintegral_hitTime_eq`) gives
`E^z[visits] = P^z[τ_D < ∞, X_{τ_D} = a] E^a[visits]`, and `{τ_D < ∞, X_{τ_D} = a} = {τ_a < T_O}` for `a ∈ O`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem measurable_visitsBeforeExit (O : Set ℤ) (a : ℤ) : Measurable (visitsBeforeExit O a) := by
  unfold visitsBeforeExit
  refine Measurable.tsum fun n => Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_natCast_lt_vExitTime O n).inter (measurableSet_coord n {a})

/-- Pathwise decomposition of the visits to `a` before exiting `O` at the hitting time of `D = {a} ∪ Oᶜ`. -/
theorem visitsBeforeExit_eq_tsum_hit {O : Set ℤ} {a : ℤ} (ha : a ∈ O) (x : ℕ → ℤ) :
    visitsBeforeExit O a x = ∑' k : ℕ, {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k}.indicator
      (fun x => ({a} : Set ℤ).indicator 1 (x k) * visitsBeforeExit O a (pathShift k x)) x := by
  set D : Set ℤ := {a} ∪ Oᶜ with hD
  induction hτ : vHitTime D x using ENat.recTopCoe with
  | top =>
    have hall : ∀ n, x n ∈ Dᶜ := vExitTime_eq_top_iff.1 hτ
    have hzero : ∀ k : ℕ, x ∉ {x : ℕ → ℤ | vHitTime D x = k} := fun k h => by
      simp only [mem_ofPred_eq, hτ] at h
      exact ENat.natCast_ne_top k h.symm
    rw [ENNReal.tsum_eq_zero.2 fun k => indicator_of_notMem (hzero k) _]
    unfold visitsBeforeExit
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    have hn : x n ≠ a := fun h => hall n (by rw [h]; exact Or.inl rfl)
    simp [hn]
  | coe k =>
    have hpre : ∀ j < k, x j ∈ Dᶜ := fun j hj => mem_of_lt_vExitTime (by
      show (j : ℕ∞) < vHitTime D x
      rw [hτ]
      exact_mod_cast hj)
    have hk : x k ∈ D := by simpa using apply_vExitTime_not_mem (A := Dᶜ) hτ
    rw [tsum_eq_single k fun j hj => indicator_of_notMem (fun h => hj (by
      simp only [mem_ofPred_eq, hτ] at h
      exact_mod_cast h.symm)) _]
    rw [indicator_of_mem (show x ∈ {x : ℕ → ℤ | vHitTime D x = k} from hτ)]
    show visitsBeforeExit O a x = ({a} : Set ℤ).indicator 1 (x k) * visitsBeforeExit O a (pathShift k x)
    have hne : ∀ j < k, x j ≠ a := fun j hj h => hpre j hj (by rw [h]; exact Or.inl rfl)
    have hO : ∀ j < k, x j ∈ O := fun j hj => by
      have := hpre j hj
      simp only [hD, compl_union, mem_inter_iff, mem_compl_iff, not_not] at this
      exact this.2
    by_cases hxk : x k = a
    · rw [hxk, indicator_of_mem (mem_singleton a), Pi.one_apply, one_mul]
      have hkO : ∀ j ≤ k, x j ∈ O := fun j hj => by
        rcases hj.lt_or_eq with h | h
        · exact hO j h
        · rw [h, hxk]; exact ha
      unfold visitsBeforeExit
      have hsupp : Function.support (fun n : ℕ => if (n : ℕ∞) < vExitTime O x ∧ x n = a then (1 : ℝ≥0∞) else 0) ⊆
          Set.range (fun m : ℕ => m + k) := by
        intro n hn
        have hn' : (n : ℕ∞) < vExitTime O x ∧ x n = a := by
          by_contra h
          exact hn (ite_eq_right h)
        have hkn : k ≤ n := by
          by_contra h
          exact hne n (by omega) hn'.2
        exact ⟨n - k, Nat.sub_add_cancel hkn⟩
      rw [← (add_left_injective k).tsum_eq hsupp]
      refine tsum_congr fun m => ?_
      have h1 := lt_vExitTime_add_iff hkO m
      by_cases hm : ((m + k : ℕ) : ℕ∞) < vExitTime O x ∧ x (m + k) = a
      · rw [ite_eq_left hm, ite_eq_left ⟨h1.1 hm.1, hm.2⟩]
      · rw [ite_eq_right hm, ite_eq_right]
        rintro ⟨h2, h3⟩
        exact hm ⟨h1.2 h2, h3⟩
    · have hkO : x k ∉ O := by
        rcases hk with h | h
        · exact absurd h hxk
        · exact h
      have hT : ¬ (k : ℕ∞) < vExitTime O x := fun h => hkO (mem_of_lt_vExitTime h)
      rw [indicator_of_notMem (show x k ∉ ({a} : Set ℤ) from hxk), zero_mul]
      unfold visitsBeforeExit
      refine ENNReal.tsum_eq_zero.2 fun n => ?_
      rw [ite_eq_right]
      rintro ⟨h2, h3⟩
      by_cases hnk : n < k
      · exact hne n hnk h3
      · exact hT (lt_of_le_of_lt (by exact_mod_cast not_lt.1 hnk) h2)

/-- `⋃_k {τ_D = k, X_k = a} = {τ_a < T_O}` for `D = {a} ∪ Oᶜ` and `a ∈ O`. -/
theorem iUnion_hit_eq {O : Set ℤ} {a : ℤ} (ha : a ∈ O) :
    (⋃ k : ℕ, {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k ∧ x k = a}) =
      {x : ℕ → ℤ | vHitTime {a} x < vExitTime O x} := by
  ext x
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨k, hτ, hxk⟩
    have hpre : ∀ j < k, x j ∈ ({a} ∪ Oᶜ)ᶜ := fun j hj =>
      mem_of_lt_vExitTime (by rw [show vExitTime ({a} ∪ Oᶜ)ᶜ x = k from hτ]; exact_mod_cast hj)
    have hτa : vHitTime {a} x = k := by
      unfold vHitTime
      rw [vExitTime_eq_natCast_iff]
      refine ⟨fun h => ?_, fun j hj => ?_⟩
      · have := mem_of_lt_vExitTime h
        simp [hxk] at this
      · have := hpre j hj
        simp only [compl_union, mem_inter_iff, mem_compl_iff] at this
        exact this.1
    rw [hτa, natCast_lt_vExitTime_iff]
    intro j hj
    rcases hj.lt_or_eq with h | h
    · have := hpre j h
      simp only [compl_union, mem_inter_iff, mem_compl_iff, not_not] at this
      exact this.2
    · rw [h, hxk]; exact ha
  · intro h
    have hne : vHitTime {a} x ≠ ⊤ := ne_top_of_lt h
    set k := (vHitTime {a} x).toNat with hk
    have hτa : vHitTime {a} x = k := (ENat.natCast_toNat hne).symm
    have hxk : x k = a := apply_vHitTime_eq hτa
    have hkT : (k : ℕ∞) < vExitTime O x := by rw [← hτa]; exact h
    refine ⟨k, ?_, hxk⟩
    unfold vHitTime
    rw [vExitTime_eq_natCast_iff]
    refine ⟨fun h' => ?_, fun j hj => ?_⟩
    · have := mem_of_lt_vExitTime h'
      simp [hxk] at this
    · have h1 : x j ∈ ({a} : Set ℤ)ᶜ := mem_of_lt_vExitTime (by
        rw [show vExitTime ({a} : Set ℤ)ᶜ x = k from hτa]; exact_mod_cast hj)
      have h2 : x j ∈ O := (natCast_lt_vExitTime_iff.1 hkT) j hj.le
      simp only [compl_union, mem_inter_iff, mem_compl_iff, not_not]
      exact ⟨h1, h2⟩

/-- **Step** `GreenHittingStep` (LL10 Lemma 4.6.1). -/
theorem greenHittingStep : GreenHittingStep := by
  intro m O a z
  by_cases ha : a ∉ O
  · -- no visits to `a ∉ O` before exiting `O`
    have h0 : ∀ x, visitsBeforeExit O a x = 0 := by
      intro x
      unfold visitsBeforeExit
      refine ENNReal.tsum_eq_zero.2 fun n => ?_
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      exact ha (h2 ▸ mem_of_lt_vExitTime h1)
    simp [greenFn, h0]
  · rw [not_not] at ha
    have hF := measurable_visitsBeforeExit O a
    have hmeas : ∀ k : ℕ, Measurable ({x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k}.indicator
        (fun x => ({a} : Set ℤ).indicator 1 (x k) * visitsBeforeExit O a (pathShift k x))) := fun k =>
      Measurable.indicator
        (((measurable_of_countable (({a} : Set ℤ).indicator (1 : ℤ → ℝ≥0∞))).comp
          (measurable_pi_apply k)).mul (hF.comp (measurable_pathShift k)))
        (measurableSet_vHitTime_eq ({a} ∪ Oᶜ) k)
    have hEk : ∀ k : ℕ, MeasurableSet {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k ∧ x k = a} := fun k =>
      (measurableSet_vHitTime_eq _ k).inter (measurableSet_coord k {a})
    have hkey : ∫⁻ x, visitsBeforeExit O a x ∂srwLaw m z =
        srwLaw m z {x | vHitTime {a} x < vExitTime O x} * ∫⁻ y, visitsBeforeExit O a y ∂srwLaw m a := by
      calc ∫⁻ x, visitsBeforeExit O a x ∂srwLaw m z
          = ∫⁻ x, ∑' k : ℕ, {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k}.indicator
              (fun x => ({a} : Set ℤ).indicator 1 (x k) * visitsBeforeExit O a (pathShift k x)) x
              ∂srwLaw m z :=
            lintegral_congr fun x => visitsBeforeExit_eq_tsum_hit ha x
        _ = ∑' k : ℕ, ∫⁻ x, {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k}.indicator
              (fun x => ({a} : Set ℤ).indicator 1 (x k) * visitsBeforeExit O a (pathShift k x)) x
              ∂srwLaw m z :=
            lintegral_tsum fun k => (hmeas k).aemeasurable
        _ = ∑' k : ℕ, ∫⁻ x, {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k}.indicator
              (fun x => ({a} : Set ℤ).indicator 1 (x k) * ∫⁻ y, visitsBeforeExit O a y ∂srwLaw m (x k)) x
              ∂srwLaw m z :=
            tsum_congr fun k => lintegral_hitTime_eq m _ _ hF k z
        _ = ∑' k : ℕ, srwLaw m z {x | vHitTime ({a} ∪ Oᶜ) x = k ∧ x k = a} *
              ∫⁻ y, visitsBeforeExit O a y ∂srwLaw m a := by
            refine tsum_congr fun k => ?_
            have hpt : ∀ x, {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k}.indicator
                (fun x => ({a} : Set ℤ).indicator 1 (x k) * ∫⁻ y, visitsBeforeExit O a y ∂srwLaw m (x k)) x =
                {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k ∧ x k = a}.indicator
                  (fun _ => ∫⁻ y, visitsBeforeExit O a y ∂srwLaw m a) x := by
              intro x
              by_cases h1 : vHitTime ({a} ∪ Oᶜ) x = k
              · by_cases h2 : x k = a
                · rw [indicator_of_mem (show x ∈ {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k} from h1),
                    indicator_of_mem
                      (show x ∈ {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k ∧ x k = a} from ⟨h1, h2⟩)]
                  show ({a} : Set ℤ).indicator 1 (x k) * ∫⁻ y, visitsBeforeExit O a y ∂srwLaw m (x k) =
                    ∫⁻ y, visitsBeforeExit O a y ∂srwLaw m a
                  rw [h2, indicator_of_mem (mem_singleton a), Pi.one_apply, one_mul]
                · rw [indicator_of_mem (show x ∈ {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k} from h1),
                    indicator_of_notMem
                      (show x ∉ {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k ∧ x k = a} from fun h => h2 h.2)]
                  show ({a} : Set ℤ).indicator 1 (x k) * ∫⁻ y, visitsBeforeExit O a y ∂srwLaw m (x k) = 0
                  rw [indicator_of_notMem (show x k ∉ ({a} : Set ℤ) from h2), zero_mul]
              · rw [indicator_of_notMem (show x ∉ {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k} from h1),
                  indicator_of_notMem
                    (show x ∉ {x : ℕ → ℤ | vHitTime ({a} ∪ Oᶜ) x = k ∧ x k = a} from fun h => h1 h.1)]
            rw [lintegral_congr hpt, lintegral_indicator_const (hEk k), mul_comm]
        _ = (∑' k : ℕ, srwLaw m z {x | vHitTime ({a} ∪ Oᶜ) x = k ∧ x k = a}) *
              ∫⁻ y, visitsBeforeExit O a y ∂srwLaw m a := ENNReal.tsum_mul_right
        _ = srwLaw m z {x | vHitTime {a} x < vExitTime O x} * ∫⁻ y, visitsBeforeExit O a y ∂srwLaw m a := by
            rw [← measure_iUnion ?_ hEk, iUnion_hit_eq ha]
            intro i j hij
            exact Set.disjoint_left.2 fun x hi hj => hij (by
              have := hi.1.symm.trans hj.1
              exact_mod_cast this)
    unfold greenFn hitBeforeExitProb
    rw [hkey, ENNReal.toReal_mul]

end MatedCRT
