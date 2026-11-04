import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationTail
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit

/-! Counting visits to each vertex before a finite exit. -/

namespace MatedCRT

open scoped ENNReal

/-- When the exit time is finite, the visit count is the finite sum of the
indicators at times before exit. -/
theorem visitsBeforeExit_eq_sum_of_finite (A : Set ℤ) (b : ℤ) (x : ℕ → ℤ)
    (hτ : vExitTime A x ≠ ⊤) :
    visitsBeforeExit A b x =
      ∑ n ∈ Finset.range (vExitTime A x).toNat, (if x n = b then (1 : ℝ≥0∞) else 0) := by
  classical
  have hτ' : vExitTime A x = ((vExitTime A x).toNat : ℕ∞) :=
    (ENat.natCast_toNat hτ).symm
  unfold visitsBeforeExit
  rw [tsum_eq_sum (s := Finset.range (vExitTime A x).toNat)]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnτ : (n : ℕ∞) < vExitTime A x := by
      rw [hτ']
      exact Nat.cast_lt.mpr (Finset.mem_range.mp hn)
    simp [hnτ]
  · intro n hn
    have hnτ : ¬ (n : ℕ∞) < vExitTime A x := by
      rw [hτ']
      have hle : (vExitTime A x).toNat ≤ n := by
        simpa only [Finset.mem_range, not_lt] using hn
      exact not_lt.mpr (Nat.cast_le.mpr hle)
    simp [hnτ]

/-- Summing the visit counts against a test function equals the path
occupation sum whenever the finite set contains all visited vertices. -/
theorem sum_visitCounts_mul_eq_occupation (B : Finset ℤ) (x : ℕ → ℤ)
    (g : ℤ → ℝ) (k : ℕ) (hB : ∀ n < k, x n ∈ B) :
    (∑ b ∈ B, (∑ n ∈ Finset.range k, if x n = b then (1 : ℝ) else 0) * g b) =
      ∑ n ∈ Finset.range k, g (x n) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_eq_single (x n)]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · intro hnot
    exact (hnot (hB n (Finset.mem_range.mp hn))).elim

/-- On a finite killed domain, weighted visit counts sum to the occupation
along the path up to its finite exit time. -/
theorem sum_visitsBeforeExit_mul_eq_occupation (A : Set ℤ) (B : Finset ℤ)
    (hAB : A ⊆ B) (x : ℕ → ℤ) (g : ℤ → ℝ)
    (hτ : vExitTime A x ≠ ⊤) :
    (∑ b ∈ B, (visitsBeforeExit A b x).toReal * g b) =
      ∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n) := by
  classical
  have hτ' : vExitTime A x = ((vExitTime A x).toNat : ℕ∞) :=
    (ENat.natCast_toNat hτ).symm
  rw [← sum_visitCounts_mul_eq_occupation B x g _]
  · apply Finset.sum_congr rfl
    intro b hb
    congr 1
    rw [visitsBeforeExit_eq_sum_of_finite A b x hτ, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    · intro n hn
      split_ifs <;> simp
  · intro n hn
    apply hAB
    apply mem_of_lt_vExitTime
    rw [hτ']
    exact Nat.cast_lt.mpr hn

/-- The Green function is the expected real visit count when the walk exits
in finite time almost surely. -/
theorem greenFn_eq_integral_visits (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ)
    (hfinite : ∀ᵐ x ∂srwLaw m a, vExitTime A x ≠ ⊤) :
    greenFn m A a b = ∫ x, (visitsBeforeExit A b x).toReal ∂srwLaw m a := by
  unfold greenFn
  symm
  apply MeasureTheory.integral_toReal
    (ConstantOrderDiv.measurable_visitsBeforeExit A b).aemeasurable
  filter_upwards [hfinite] with x hx
  rw [visitsBeforeExit_eq_sum_of_finite A b x hx]
  apply ENNReal.sum_lt_top.2
  intro n hn
  split_ifs <;> simp

/-- For a finite killed domain, the weighted Green sum is the expected
occupation up to exit, provided the visit counts are integrable. -/
theorem sum_greenFn_mul_eq_integral_occupation (m : ℤ → ℤ → ℕ)
    (A : Set ℤ) (B : Finset ℤ) (hAB : A ⊆ B) (a : ℤ) (g : ℤ → ℝ)
    (hfinite : ∀ᵐ x ∂srwLaw m a, vExitTime A x ≠ ⊤)
    (hvisit : ∀ b ∈ B, MeasureTheory.Integrable
      (fun x => (visitsBeforeExit A b x).toReal) (srwLaw m a)) :
    (∑ b ∈ B, greenFn m A a b * g b) =
      ∫ x, ∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n) ∂srwLaw m a := by
  calc
    _ = ∑ b ∈ B, ∫ x, (visitsBeforeExit A b x).toReal * g b ∂srwLaw m a := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [greenFn_eq_integral_visits m A a b hfinite, MeasureTheory.integral_mul_const]
    _ = ∫ x, ∑ b ∈ B, (visitsBeforeExit A b x).toReal * g b ∂srwLaw m a := by
      symm
      apply MeasureTheory.integral_finsetSum
      intro b hb
      exact (hvisit b hb).mul_const (g b)
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hfinite] with x hx
      exact sum_visitsBeforeExit_mul_eq_occupation A B hAB x g hx

/-- A finite expected exit time makes every visit count integrable. -/
theorem integrable_visitsBeforeExit_of_expectedExitTime_ne_top
    (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a b : ℤ)
    (hmean : expectedExitTime m A a ≠ ⊤) :
    MeasureTheory.Integrable (fun x => (visitsBeforeExit A b x).toReal) (srwLaw m a) := by
  apply MeasureTheory.integrable_toReal_of_lintegral_ne_top
    (ConstantOrderDiv.measurable_visitsBeforeExit A b).aemeasurable
  apply ne_of_lt
  calc
    (∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a) ≤ expectedExitTime m A a := by
      apply MeasureTheory.lintegral_mono
      intro x
      have h := ConstantOrderDiv.visitCount_le A {b} x
      simpa [ConstantOrderDiv.visitCount, visitsBeforeExit] using h
    _ < ⊤ := lt_top_iff_ne_top.mpr hmean

/-- A finite expected exit time implies almost-sure finite exit. -/
theorem ae_vExitTime_ne_top_of_expectedExitTime_ne_top
    (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ)
    (hmean : expectedExitTime m A a ≠ ⊤) :
    ∀ᵐ x ∂srwLaw m a, vExitTime A x ≠ ⊤ := by
  have hmeas : Measurable (fun x : ℕ → ℤ => (vExitTime A x : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_vExitTime A)
  have hae := MeasureTheory.ae_lt_top hmeas hmean
  filter_upwards [hae] with x hx
  intro heq
  simp [heq] at hx

/-- On a finite killed domain, finite expected exit time identifies the
weighted Green sum with the expected walk occupation. -/
theorem sum_greenFn_mul_eq_integral_occupation_of_expectedExitTime_ne_top
    (m : ℤ → ℤ → ℕ) (A : Set ℤ) (B : Finset ℤ) (hAB : A ⊆ B)
    (a : ℤ) (g : ℤ → ℝ) (hmean : expectedExitTime m A a ≠ ⊤) :
    (∑ b ∈ B, greenFn m A a b * g b) =
      ∫ x, ∑ n ∈ Finset.range (vExitTime A x).toNat, g (x n) ∂srwLaw m a :=
  sum_greenFn_mul_eq_integral_occupation m A B hAB a g
    (ae_vExitTime_ne_top_of_expectedExitTime_ne_top m A a hmean)
    (fun b _ => integrable_visitsBeforeExit_of_expectedExitTime_ne_top m A a b hmean)

end MatedCRT
