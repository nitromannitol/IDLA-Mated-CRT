import MatedCRT.Proofs.Sec6.ConstantOrderLowerBoundDiv.Visit
import MatedCRT.Proofs.IDLA.Measurable

/-!
# The expected exit time as a sum of the Green function

For simple random walk on a multigraph `m` on `ℤ` and `A ⊆ ℤ`, the exit time `τ_A` of a path equals the number of
its visits to `A` before `τ_A` (`vExitTime_eq_visitCount`). Taking expectations,
`E^a[τ_A] = ∑_{b ∈ A} E^a[#visits to b before τ_A]` (`expectedExitTime_eq_tsum_lintegral_visitsBeforeExit`), and,
when `E^a[τ_A] < ∞`, `E^a[τ_A] = ∑_{b ∈ A} G_A(a, b)` (`expectedExitTime_eq_tsum_greenFn`) and
`E^a[τ_A] = ∑_{b ∈ A} deg(b) g_A(a, b)` when every vertex of `A` has positive degree
(`expectedExitTime_eq_tsum_mdeg_mul_greenKernel`).

This is the identity `E[τ_B] = ∑_{y ∈ B} Gr_B(x, y)` of Berestycki-Gwynne (arXiv:2003.10320), Section 5.4, through
which their Lemma 5.8 (a bound on `∑_y Gr^ε_D(x, y)`) and Lemma 5.9 (moments of exit times) give Proposition 5.1.
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

namespace ExitTimeMoment

/-- The exit time `τ_A` of a path is the number of its visits to `A` before `τ_A`. -/
theorem vExitTime_eq_visitCount (A : Set ℤ) (x : ℕ → ℤ) :
    ((vExitTime A x : ℕ∞) : ℝ≥0∞) = ConstantOrderDiv.visitCount A A x := by
  refine le_antisymm ?_ (ConstantOrderDiv.visitCount_le A A x)
  have hmem : ∀ n : ℕ, (n : ℕ∞) < vExitTime A x → x n ∈ A := fun n hn =>
    (natCast_lt_vExitTime_iff.mp hn) n le_rfl
  by_cases htop : vExitTime A x = ⊤
  · have hlt : ∀ n : ℕ, (n : ℕ∞) < vExitTime A x := fun n => by
      rw [htop]; exact ENat.natCast_lt_top n
    rw [htop, ENat.toENNReal_top]
    unfold ConstantOrderDiv.visitCount
    calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, (1 : ℝ≥0∞) := (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun n => by
          split_ifs with h
          · exact le_rfl
          · exact absurd ⟨hlt n, hmem n (hlt n)⟩ h
  · obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp htop
    have hτ : ((vExitTime A x : ℕ∞) : ℝ≥0∞) = t := by rw [← ht, ENat.toENNReal_coe]
    rw [hτ]
    unfold ConstantOrderDiv.visitCount
    refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.range t))
    refine le_trans (le_of_eq (by simp : (t : ℝ≥0∞) = ∑ _j ∈ Finset.range t, (1 : ℝ≥0∞))) ?_
    refine Finset.sum_le_sum fun j hj => ?_
    have hjt : (j : ℕ∞) < vExitTime A x := by
      rw [← ht]; exact_mod_cast Finset.mem_range.mp hj
    split_ifs with h
    · exact le_rfl
    · exact absurd ⟨hjt, hmem j hjt⟩ h

/-- `E^a[τ_A] = ∑_{b ∈ A} E^a[#visits to b before τ_A]`. -/
theorem expectedExitTime_eq_tsum_lintegral_visitsBeforeExit (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) :
    expectedExitTime m A a = ∑' b : A, ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a := by
  rw [← lintegral_tsum fun b : A => (ConstantOrderDiv.measurable_visitsBeforeExit A b).aemeasurable]
  unfold expectedExitTime
  exact lintegral_congr fun x =>
    (vExitTime_eq_visitCount A x).trans (ConstantOrderDiv.tsum_visitsBeforeExit A A x).symm

/-- Each expected number of visits before `τ_A` is at most `E^a[τ_A]`. -/
theorem lintegral_visitsBeforeExit_le_expectedExitTime (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ) (b : A) :
    ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a ≤ expectedExitTime m A a := by
  rw [expectedExitTime_eq_tsum_lintegral_visitsBeforeExit]
  exact ENNReal.le_tsum (f := fun b' : A => ∫⁻ x, visitsBeforeExit A b' x ∂srwLaw m a) b

/-- **Green-function form of the expected exit time**: if `E^a[τ_A] < ∞`, then `E^a[τ_A] = ∑_{b ∈ A} G_A(a, b)`. -/
theorem expectedExitTime_eq_tsum_greenFn (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ)
    (hfin : expectedExitTime m A a ≠ ⊤) :
    expectedExitTime m A a = ∑' b : A, ENNReal.ofReal (greenFn m A a b) := by
  have hle := lintegral_visitsBeforeExit_le_expectedExitTime m A a
  conv_lhs => rw [expectedExitTime_eq_tsum_lintegral_visitsBeforeExit]
  refine tsum_congr fun b => ?_
  unfold greenFn
  rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top hfin (hle b))]

/-- **Green-kernel form of the expected exit time**: if `E^a[τ_A] < ∞` and every vertex of `A` has positive degree,
then `E^a[τ_A] = ∑_{b ∈ A} deg(b) g_A(a, b)`. -/
theorem expectedExitTime_eq_tsum_mdeg_mul_greenKernel (m : ℤ → ℤ → ℕ) (A : Set ℤ) (a : ℤ)
    (hfin : expectedExitTime m A a ≠ ⊤) (hdeg : ∀ b ∈ A, 0 < mdeg m b) :
    expectedExitTime m A a = ∑' b : A, ENNReal.ofReal ((mdeg m b : ℝ) * greenKernel m A a b) := by
  rw [expectedExitTime_eq_tsum_greenFn m A a hfin]
  refine tsum_congr fun b => ?_
  have hd : (mdeg m b : ℝ) ≠ 0 := by exact_mod_cast (hdeg b b.2).ne'
  unfold greenKernel
  rw [mul_div_cancel₀ _ hd]

end ExitTimeMoment

end MatedCRT
