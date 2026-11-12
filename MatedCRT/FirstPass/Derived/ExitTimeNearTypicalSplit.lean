import MatedCRT.FirstPass.Derived.ExpectedExitGreenSum
import MatedCRT.FirstPass.S5e.SecondGreenDet
import MatedCRT.Audit.StatementsSec3Sec5M1
import MatedCRT.Proofs.Sec5.LLowerBound.GreenMonotonicity

/-!
# Exit times from a near/typical split of the Green sum (BG20 Lemma 5.8, deterministic core)

Berestycki-Gwynne (arXiv:2003.10320), proof of Lemma 5.8, equations (5.39)-(5.45). Let `A ⊆ B` be finite
vertex sets of a locally finite multigraph on `ℤ` whose consecutive vertices are adjacent, and let `a ∈ ℤ`.
By the Green-function form of the expected exit time, `E^a[τ_A] = ∑_{b ∈ A} G_A(a, b)`, and by the
monotonicity of the Green function in the domain (5.39), `G_A(a, b) ≤ G_B(a, b)`. Split `A` into a *near*
part `A ∩ Y` and a *typical* part `A \ Y`. If the near part has at most `K` vertices and `G_B(a, ·) ≤ M`
on it (BG20 (5.40)-(5.42)), and `G_B(a, b) ≤ deg(b) f(b)` on the typical part (BG20 (5.43)-(5.44), with
`G = deg · g`), then `E^a[τ_A] ≤ K M + ∑_{b ∈ A} deg(b) f(b)`.

The bound of the degree-weighted sum `∑_{b ∈ A} deg(b) f(b)` by an integral against the LQG area measure
(BG20 Lemma A.5, the last step of (5.45)) is not part of this file.

## Main statements
* `ExitTimeMoment.expectedExitTime_le_near_typical`: the bound above, with `G_B(a, b) ≤ deg(b) f(b)`.
* `ExitTimeMoment.expectedExitTime_le_near_typical_greenKernel`: the same with `g_B(a, b) ≤ f(b)` on the
  typical part, for vertices of `A` of positive degree.
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal

namespace ExitTimeMoment

/-- Sum form of the expected exit time of a finite set: `E^a[τ_A] = ∑_{b ∈ A} G_A(a, b)` as a finite sum of
real numbers. -/
theorem expectedExitTime_eq_ofReal_sum_greenFn {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ} (hA : A.Finite) (a : ℤ) :
    expectedExitTime m A a = ENNReal.ofReal (∑ b ∈ hA.toFinset, greenFn m A a b) := by
  rw [expectedExitTime_eq_tsum_greenFn m A a (Audit.StatementsSec3Sec5M1.finite_expectedExitTime hlf hcons hA a),
    ENNReal.ofReal_sum_of_nonneg (fun b _ => greenFn_nonnegative m A a b)]
  rw [tsum_subtype A (fun b => ENNReal.ofReal (greenFn m A a b))]
  rw [tsum_eq_sum (s := hA.toFinset)]
  · refine Finset.sum_congr rfl fun b hb => ?_
    exact indicator_of_mem (hA.mem_toFinset.1 hb) _
  · intro b hb
    exact indicator_of_notMem (fun h => hb (hA.mem_toFinset.2 h)) _

/-- **Near/typical split of the exit time** (BG20, proof of Lemma 5.8, (5.39)-(5.45)). Let `A ⊆ B` be finite,
let `Y` be a set of vertices (the near part), and suppose every finite subset of `A ∩ Y` has at most `K`
elements, `G_B(a, b) ≤ M` for `b ∈ A ∩ Y` (with `0 ≤ M`), and `G_B(a, b) ≤ deg(b) f(b)` for `b ∈ A \ Y`,
where `f ≥ 0` on `A`. Then `E^a[τ_A] ≤ K M + ∑_{b ∈ A} deg(b) f(b)`. -/
theorem expectedExitTime_le_near_typical {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A B : Set ℤ} (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B)
    (a : ℤ) (Y : Set ℤ) {K M : ℝ} (hY : ∀ s : Finset ℤ, (s : Set ℤ) ⊆ A ∩ Y → (s.card : ℝ) ≤ K)
    (hM0 : 0 ≤ M) (hM : ∀ b ∈ A ∩ Y, greenFn m B a b ≤ M) (f : ℤ → ℝ) (hf0 : ∀ b ∈ A, 0 ≤ f b)
    (hf : ∀ b ∈ A, b ∉ Y → greenFn m B a b ≤ (mdeg m b : ℝ) * f b) :
    expectedExitTime m A a ≤ ENNReal.ofReal (K * M + ∑ b ∈ hA.toFinset, (mdeg m b : ℝ) * f b) := by
  classical
  rw [expectedExitTime_eq_ofReal_sum_greenFn hlf hcons hA a]
  refine ENNReal.ofReal_le_ofReal ?_
  set s := hA.toFinset with hs
  have hmono : ∀ b, greenFn m A a b ≤ greenFn m B a b := fun b =>
    S5e.greenFn_mono_of_domain hlf hcons hA hB hAB a b
  have hnear : ∑ b ∈ s.filter (· ∈ Y), greenFn m B a b ≤ K * M := by
    have hcard : ((s.filter (· ∈ Y)).card : ℝ) ≤ K := by
      refine hY _ fun b hb => ?_
      rw [Finset.coe_filter] at hb
      exact ⟨hA.mem_toFinset.1 hb.1, hb.2⟩
    calc ∑ b ∈ s.filter (· ∈ Y), greenFn m B a b
        ≤ ∑ _b ∈ s.filter (· ∈ Y), M := by
          refine Finset.sum_le_sum fun b hb => ?_
          rw [Finset.mem_filter] at hb
          exact hM b ⟨hA.mem_toFinset.1 hb.1, hb.2⟩
      _ = ((s.filter (· ∈ Y)).card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * M := mul_le_mul_of_nonneg_right hcard hM0
  have htyp : ∑ b ∈ s.filter (· ∉ Y), greenFn m B a b ≤ ∑ b ∈ s, (mdeg m b : ℝ) * f b := by
    calc ∑ b ∈ s.filter (· ∉ Y), greenFn m B a b
        ≤ ∑ b ∈ s.filter (· ∉ Y), (mdeg m b : ℝ) * f b := by
          refine Finset.sum_le_sum fun b hb => ?_
          rw [Finset.mem_filter] at hb
          exact hf b (hA.mem_toFinset.1 hb.1) hb.2
      _ ≤ ∑ b ∈ s, (mdeg m b : ℝ) * f b := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun b hb _ => ?_
          exact mul_nonneg (Nat.cast_nonneg _) (hf0 b (hA.mem_toFinset.1 hb))
  calc ∑ b ∈ s, greenFn m A a b ≤ ∑ b ∈ s, greenFn m B a b := Finset.sum_le_sum fun b _ => hmono b
    _ = ∑ b ∈ s.filter (· ∈ Y), greenFn m B a b + ∑ b ∈ s.filter (· ∉ Y), greenFn m B a b :=
        (Finset.sum_filter_add_sum_filter_not s (· ∈ Y) _).symm
    _ ≤ K * M + ∑ b ∈ s, (mdeg m b : ℝ) * f b := add_le_add hnear htyp

/-- **Near/typical split, Green-kernel form** (BG20 (5.44)): as `expectedExitTime_le_near_typical`, with the
typical bound `g_B(a, b) ≤ f(b)` on the Green kernel `g = G / deg`, for a domain `A` whose vertices have positive
degree. -/
theorem expectedExitTime_le_near_typical_greenKernel {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A B : Set ℤ} (hA : A.Finite) (hB : B.Finite) (hAB : A ⊆ B)
    (a : ℤ) (Y : Set ℤ) {K M : ℝ} (hY : ∀ s : Finset ℤ, (s : Set ℤ) ⊆ A ∩ Y → (s.card : ℝ) ≤ K)
    (hM0 : 0 ≤ M) (hM : ∀ b ∈ A ∩ Y, greenFn m B a b ≤ M) (hdeg : ∀ b ∈ A, 0 < mdeg m b)
    (f : ℤ → ℝ) (hf0 : ∀ b ∈ A, 0 ≤ f b) (hf : ∀ b ∈ A, b ∉ Y → greenKernel m B a b ≤ f b) :
    expectedExitTime m A a ≤ ENNReal.ofReal (K * M + ∑ b ∈ hA.toFinset, (mdeg m b : ℝ) * f b) := by
  refine expectedExitTime_le_near_typical hlf hcons hA hB hAB a Y hY hM0 hM f hf0 fun b hb hbY => ?_
  have hd : (0 : ℝ) < mdeg m b := Nat.cast_pos.2 (hdeg b hb)
  have h := hf b hb hbY
  unfold greenKernel at h
  rw [div_le_iff₀ hd] at h
  linarith

end ExitTimeMoment

end MatedCRT
