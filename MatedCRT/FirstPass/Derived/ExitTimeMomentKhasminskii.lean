import MatedCRT.Proofs.IDLA.Measurable
import MatedCRT.Proofs.Infra.RandomWalk
import MatedCRT.Proofs.WalkPotential.MarkovFixedTime

/-!
# Moments of exit times of simple random walk (Berestycki-Gwynne, Lemma 5.9)

For simple random walk on a multigraph `m` on `ℤ` and a set `A ⊆ ℤ`: if the expected exit time from `A` is at most
`M` from every starting point in `A`, then for every starting point `a` and every `N`,
`E^a[τ_A^N] ≤ N! M^N` (`exitTimeMoment_le_factorial_mul_pow`).

This is Berestycki-Gwynne (arXiv:2003.10320), Lemma 5.9, eq. (5.46), in the form used in the proof of their
Proposition 5.1: since `E^y[τ_A] = ∑_{y' ∈ A} Gr_A(y, y')`, bounding each factor of the product in (5.46) by the
supremum over the first point gives `E^a[τ_A^N] ≤ N! (sup_{y ∈ A} E^y[τ_A])^N` (Khasminskii's lemma).

The proof is by induction on `N`. Pointwise, `τ^{N+1} ≤ (N+1) ∑_{j < τ} (τ ∘ θ_j)^N`, where `θ_j` is the shift of the
path by `j` (`pow_vExitTime_le_tsum`; from the elementary inequality `t^{N+1} ≤ (N+1) ∑_{j < t} (t - j)^N` and
`τ ∘ θ_j ≥ τ - j` on `{j < τ}`). The Markov property at the fixed time `j` (`lintegral_srwLaw_markov`) turns the
`j`-th term into `E^a[1{j < τ} E^{x_j}[τ^N]]`, and `∑_j P^a(j < τ) ≤ E^a[τ]`.
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal
open WalkPotential

namespace ExitTimeMoment

/-- `(t + 1)^(N + 1) ≤ t^(N + 1) + (N + 1) (t + 1)^N`. -/
theorem succ_pow_succ_le (t N : ℕ) :
    (t + 1) ^ (N + 1) ≤ t ^ (N + 1) + (N + 1) * (t + 1) ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    have h2 : (t + 1) ^ n * t ≤ (t + 1) ^ (n + 1) := by
      rw [pow_succ]; exact Nat.mul_le_mul_left _ (Nat.le_succ t)
    calc (t + 1) ^ (n + 1 + 1) = (t + 1) ^ (n + 1) * t + (t + 1) ^ (n + 1) := by ring
      _ ≤ (t ^ (n + 1) + (n + 1) * (t + 1) ^ n) * t + (t + 1) ^ (n + 1) := by gcongr
      _ = t ^ (n + 1 + 1) + (n + 1) * ((t + 1) ^ n * t) + (t + 1) ^ (n + 1) := by ring
      _ ≤ t ^ (n + 1 + 1) + (n + 1) * (t + 1) ^ (n + 1) + (t + 1) ^ (n + 1) := by gcongr
      _ = t ^ (n + 1 + 1) + (n + 1 + 1) * (t + 1) ^ (n + 1) := by ring

/-- `t^(N + 1) ≤ (N + 1) ∑_{j < t} (t - j)^N`. -/
theorem pow_succ_le_sum (N t : ℕ) :
    t ^ (N + 1) ≤ (N + 1) * ∑ j ∈ Finset.range t, (t - j) ^ N := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ']
    have hs : ∑ j ∈ Finset.range t, (t + 1 - (j + 1)) ^ N = ∑ j ∈ Finset.range t, (t - j) ^ N :=
      Finset.sum_congr rfl fun j _ => by rw [Nat.add_sub_add_right]
    rw [hs, Nat.sub_zero, mul_add]
    exact (succ_pow_succ_le t N).trans (Nat.add_le_add_right ih _)

open Classical in
/-- The indicator that a history `(x_0, …, x_j)` stays in `A`. -/
noncomputable def stayIn (A : Set ℤ) (j : ℕ) (h : Fin (j + 1) → ℤ) : ℝ≥0∞ :=
  if ∀ i, h i ∈ A then 1 else 0

theorem measurable_stayIn (A : Set ℤ) (j : ℕ) : Measurable (stayIn A j) :=
  measurable_of_countable _

/-- The history `(x_0, …, x_j)` stays in `A` iff `j < τ_A`. -/
theorem stayIn_pathHist (A : Set ℤ) (j : ℕ) (x : ℕ → ℤ) :
    stayIn A j (pathHist j x) = if (j : ℕ∞) < vExitTime A x then 1 else 0 := by
  have key : (∀ i : Fin (j + 1), pathHist j x i ∈ A) ↔ (j : ℕ∞) < vExitTime A x := by
    rw [natCast_lt_vExitTime_iff]
    constructor
    · intro h i hi
      exact h ⟨i, Nat.lt_succ_of_le hi⟩
    · intro h i
      exact h i (Nat.le_of_lt_succ i.isLt)
  unfold stayIn
  by_cases hj : (j : ℕ∞) < vExitTime A x
  · rw [ite_eq_left (key.2 hj), ite_eq_left hj]
  · rw [ite_eq_right (fun h => hj (key.1 h)), ite_eq_right hj]

/-- If `j + k < τ_A(x)`, then `k < τ_A(θ_j x)`. -/
theorem lt_vExitTime_pathShift {A : Set ℤ} {x : ℕ → ℤ} {j k : ℕ}
    (h : ((j + k : ℕ) : ℕ∞) < vExitTime A x) : (k : ℕ∞) < vExitTime A (pathShift j x) := by
  rw [natCast_lt_vExitTime_iff] at h ⊢
  intro i hi
  exact h (j + i) (by omega)

/-- **Pointwise decomposition**: `τ^{N+1} ≤ (N+1) ∑_j 1{j < τ} (τ ∘ θ_j)^N`. -/
theorem pow_vExitTime_le_tsum (A : Set ℤ) (N : ℕ) (x : ℕ → ℤ) :
    ((vExitTime A x : ℕ∞) : ℝ≥0∞) ^ (N + 1) ≤
      ((N + 1 : ℕ) : ℝ≥0∞) * ∑' j : ℕ, stayIn A j (pathHist j x) *
        ((vExitTime A (pathShift j x) : ℕ∞) : ℝ≥0∞) ^ N := by
  by_cases htop : vExitTime A x = ⊤
  · have hterm : ∀ j : ℕ, (1 : ℝ≥0∞) ≤ stayIn A j (pathHist j x) *
        ((vExitTime A (pathShift j x) : ℕ∞) : ℝ≥0∞) ^ N := by
      intro j
      have hj : (j : ℕ∞) < vExitTime A x := by rw [htop]; exact ENat.natCast_lt_top j
      rw [stayIn_pathHist, ite_eq_left hj, one_mul]
      have h0 : ((0 : ℕ) : ℕ∞) < vExitTime A (pathShift j x) :=
        lt_vExitTime_pathShift (by rw [htop]; exact ENat.natCast_lt_top _)
      have h1 : (1 : ℕ∞) ≤ vExitTime A (pathShift j x) := by
        rw [Nat.cast_zero] at h0
        exact Order.one_le_iff_pos.mpr h0
      have h1' : (1 : ℝ≥0∞) ≤ ((vExitTime A (pathShift j x) : ℕ∞) : ℝ≥0∞) := by
        have := ENat.toENNReal_le.mpr h1
        rwa [ENat.toENNReal_one] at this
      exact one_le_pow₀ h1'
    have hsum : (⊤ : ℝ≥0∞) ≤ ((N + 1 : ℕ) : ℝ≥0∞) * ∑' j : ℕ, stayIn A j (pathHist j x) *
        ((vExitTime A (pathShift j x) : ℕ∞) : ℝ≥0∞) ^ N := by
      calc (⊤ : ℝ≥0∞) = ((N + 1 : ℕ) : ℝ≥0∞) * ∑' _ : ℕ, (1 : ℝ≥0∞) := by
            rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero,
              ENNReal.mul_top (by exact_mod_cast Nat.succ_ne_zero N)]
        _ ≤ _ := mul_le_mul' le_rfl (ENNReal.tsum_le_tsum hterm)
    exact le_top.trans hsum
  · obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← ht, ENat.toENNReal_coe]
    have hterm : ∀ j ∈ Finset.range t, ((t - j : ℕ) : ℝ≥0∞) ^ N ≤
        stayIn A j (pathHist j x) * ((vExitTime A (pathShift j x) : ℕ∞) : ℝ≥0∞) ^ N := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hjt : (j : ℕ∞) < vExitTime A x := by rw [← ht]; exact_mod_cast hj
      rw [stayIn_pathHist, ite_eq_left hjt, one_mul]
      have hk : ((t - j - 1 : ℕ) : ℕ∞) < vExitTime A (pathShift j x) :=
        lt_vExitTime_pathShift (by rw [← ht]; exact_mod_cast (by omega : j + (t - j - 1) < t))
      have hle : ((t - j : ℕ) : ℕ∞) ≤ vExitTime A (pathShift j x) := by
        have he : t - j = (t - j - 1) + 1 := by omega
        rw [he, Nat.cast_add, Nat.cast_one]
        exact Order.add_one_le_of_lt hk
      have hle' : ((t - j : ℕ) : ℝ≥0∞) ≤ ((vExitTime A (pathShift j x) : ℕ∞) : ℝ≥0∞) := by
        have := ENat.toENNReal_le.mpr hle
        rwa [ENat.toENNReal_coe] at this
      gcongr
    calc ((t : ℕ) : ℝ≥0∞) ^ (N + 1) = ((t ^ (N + 1) : ℕ) : ℝ≥0∞) := by push_cast; rfl
      _ ≤ (((N + 1) * ∑ j ∈ Finset.range t, (t - j) ^ N : ℕ) : ℝ≥0∞) :=
          Nat.cast_le.mpr (pow_succ_le_sum N t)
      _ = ((N + 1 : ℕ) : ℝ≥0∞) * ∑ j ∈ Finset.range t, ((t - j : ℕ) : ℝ≥0∞) ^ N := by
          rw [Nat.cast_mul, Nat.cast_sum]
          simp only [Nat.cast_pow]
      _ ≤ ((N + 1 : ℕ) : ℝ≥0∞) * ∑ j ∈ Finset.range t, stayIn A j (pathHist j x) *
            ((vExitTime A (pathShift j x) : ℕ∞) : ℝ≥0∞) ^ N := by
          gcongr with j hj
          exact hterm j hj
      _ ≤ _ := by
          gcongr
          exact ENNReal.sum_le_tsum _

/-- `∑_j 1{j < τ} ≤ τ`. -/
theorem tsum_stayIn_le (A : Set ℤ) (x : ℕ → ℤ) :
    ∑' j : ℕ, stayIn A j (pathHist j x) ≤ ((vExitTime A x : ℕ∞) : ℝ≥0∞) := by
  simp_rw [stayIn_pathHist]
  by_cases htop : vExitTime A x = ⊤
  · rw [htop, ENat.toENNReal_top]; exact le_top
  · obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← ht, ENat.toENNReal_coe]
    have hzero : ∀ j ∉ Finset.range t, (if (j : ℕ∞) < (t : ℕ∞) then (1 : ℝ≥0∞) else 0) = 0 := by
      intro j hj
      rw [Finset.mem_range, not_lt] at hj
      rw [ite_eq_right (by exact_mod_cast not_lt.mpr hj)]
    rw [tsum_eq_sum hzero]
    refine le_of_eq ?_
    calc ∑ j ∈ Finset.range t, (if (j : ℕ∞) < (t : ℕ∞) then (1 : ℝ≥0∞) else 0)
        = ∑ _j ∈ Finset.range t, (1 : ℝ≥0∞) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.mem_range] at hj
          rw [ite_eq_left (by exact_mod_cast hj)]
      _ = (t : ℝ≥0∞) := by simp

end ExitTimeMoment

open ExitTimeMoment in
/-- **Moments of exit times** (Berestycki-Gwynne, Lemma 5.9, Khasminskii form). For simple random walk on a
multigraph `m` and `A ⊆ ℤ`, if `E^y[τ_A] ≤ M` for every `y ∈ A`, then `E^a[τ_A^N] ≤ N! M^N` for every `a ∈ ℤ` and
every `N ∈ ℕ`. -/
theorem exitTimeMoment_le_factorial_mul_pow (m : ℤ → ℤ → ℕ) (A : Set ℤ) {M : ℝ≥0∞}
    (hM : ∀ y ∈ A, expectedExitTime m A y ≤ M) (N : ℕ) (a : ℤ) :
    exitTimeMoment m A a N ≤ (N.factorial : ℝ≥0∞) * M ^ N := by
  have hM' : ∀ y, expectedExitTime m A y ≤ M := fun y => by
    by_cases hy : y ∈ A
    · exact hM y hy
    · rw [expectedExitTime_eq_zero_of_not_mem m hy]; exact zero_le
  have hτ : Measurable fun y : ℕ → ℤ => ((vExitTime A y : ℕ∞) : ℝ≥0∞) :=
    (measurable_of_countable _).comp (measurable_vExitTime A)
  induction N generalizing a with
  | zero => simp [exitTimeMoment]
  | succ N ih =>
    have hg : Measurable fun y : ℕ → ℤ => ((vExitTime A y : ℕ∞) : ℝ≥0∞) ^ N := hτ.pow_const N
    have hmeas : ∀ j : ℕ, Measurable fun x : ℕ → ℤ =>
        stayIn A j (pathHist j x) * ((vExitTime A (pathShift j x) : ℕ∞) : ℝ≥0∞) ^ N := fun j =>
      ((measurable_stayIn A j).comp (measurable_pathHist j)).mul (hg.comp (walk_measurable_pathShift j))
    have hstay : ∀ j : ℕ, Measurable fun x : ℕ → ℤ => stayIn A j (pathHist j x) := fun j =>
      (measurable_stayIn A j).comp (measurable_pathHist j)
    calc exitTimeMoment m A a (N + 1)
        = ∫⁻ x, ((vExitTime A x : ℕ∞) : ℝ≥0∞) ^ (N + 1) ∂srwLaw m a := rfl
      _ ≤ ∫⁻ x, ((N + 1 : ℕ) : ℝ≥0∞) * ∑' j : ℕ, stayIn A j (pathHist j x) *
            ((vExitTime A (pathShift j x) : ℕ∞) : ℝ≥0∞) ^ N ∂srwLaw m a :=
          lintegral_mono fun x => pow_vExitTime_le_tsum A N x
      _ = ((N + 1 : ℕ) : ℝ≥0∞) * ∑' j : ℕ, ∫⁻ x, stayIn A j (pathHist j x) *
            ((vExitTime A (pathShift j x) : ℕ∞) : ℝ≥0∞) ^ N ∂srwLaw m a := by
          rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
            lintegral_tsum fun j => (hmeas j).aemeasurable]
      _ = ((N + 1 : ℕ) : ℝ≥0∞) * ∑' j : ℕ, ∫⁻ x, stayIn A j (pathHist j x) *
            ∫⁻ y, ((vExitTime A y : ℕ∞) : ℝ≥0∞) ^ N ∂srwLaw m (x j) ∂srwLaw m a := by
          congr 1
          exact tsum_congr fun j => lintegral_srwLaw_markov m j a (stayIn A j) hg
      _ ≤ ((N + 1 : ℕ) : ℝ≥0∞) * ∑' j : ℕ, ∫⁻ x, stayIn A j (pathHist j x) *
            ((N.factorial : ℝ≥0∞) * M ^ N) ∂srwLaw m a := by
          gcongr with j x
          exact ih (x j)
      _ = ((N + 1 : ℕ) : ℝ≥0∞) * ((N.factorial : ℝ≥0∞) * M ^ N) *
            ∑' j : ℕ, ∫⁻ x, stayIn A j (pathHist j x) ∂srwLaw m a := by
          rw [mul_assoc]
          congr 1
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun j => ?_
          rw [lintegral_mul_const _ (hstay j), mul_comm]
      _ ≤ ((N + 1 : ℕ) : ℝ≥0∞) * ((N.factorial : ℝ≥0∞) * M ^ N) * M := by
          gcongr
          calc ∑' j : ℕ, ∫⁻ x, stayIn A j (pathHist j x) ∂srwLaw m a
              = ∫⁻ x, ∑' j : ℕ, stayIn A j (pathHist j x) ∂srwLaw m a :=
                (lintegral_tsum fun j => (hstay j).aemeasurable).symm
            _ ≤ ∫⁻ x, ((vExitTime A x : ℕ∞) : ℝ≥0∞) ∂srwLaw m a :=
                lintegral_mono fun x => tsum_stayIn_le A x
            _ ≤ M := hM' a
      _ = ((N + 1).factorial : ℝ≥0∞) * M ^ (N + 1) := by
          rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
          ring

end MatedCRT
