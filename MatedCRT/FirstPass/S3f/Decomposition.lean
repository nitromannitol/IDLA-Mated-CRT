-- Renamed copy of the untracked draft MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/Decomposition.lean; namespace MatedCRT.FirstPass37; srwLaw_nonadjacent_null -> WalkSteps.srwLaw_nonadjacent_null (Walk.lean:38); imports the S3f copy of ExitValue.
import MatedCRT.FirstPass.S3f.ExitValue
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.GreenRepresentation
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk

/-!
# Lemma 3.5, Step 1: the discrete solution as exit value minus Green potential

On a finite set `A` whose neighbours lie in `A ∪ B`, a function `F` with `Δ F = ψ'` on `A` is, on `A ∪ B`, the
expected value of `F` at the exit position from `A` (which lies in `B`) minus the Green potential of `ψ'`
(Lawler-Limic, Corollary 6.2.4).
-/

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRT.FirstPass37

open WalkPotential

variable {m : ℤ → ℤ → ℕ}

/-- A walk started off `A` exits at once, at its starting point. -/
theorem integral_exitValue_of_notMem {A : Set ℤ} (g : ℤ → ℝ) {c : ℤ} (hc : c ∉ A) :
    ∫ x, g (vExitPosition A x) ∂srwLaw m c = g c := by
  have h : ∀ᵐ x ∂srwLaw m c, g (vExitPosition A x) = g c := by
    filter_upwards [srwLaw_ae_start m c] with x hx
    unfold vExitPosition
    rw [vExitTime_eq_zero_of_not_mem (by rw [hx]; exact hc)]
    simp [hx]
  rw [integral_congr_ae h]
  simp

/-- A walk started in `A` whose neighbours lie in `A ∪ B` exits `A` into `B`. -/
theorem ae_vExitPosition_mem {A B : Set ℤ} (hnb : ∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∈ A ∪ B)
    {a : ℤ} (ha : a ∈ A) :
    ∀ᵐ x ∂srwLaw m a, vExitTime A x ≠ ⊤ → vExitPosition A x ∈ B := by
  have hadj : ∀ᵐ x ∂srwLaw m a, ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0 := by
    rw [ae_all_iff]
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (WalkSteps.srwLaw_nonadjacent_null m n a)] with x hx
    exact Classical.not_not.1 hx
  filter_upwards [srwLaw_ae_start m a, hadj] with x h0 hadj hfin
  unfold vExitPosition
  induction hk : vExitTime A x using ENat.recTopCoe with
  | top => exact absurd hk hfin
  | coe k =>
    rw [ENat.toNat_natCast]
    have hout : x k ∉ A := apply_vExitTime_not_mem hk
    cases k with
    | zero => exact absurd (h0 ▸ ha) hout
    | succ j =>
      have hin : x j ∈ A := mem_of_lt_vExitTime (by rw [hk]; exact_mod_cast Nat.lt_succ_self j)
      rcases hadj j with h | h
      · exact absurd (h ▸ hin) hout
      · exact (hnb (x j) hin _ h).resolve_left hout

/-- **Decomposition of the discrete Dirichlet solution** (Lawler-Limic, Corollary 6.2.4). -/
theorem eq_exitValue_sub_greenPotential (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A B : Set ℤ} (hA : A.Finite) (hB : B.Finite)
    (hnb : ∀ a ∈ A, ∀ b, m a b ≠ 0 → b ∈ A ∪ B)
    (hexit : ∀ c ∈ A, ∀ᵐ x ∂srwLaw m c, vExitTime A x ≠ ⊤)
    (F ψ' : ℤ → ℝ) (hF : ∀ a ∈ A, mLaplacian m F a = ψ' a) {a : ℤ} (ha : a ∈ A ∪ B) :
    F a = ∫ x, B.indicator F (vExitPosition A x) ∂srwLaw m a -
      ∑ b ∈ hA.toFinset, ψ' b * greenFn m A a b := by
  classical
  set g : ℤ → ℝ := B.indicator F with hg
  set C : ℝ := ∑ b ∈ hB.toFinset, |F b| with hC
  have hgC : ∀ b, |g b| ≤ C := by
    intro b
    by_cases hb : b ∈ B
    · rw [hg, indicator_of_mem hb]
      exact Finset.single_le_sum (f := fun b => |F b|) (fun _ _ => abs_nonneg _)
        (hB.mem_toFinset.2 hb)
    · rw [hg, indicator_of_notMem hb, abs_zero]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  set H : ℤ → ℝ := fun c => ∫ x, g (vExitPosition A x) ∂srwLaw m c with hH
  set F' : ℤ → ℝ := fun c => if c ∈ A ∪ B then F c else H c with hF'
  have hF'mem : ∀ c ∈ A ∪ B, F' c = F c := fun c hc => by
    simp only [hF', ite_eq_left hc]
  have hbd : ∀ c ∉ A, F' c = H c := by
    intro c hc
    by_cases hcB : c ∈ B
    · rw [hF'mem c (Or.inr hcB)]
      show F c = ∫ x, g (vExitPosition A x) ∂srwLaw m c
      rw [integral_exitValue_of_notMem g hc, hg, indicator_of_mem hcB]
    · simp only [hF']
      rw [ite_eq_right (fun h => h.elim hc hcB)]
  have hu : ∀ c ∈ A, mLaplacian m F' c = -(fun b => -ψ' b) c := by
    intro c hc
    rw [neg_neg, ← hF c hc]
    unfold mLaplacian
    congr 1
    refine finsum_congr fun b => ?_
    by_cases hmb : m c b = 0
    · simp [hmb]
    · rw [hF'mem b (hnb c hc b hmb), hF'mem c (Or.inl hc)]
  have hh : ∀ c ∈ A, mLaplacian m H c = 0 := fun c hc =>
    mLaplacian_integral_exitValue hlf hexit hc (mdeg_ne_zero_of_ne_zero hlf (hcons c)) hgC
  have hrep := eq_harmonic_add_greenPotential hlf hcons hA (fun b => -ψ' b) F' H hbd hu hh a
  rw [hF'mem a ha] at hrep
  rw [hrep]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

end MatedCRT.FirstPass37
