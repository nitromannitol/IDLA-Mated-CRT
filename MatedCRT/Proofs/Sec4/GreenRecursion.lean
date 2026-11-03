import MatedCRT.Proofs.Sec4.GreenFirstStep

/-!
# From the first-step recursion of the truncated visit counts to `Δ G_A(·, b) = -δ_b`

Abstract form of the argument for eq:discrete-green-laplacian (line 797). Let `E N c ∈ [0, ∞]` (the expected number of
visits to `b` before `min(τ_A, N)` of the walk from `c`) satisfy `E 0 = 0`, `E N = 0` off `A`, `N ↦ E N c` monotone, and
the first-step recursion `E (N+1) a = δ_{ab} + ∑_{c ∼ a} p(a,c) E N c` on `A`, `p(a,c) = m(a,c)/deg(a)`. Then:
* `le_ofReal_of_recursion`: `E N ≤ v` where `v ≥ 0` solves `Δv = -δ_b` on `A`, `v = 0` off `A`
  (`exists_nonneg_laplacian_eq`); hence `G = sup_N E N` is finite;
* `iSup_recursion`: `G a = δ_{ab} + ∑_{c ∼ a} p(a,c) G c` on `A`;
* `laplacian_toReal_of_recursion`: `Δ G.toReal = -δ_b` on `A`.
-/

namespace MatedCRT

open Set Classical
open scoped ENNReal

variable {m : ℤ → ℤ → ℕ} {A : Set ℤ}

theorem lapSum_eq_sub (hlf : IsLocallyFiniteMult m) (u : ℤ → ℝ) (a : ℤ) :
    lapSum hlf u a = ∑ c ∈ nbrs hlf a, (m a c : ℝ) * u c - u a * (mdeg m a : ℝ) := by
  unfold lapSum
  rw [mdeg_cast_eq hlf a, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem sum_div_mdeg_mul (hlf : IsLocallyFiniteMult m) (u : ℤ → ℝ) (a : ℤ) :
    ∑ c ∈ nbrs hlf a, ((m a c : ℝ) / mdeg m a) * u c = (∑ c ∈ nbrs hlf a, (m a c : ℝ) * u c) / mdeg m a := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- `Δu(a) = r` gives `u(a) = -r + ∑_{c ∼ a} p(a,c) u(c)`. -/
theorem eq_of_mLaplacian_eq (hlf : IsLocallyFiniteMult m) {a : ℤ} (hd : (mdeg m a : ℝ) ≠ 0) {u : ℤ → ℝ} {r : ℝ}
    (h : mLaplacian m u a = r) : u a = -r + ∑ c ∈ nbrs hlf a, ((m a c : ℝ) / mdeg m a) * u c := by
  have h1 := mLaplacian_mul_mdeg hlf u a
  rw [h, lapSum_eq_sub] at h1
  have h3 : (∑ c ∈ nbrs hlf a, (m a c : ℝ) * u c) / mdeg m a = r + u a := by
    rw [div_eq_iff hd]
    linear_combination (-1 : ℝ) * h1
  rw [sum_div_mdeg_mul, h3]
  ring

/-- `u(a) = -r + ∑_{c ∼ a} p(a,c) u(c)` gives `Δu(a) = r`. -/
theorem mLaplacian_eq_of_eq (hlf : IsLocallyFiniteMult m) {a : ℤ} (hd : (mdeg m a : ℝ) ≠ 0) {u : ℤ → ℝ} {r : ℝ}
    (h : u a = -r + ∑ c ∈ nbrs hlf a, ((m a c : ℝ) / mdeg m a) * u c) : mLaplacian m u a = r := by
  rw [eq_div_of_mul_eq hd (mLaplacian_mul_mdeg hlf u a), lapSum_eq_sub, div_eq_iff hd]
  rw [sum_div_mdeg_mul] at h
  have h3 : ∑ c ∈ nbrs hlf a, (m a c : ℝ) * u c = (u a + r) * mdeg m a :=
    (div_eq_iff hd).1 (by linarith)
  rw [h3]
  ring

theorem ofReal_ite_one_zero (P : Prop) [Decidable P] :
    ENNReal.ofReal (if P then 1 else 0) = if P then 1 else 0 := by
  split_ifs <;> simp

/-- The truncated counts are bounded by the nonnegative solution of the Dirichlet problem. -/
theorem le_ofReal_of_recursion (hlf : IsLocallyFiniteMult m) {b : ℤ} {v : ℤ → ℝ} (hv0 : ∀ c, 0 ≤ v c)
    (hvA : ∀ a ∈ A, v a = (if a = b then 1 else 0) + ∑ c ∈ nbrs hlf a, ((m a c : ℝ) / mdeg m a) * v c)
    {E : ℕ → ℤ → ℝ≥0∞} (hE0 : ∀ c, E 0 c = 0) (hEout : ∀ N, ∀ c ∉ A, E N c = 0)
    (hEstep : ∀ N, ∀ a ∈ A, E (N + 1) a =
      (if a = b then 1 else 0) + ∑ c ∈ nbrs hlf a, ENNReal.ofReal ((m a c : ℝ) / mdeg m a) * E N c) :
    ∀ N c, E N c ≤ ENNReal.ofReal (v c) := by
  intro N
  induction N with
  | zero => intro c; rw [hE0 c]; exact zero_le
  | succ N ih =>
    intro c
    by_cases hc : c ∈ A
    · have hp : ∀ d ∈ nbrs hlf c, 0 ≤ ((m c d : ℝ) / mdeg m c) * v d := fun d _ =>
        mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hv0 d)
      rw [hEstep N c hc, hvA c hc, ENNReal.ofReal_add (by split_ifs <;> norm_num) (Finset.sum_nonneg hp),
        ENNReal.ofReal_sum_of_nonneg hp, ofReal_ite_one_zero]
      gcongr with d hd
      rw [ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      gcongr
      exact ih d
    · rw [hEout _ c hc]
      exact zero_le

/-- A finite sum of suprema of monotone sequences is the supremum of the sums. -/
theorem finset_sum_iSup_of_monotone {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℝ≥0∞) (hF : ∀ i, Monotone (F i)) :
    ∑ i ∈ s, ⨆ N, F i N = ⨆ N, ∑ i ∈ s, F i N := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, ih,
      ENNReal.iSup_add_iSup_of_monotone (hF i) fun N M h => Finset.sum_le_sum fun c _ => hF c h]
    simp_rw [Finset.sum_insert hi]

/-- Passage to the supremum in the first-step recursion. -/
theorem iSup_recursion (hlf : IsLocallyFiniteMult m) {b : ℤ} {E : ℕ → ℤ → ℝ≥0∞}
    (hmono : ∀ c, Monotone fun N => E N c)
    (hEstep : ∀ N, ∀ a ∈ A, E (N + 1) a =
      (if a = b then 1 else 0) + ∑ c ∈ nbrs hlf a, ENNReal.ofReal ((m a c : ℝ) / mdeg m a) * E N c)
    {a : ℤ} (ha : a ∈ A) :
    ⨆ N, E N a = (if a = b then 1 else 0) +
      ∑ c ∈ nbrs hlf a, ENNReal.ofReal ((m a c : ℝ) / mdeg m a) * ⨆ N, E N c := by
  have hshift : ⨆ N, E N a = ⨆ N, E (N + 1) a :=
    le_antisymm (iSup_le fun N => (hmono a N.le_succ).trans (le_iSup (fun N => E (N + 1) a) N))
      (iSup_le fun N => le_iSup (fun N => E N a) (N + 1))
  rw [hshift]
  simp_rw [hEstep _ a ha, ENNReal.mul_iSup]
  rw [← ENNReal.add_iSup, finset_sum_iSup_of_monotone _ _ fun c => (hmono c).const_mul' _]

/-- `Δ G.toReal = -δ_b` on `A`, for `G = sup_N E N` with `E` satisfying the first-step recursion. -/
theorem laplacian_toReal_of_recursion (hcons : ∀ a, m a (a + 1) ≠ 0) (hlf : IsLocallyFiniteMult m)
    (hA : A.Finite) {b : ℤ} {E : ℕ → ℤ → ℝ≥0∞} (hmono : ∀ c, Monotone fun N => E N c) (hE0 : ∀ c, E 0 c = 0)
    (hEout : ∀ N, ∀ c ∉ A, E N c = 0)
    (hEstep : ∀ N, ∀ a ∈ A, E (N + 1) a =
      (if a = b then 1 else 0) + ∑ c ∈ nbrs hlf a, ENNReal.ofReal ((m a c : ℝ) / mdeg m a) * E N c)
    {G : ℤ → ℝ≥0∞} (hG : ∀ c, G c = ⨆ N, E N c) :
    ∀ a ∈ A, mLaplacian m (fun x => (G x).toReal) a = -(if a = b then 1 else 0) := by
  have hd : ∀ a, (mdeg m a : ℝ) ≠ 0 := fun a => Nat.cast_ne_zero.2 (mdeg_pos_of_ne_zero hlf (hcons a)).ne'
  obtain ⟨v, hv0, hvL, hvnn⟩ := exists_nonneg_laplacian_eq hcons hlf hA (fun a => -(if a = b then 1 else 0))
    fun a _ => by split_ifs <;> norm_num
  have hvA : ∀ a ∈ A, v a = (if a = b then 1 else 0) + ∑ c ∈ nbrs hlf a, ((m a c : ℝ) / mdeg m a) * v c :=
    fun a ha => by rw [eq_of_mLaplacian_eq hlf (hd a) (hvL a ha), neg_neg]
  have hbound := le_ofReal_of_recursion hlf hvnn hvA hE0 hEout hEstep
  have hfin : ∀ c, G c ≠ ⊤ := fun c =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by rw [hG c]; exact iSup_le fun N => hbound N c)
  intro a ha
  refine mLaplacian_eq_of_eq hlf (hd a) ?_
  have hrec := iSup_recursion hlf hmono hEstep ha
  rw [← hG a] at hrec
  simp_rw [← hG] at hrec
  have hterm : ∀ c ∈ nbrs hlf a, ENNReal.ofReal ((m a c : ℝ) / mdeg m a) * G c ≠ ⊤ := fun c _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin c)
  rw [hrec, ENNReal.toReal_add (by split_ifs <;> simp) (ENNReal.sum_ne_top.2 hterm),
    ENNReal.toReal_sum hterm, neg_neg]
  congr 1
  · split_ifs <;> simp
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

end MatedCRT
