import MatedCRT.Proofs.WalkPotential.Markov
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple
import MatedCRT.Proofs.Sec4.GreenLaplacian
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The Green's function in its first variable: `Δ G_A(·, b) = -δ_b` on a finite set `A`
(eq:discrete-green-laplacian, line 797; Lawler-Limic, Proposition 6.2.3)

For a locally finite multigraph on `ℤ` with `k ∼ k + 1` and a finite `A`:

* first-step analysis (`lintegral_firstStep`): for `a ∈ A` the visits to `b` before exiting `A` of the path
  `(a, Y)` are `1{a = b}` plus those of `Y`, so `E^a[V] = 1{a = b} + ∫ E^c[V] p(a, dc)` in `[0, ∞]`;
* finiteness (`lintegral_visitsBeforeExit_ne_top`): the expected number of visits before time `n`, `E^a[V_n]`, is
  dominated by the nonnegative solution `v` of the Dirichlet problem `Δv = -δ_b` on `A`, `v = 0` off `A`
  (`exists_nonneg_laplacian_eq`), by induction on `n`; `E^a[V] = sup_n E^a[V_n]` (monotone convergence);
* hence `G_A(a, b) = 1{a = b} + ∑_c p(a, c) G_A(c, b)` in `ℝ`, i.e. `Δ G_A(·, b)(a) = -δ_b(a)` (`mLaplacian_greenFn`).
-/

namespace MatedCRT.WalkPotential

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {m : ℤ → ℤ → ℕ}

/-! ## Exit times of `(a, Y)` -/

open Classical in
theorem natCast_lt_vExitTime_iff {A : Set ℤ} {x : ℕ → ℤ} {n : ℕ} :
    (n : ℕ∞) < vExitTime A x ↔ ∀ k ≤ n, x k ∈ A := by
  unfold vExitTime
  split_ifs with h
  · rw [Nat.cast_lt, Nat.lt_find_iff]
    simp only [not_not]
  · simp only [not_exists, not_not] at h
    exact ⟨fun _ k _ => h k, fun _ => ENat.natCast_lt_top n⟩

theorem natCast_succ_lt_vExitTime_pathCons_iff {A : Set ℤ} {a : ℤ} (ha : a ∈ A) (y : ℕ → ℤ) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) < vExitTime A (pathCons a y) ↔ (n : ℕ∞) < vExitTime A y := by
  rw [natCast_lt_vExitTime_iff, natCast_lt_vExitTime_iff]
  constructor
  · intro h k hk
    exact h (k + 1) (by omega)
  · intro h k hk
    cases k with
    | zero => exact ha
    | succ k => exact h k (by omega)

theorem zero_lt_vExitTime_pathCons {A : Set ℤ} {a : ℤ} (ha : a ∈ A) (y : ℕ → ℤ) :
    ((0 : ℕ) : ℕ∞) < vExitTime A (pathCons a y) :=
  natCast_lt_vExitTime_iff.2 fun k hk => by
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    exact ha

theorem measurableSet_natCast_lt_vExitTime' (A : Set ℤ) (k : ℕ) :
    MeasurableSet {x : ℕ → ℤ | (k : ℕ∞) < vExitTime A x} := by
  have : {x : ℕ → ℤ | (k : ℕ∞) < vExitTime A x} = ⋂ j ∈ Iic k, (fun x : ℕ → ℤ => x j) ⁻¹' A := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_Iic]
    exact natCast_lt_vExitTime_iff
  rw [this]
  exact MeasurableSet.biInter (to_countable _) fun j _ => measurable_pi_apply j (to_countable A).measurableSet

/-! ## Visits before the exit time -/

theorem measurable_visitTerm (A : Set ℤ) (b : ℤ) (k : ℕ) :
    Measurable fun x : ℕ → ℤ => if (k : ℕ∞) < vExitTime A x ∧ x k = b then (1 : ℝ≥0∞) else 0 := by
  have h : MeasurableSet ((fun x : ℕ → ℤ => x k) ⁻¹' {b}) := measurable_pi_apply k (measurableSet_singleton b)
  exact Measurable.ite ((measurableSet_natCast_lt_vExitTime' A k).inter h) measurable_const measurable_const

/-- The number of times `k < n` with `k < τ_A` at which the path is at `b`. -/
noncomputable def visitsUpTo (A : Set ℤ) (b : ℤ) (n : ℕ) (x : ℕ → ℤ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range n, if (k : ℕ∞) < vExitTime A x ∧ x k = b then 1 else 0

theorem measurable_visitsUpTo (A : Set ℤ) (b : ℤ) (n : ℕ) : Measurable (visitsUpTo A b n) := by
  unfold visitsUpTo
  exact Finset.measurable_sum _ fun k _ => measurable_visitTerm A b k

theorem measurable_visitsBeforeExit' (A : Set ℤ) (b : ℤ) : Measurable (visitsBeforeExit A b) := by
  unfold visitsBeforeExit
  exact Measurable.tsum fun k => measurable_visitTerm A b k

theorem visitsUpTo_eq_zero {A : Set ℤ} {x : ℕ → ℤ} (hx : x 0 ∉ A) (b : ℤ) (n : ℕ) : visitsUpTo A b n x = 0 := by
  unfold visitsUpTo
  refine Finset.sum_eq_zero fun k _ => ?_
  have : ¬ ((k : ℕ∞) < vExitTime A x) := fun h => hx (natCast_lt_vExitTime_iff.1 h 0 (Nat.zero_le _))
  simp [this]

theorem visitsUpTo_pathCons {A : Set ℤ} {a : ℤ} (ha : a ∈ A) (b : ℤ) (n : ℕ) (y : ℕ → ℤ) :
    visitsUpTo A b (n + 1) (pathCons a y) = (if a = b then 1 else 0) + visitsUpTo A b n y := by
  unfold visitsUpTo
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp only [zero_lt_vExitTime_pathCons ha y, true_and, pathCons_zero]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [natCast_succ_lt_vExitTime_pathCons_iff ha y k, pathCons_succ]

theorem visitsBeforeExit_pathCons {A : Set ℤ} {a : ℤ} (ha : a ∈ A) (b : ℤ) (y : ℕ → ℤ) :
    visitsBeforeExit A b (pathCons a y) = (if a = b then 1 else 0) + visitsBeforeExit A b y := by
  unfold visitsBeforeExit
  rw [tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · simp only [zero_lt_vExitTime_pathCons ha y, true_and, pathCons_zero]
  · refine tsum_congr fun k => ?_
    simp only [natCast_succ_lt_vExitTime_pathCons_iff ha y k, pathCons_succ]

theorem visitsBeforeExit_eq_iSup (A : Set ℤ) (b : ℤ) (x : ℕ → ℤ) :
    visitsBeforeExit A b x = ⨆ n, visitsUpTo A b n x := by
  unfold visitsBeforeExit visitsUpTo
  exact ENNReal.tsum_eq_iSup_nat

theorem lintegral_visitsBeforeExit_eq_iSup (m : ℤ → ℤ → ℕ) (A : Set ℤ) (b a : ℤ) :
    ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a = ⨆ n, ∫⁻ x, visitsUpTo A b n x ∂srwLaw m a := by
  simp_rw [visitsBeforeExit_eq_iSup]
  refine lintegral_iSup (fun n => measurable_visitsUpTo A b n) fun n n' h x => ?_
  unfold visitsUpTo
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-! ## First-step analysis -/

/-- `E^a[F] = ∫ E^c[F((a, ·))] p(a, dc)`. -/
theorem lintegral_srwLaw_eq_pathCons (m : ℤ → ℤ → ℕ) (a : ℤ) {F : (ℕ → ℤ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂srwLaw m a = ∫⁻ c, ∫⁻ y, F (pathCons a y) ∂srwLaw m c ∂srwStep m a := by
  rw [srwLaw_eq_srwFirstStepLaw m a, srwFirstStepLaw,
    Measure.lintegral_bind (measurable_of_countable _).aemeasurable hF.aemeasurable]
  refine lintegral_congr fun c => ?_
  rw [lintegral_map hF (measurable_pathCons a)]

theorem lintegral_const_add_of_prob {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (k : ℝ≥0∞) {g : α → ℝ≥0∞} (hg : Measurable g) : ∫⁻ x, k + g x ∂μ = k + ∫⁻ x, g x ∂μ := by
  rw [lintegral_add_right _ hg, lintegral_const, measure_univ, mul_one]

/-- If `F((a, y)) = k + H(y)`, then `E^a[F] = k + ∫ E^c[H] p(a, dc)`. -/
theorem lintegral_firstStep {a : ℤ} {F H : (ℕ → ℤ) → ℝ≥0∞} (hF : Measurable F) (hH : Measurable H)
    {k : ℝ≥0∞} (hFH : ∀ y, F (pathCons a y) = k + H y) :
    ∫⁻ x, F x ∂srwLaw m a = k + ∫⁻ c, ∫⁻ y, H y ∂srwLaw m c ∂srwStep m a := by
  rw [lintegral_srwLaw_eq_pathCons m a hF]
  have hc : ∀ c, ∫⁻ y, F (pathCons a y) ∂srwLaw m c = k + ∫⁻ y, H y ∂srwLaw m c := fun c => by
    simp_rw [hFH]
    exact lintegral_const_add_of_prob (srwLaw m c) k hH
  rw [lintegral_congr hc]
  exact lintegral_const_add_of_prob (srwStep m a) k (measurable_of_countable _)

theorem toReal_lintegral_srwStep (hlf : IsLocallyFiniteMult m) {a : ℤ} (hdeg : mdeg m a ≠ 0)
    {f : ℤ → ℝ≥0∞} (hf : ∀ c, f c ≠ ⊤) :
    ∫⁻ c, f c ∂srwStep m a ≠ ⊤ ∧
      (∫⁻ c, f c ∂srwStep m a).toReal = ((mdeg m a : ℝ))⁻¹ * ∑ c ∈ nbrs hlf a, (m a c : ℝ) * (f c).toReal := by
  rw [lintegral_srwStep hlf hdeg]
  have hterm : ∀ c ∈ nbrs hlf a, (m a c : ℝ≥0∞) * f c ≠ ⊤ := fun c _ =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hf c)
  refine ⟨ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast hdeg)) (ENNReal.sum_ne_top.2 hterm), ?_⟩
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_sum hterm]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast]

/-- `Δ G(a) = -k` iff `G(a) = k + ∑_c p(a, c) G(c)`, at a vertex of positive degree. -/
theorem mLaplacian_eq_neg_iff (hlf : IsLocallyFiniteMult m) {a : ℤ} (hdeg : mdeg m a ≠ 0) (G : ℤ → ℝ) (k : ℝ) :
    mLaplacian m G a = -k ↔ G a = k + ((mdeg m a : ℝ))⁻¹ * ∑ c ∈ nbrs hlf a, (m a c : ℝ) * G c := by
  have hd : (mdeg m a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hdeg
  have hlap : lapSum hlf G a = ∑ c ∈ nbrs hlf a, (m a c : ℝ) * G c - (mdeg m a : ℝ) * G a := by
    rw [lapSum, mdeg_cast_eq hlf, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  have e : lapSum hlf G a / (mdeg m a : ℝ) =
      ((mdeg m a : ℝ))⁻¹ * ∑ c ∈ nbrs hlf a, (m a c : ℝ) * G c - G a := by
    rw [hlap, sub_div, mul_div_cancel_left₀ _ hd, div_eq_inv_mul]
  rw [mLaplacian_eq_div hlf, e]
  constructor <;> intro h <;> linarith

/-! ## Finiteness and the Laplacian in the first variable -/

theorem lintegral_visitsUpTo_le (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {A : Set ℤ}
    (b : ℤ) {v : ℤ → ℝ} (hv0 : ∀ a, 0 ≤ v a)
    (hv : ∀ a ∈ A, v a = (if a = b then 1 else 0) + ((mdeg m a : ℝ))⁻¹ * ∑ c ∈ nbrs hlf a, (m a c : ℝ) * v c) :
    ∀ n a, ∫⁻ x, visitsUpTo A b n x ∂srwLaw m a ≤ ENNReal.ofReal (v a) := by
  intro n
  induction n with
  | zero =>
    intro a
    simp [visitsUpTo]
  | succ n ih =>
    intro a
    by_cases ha : a ∈ A
    · rw [lintegral_firstStep (measurable_visitsUpTo A b (n + 1)) (measurable_visitsUpTo A b n)
        (visitsUpTo_pathCons ha b n)]
      have hdeg := mdeg_ne_zero_of_ne_zero hlf (hcons a)
      obtain ⟨hfin, hval⟩ := toReal_lintegral_srwStep hlf hdeg (f := fun c => ENNReal.ofReal (v c))
        fun _ => ENNReal.ofReal_ne_top
      have hq : 0 ≤ ((mdeg m a : ℝ))⁻¹ * ∑ c ∈ nbrs hlf a, (m a c : ℝ) * v c :=
        mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
          (Finset.sum_nonneg fun c _ => mul_nonneg (Nat.cast_nonneg _) (hv0 c))
      have hp : (0 : ℝ) ≤ if a = b then 1 else 0 := by split_ifs <;> norm_num
      have h1 : ((if a = b then (1 : ℝ≥0∞) else 0)) = ENNReal.ofReal (if a = b then 1 else 0) := by
        split_ifs <;> simp
      calc (if a = b then 1 else 0) + ∫⁻ c, ∫⁻ x, visitsUpTo A b n x ∂srwLaw m c ∂srwStep m a
          ≤ (if a = b then 1 else 0) + ∫⁻ c, ENNReal.ofReal (v c) ∂srwStep m a :=
            add_le_add le_rfl (lintegral_mono fun c => ih c)
        _ = ENNReal.ofReal (v a) := by
            rw [← ENNReal.ofReal_toReal hfin, hval, hv a ha, ENNReal.ofReal_add hp hq, h1]
            simp only [ENNReal.toReal_ofReal (hv0 _)]
    · have h0 : ∫⁻ x, visitsUpTo A b (n + 1) x ∂srwLaw m a = 0 := by
        rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
        filter_upwards [srwLaw_ae_start m a] with x hx
        refine visitsUpTo_eq_zero ?_ b (n + 1)
        rw [hx]
        exact ha
      rw [h0]
      exact zero_le

/-- **eq:discrete-green-laplacian** (line 797): `Δ G_A(·, b) = -δ_b` on a finite `A`. -/
theorem mLaplacian_greenFn (hlf : ∀ a, {b | m a b ≠ 0}.Finite) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {A : Set ℤ} (hA : A.Finite) (b : ℤ) :
    ∀ a ∈ A, mLaplacian m (fun x => greenFn m A x b) a = -(if a = b then 1 else 0) := by
  obtain ⟨v, -, hvΔ, hv0⟩ := exists_nonneg_laplacian_eq hcons hlf hA
    (fun a => -(if a = b then (1 : ℝ) else 0)) fun a _ => by split_ifs <;> norm_num
  have hdeg : ∀ a, mdeg m a ≠ 0 := fun a => mdeg_ne_zero_of_ne_zero hlf (hcons a)
  have hv : ∀ a ∈ A, v a = (if a = b then 1 else 0) +
      ((mdeg m a : ℝ))⁻¹ * ∑ c ∈ nbrs hlf a, (m a c : ℝ) * v c :=
    fun a ha => (mLaplacian_eq_neg_iff hlf (hdeg a) v _).1 (hvΔ a ha)
  have hup := lintegral_visitsUpTo_le hlf hcons b hv0 hv
  have hfin : ∀ a, ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a ≠ ⊤ := by
    intro a
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (?_ : _ ≤ ENNReal.ofReal (v a))
    rw [lintegral_visitsBeforeExit_eq_iSup]
    exact iSup_le fun n => hup n a
  intro a ha
  have hid := lintegral_firstStep (m := m) (measurable_visitsBeforeExit' A b) (measurable_visitsBeforeExit' A b)
    (visitsBeforeExit_pathCons ha b)
  obtain ⟨hstep, hval⟩ := toReal_lintegral_srwStep hlf (hdeg a)
    (f := fun c => ∫⁻ x, visitsBeforeExit A b x ∂srwLaw m c) hfin
  have e1 : ((if a = b then (1 : ℝ≥0∞) else 0)).toReal = if a = b then 1 else 0 := by
    split_ifs <;> simp
  have e2 : ((if a = b then (1 : ℝ≥0∞) else 0)) ≠ ⊤ := by
    split_ifs <;> simp
  refine (mLaplacian_eq_neg_iff hlf (hdeg a) _ _).2 ?_
  show (∫⁻ x, visitsBeforeExit A b x ∂srwLaw m a).toReal = _
  rw [hid, ENNReal.toReal_add e2 hstep, hval, e1]
  rfl

end MatedCRT.WalkPotential
