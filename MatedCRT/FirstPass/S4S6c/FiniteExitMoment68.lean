import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationIntegrable
import MatedCRT.Proofs.IDLA.Measurable
import MatedCRT.Proofs.IDLA.StrongMarkov
import MatedCRT.Proofs.WalkPotential.MarkovFixedTime

/-!
# Exit-time moments of a finite domain

For a finite set `D ⊆ ℤ` of vertices of a locally finite multigraph `m` with `m k (k + 1) ≠ 0`, the first exit
time `τ_D` of simple random walk (Armitage–Gardiner: exit time of a set) satisfies:

* `τ_D < ∞` almost surely from every start (`ExitNull68.exit_null_of_finite`);
* `E_a[τ_D] < ∞` (`Audit.StatementsSec3Sec5M1.finite_expectedExitTime`), hence the first moment is integrable;
* `E_a[τ_D²] < ∞`. This is proved from a geometric tail `P_b(jL < τ_D) ≤ 2^{-j}` (uniform in `b`), obtained from
  Markov's inequality at the block length `L` and the fixed-time Markov property (`srwLaw_markov`).

The main statement is `FiniteExitMoment68.finiteDomain_exitMoments68`.
-/

namespace MatedCRT
namespace FiniteExitMoment68

open MeasureTheory Set Filter
open scoped ENNReal

/-- A uniform integer bound for the expected exit times of a finite set `D` from all starts. -/
lemma exists_nat_bound_expectedExitTime {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {D : Set ℤ} (hD : D.Finite) :
    ∃ N : ℕ, ∀ b : ℤ, expectedExitTime m D b ≤ N := by
  classical
  have hfin : ∀ b : ℤ, expectedExitTime m D b ≠ ⊤ := fun b =>
    MatedCRT.Audit.StatementsSec3Sec5M1.finite_expectedExitTime hlf hcons hD (a := b)
  have hSlt : hD.toFinset.sup (fun b => expectedExitTime m D b) < ⊤ :=
    (Finset.sup_lt_iff bot_lt_top).2 fun b _ => lt_top_iff_ne_top.2 (hfin b)
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hSlt.ne
  refine ⟨N, fun b => ?_⟩
  by_cases hb : b ∈ D
  · exact (Finset.le_sup (f := fun b => expectedExitTime m D b) (hD.mem_toFinset.2 hb)).trans hN.le
  · rw [expectedExitTime_eq_zero_of_not_mem m hb]
    exact zero_le

/-- Markov's inequality at the block length `L = 2N + 2`: `P_b(L < τ_D) ≤ 1/2` for every start `b`. -/
lemma exists_block_le_half {m : ℤ → ℤ → ℕ} {D : Set ℤ} {N : ℕ}
    (hN : ∀ b : ℤ, expectedExitTime m D b ≤ N) :
    ∃ L : ℕ, 0 < L ∧ ∀ b : ℤ, srwLaw m b {x | (L : ℕ∞) < vExitTime D x} ≤ 1 / 2 := by
  refine ⟨2 * N + 2, by omega, fun b => ?_⟩
  have hmeas : Measurable (fun x : ℕ → ℤ => ((vExitTime D x : ℕ∞) : ℝ≥0∞)) :=
    (measurable_of_countable (fun t : ℕ∞ => (t : ℝ≥0∞))).comp (measurable_vExitTime D)
  have hM := mul_meas_ge_le_lintegral₀ (μ := srwLaw m b) hmeas.aemeasurable
    ((2 * N + 2 : ℕ) : ℝ≥0∞)
  have hsub : {x : ℕ → ℤ | ((2 * N + 2 : ℕ) : ℕ∞) < vExitTime D x} ⊆
      {x : ℕ → ℤ | ((2 * N + 2 : ℕ) : ℝ≥0∞) ≤ ((vExitTime D x : ℕ∞) : ℝ≥0∞)} := by
    intro x hx
    have h := ENat.toENNReal_le.2 hx.le
    rwa [ENat.toENNReal_coe] at h
  have h1 : ((2 * N + 2 : ℕ) : ℝ≥0∞) * srwLaw m b {x : ℕ → ℤ | ((2 * N + 2 : ℕ) : ℕ∞) < vExitTime D x}
      ≤ ((2 * N + 2 : ℕ) : ℝ≥0∞) * srwLaw m b {x : ℕ → ℤ | ((2 * N + 2 : ℕ) : ℝ≥0∞) ≤
          ((vExitTime D x : ℕ∞) : ℝ≥0∞)} :=
    mul_le_mul_of_nonneg_left (measure_mono hsub) (by exact zero_le)
  have h2 : ((2 * N + 2 : ℕ) : ℝ≥0∞) * srwLaw m b {x : ℕ → ℤ | ((2 * N + 2 : ℕ) : ℕ∞) < vExitTime D x}
      ≤ (N : ℝ≥0∞) := by
    refine h1.trans (hM.trans ?_)
    exact hN b
  have h3 : ((2 * N + 2 : ℕ) : ℝ≥0∞) * srwLaw m b {x : ℕ → ℤ | ((2 * N + 2 : ℕ) : ℕ∞) < vExitTime D x}
      ≤ ((2 * N + 2 : ℕ) : ℝ≥0∞) * (1 / 2) := by
    refine h2.trans ?_
    have h22 : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
      rw [one_div, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
    have hc : ((2 * N + 2 : ℕ) : ℝ≥0∞) * (1 / 2) = (N : ℝ≥0∞) + 1 := by
      rw [show ((2 * N + 2 : ℕ) : ℝ≥0∞) = 2 * ((N : ℝ≥0∞) + 1) by push_cast; ring,
        mul_right_comm, h22, one_mul]
    rw [hc]
    exact le_self_add
  have hc0 : ((2 * N + 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : 2 * N + 2 ≠ 0)
  have hcT : ((2 * N + 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc srwLaw m b {x : ℕ → ℤ | ((2 * N + 2 : ℕ) : ℕ∞) < vExitTime D x}
      = ((2 * N + 2 : ℕ) : ℝ≥0∞)⁻¹ * (((2 * N + 2 : ℕ) : ℝ≥0∞) *
          srwLaw m b {x : ℕ → ℤ | ((2 * N + 2 : ℕ) : ℕ∞) < vExitTime D x}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hcT, one_mul]
    _ ≤ ((2 * N + 2 : ℕ) : ℝ≥0∞)⁻¹ * (((2 * N + 2 : ℕ) : ℝ≥0∞) * (1 / 2)) :=
        mul_le_mul_of_nonneg_left h3 (by exact zero_le)
    _ = 1 / 2 := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hcT, one_mul]

/-- The first `L + 1` coordinates lie in `D` iff the exit time exceeds `L`. -/
lemma exitTime_gt_iff_pathHist (D : Set ℤ) (L : ℕ) :
    {x : ℕ → ℤ | (L : ℕ∞) < vExitTime D x} =
      {x : ℕ → ℤ | pathHist L x ∈ {h : Fin (L + 1) → ℤ | ∀ i : Fin (L + 1), h i ∈ D}} := by
  ext x
  simp only [mem_ofPred_eq, pathHist]
  rw [natCast_lt_vExitTime_iff]
  constructor
  · intro h i
    exact h i (Nat.lt_succ_iff.mp i.isLt)
  · intro h j hj
    exact h ⟨j, Nat.lt_succ_of_le hj⟩

/-- Geometric tail: `P_b(jL < τ_D) ≤ 2^{-j}` for every start `b`, once `P_b(L < τ_D) ≤ 1/2` for all `b`. -/
lemma srwLaw_tail_le {m : ℤ → ℤ → ℕ} {D : Set ℤ} {L : ℕ}
    (hL : ∀ b : ℤ, srwLaw m b {x | (L : ℕ∞) < vExitTime D x} ≤ 1 / 2) :
    ∀ j : ℕ, ∀ a : ℤ, srwLaw m a {x | ((j * L : ℕ) : ℕ∞) < vExitTime D x} ≤ (1 / 2) ^ j := by
  intro j
  induction j with
  | zero =>
    intro a
    simp only [zero_mul, Nat.cast_zero, pow_zero]
    exact prob_le_one
  | succ j ih =>
    intro a
    have hsub : {x : ℕ → ℤ | (((j + 1) * L : ℕ) : ℕ∞) < vExitTime D x} ⊆
        {x : ℕ → ℤ | pathHist L x ∈ {h : Fin (L + 1) → ℤ | ∀ i : Fin (L + 1), h i ∈ D} ∧
          WalkPotential.pathShift L x ∈ {y : ℕ → ℤ | ((j * L : ℕ) : ℕ∞) < vExitTime D y}} := by
      intro x hx
      have hle : L ≤ (j + 1) * L := by nlinarith
      have hk : ∀ i ≤ L, x i ∈ D :=
        natCast_lt_vExitTime_iff.1 (lt_of_le_of_lt (by exact_mod_cast hle) hx)
      refine ⟨?_, ?_⟩
      · show ∀ i : Fin (L + 1), x (i : ℕ) ∈ D
        exact fun i => hk i (Nat.lt_succ_iff.mp i.isLt)
      · have h2 : ((j * L + L : ℕ) : ℕ∞) < vExitTime D x := by
          rw [show j * L + L = (j + 1) * L by ring]
          exact hx
        have hsh : WalkPotential.pathShift L x = MatedCRT.pathShift L x := by
          funext k
          show x (L + k) = x (k + L)
          rw [Nat.add_comm]
        show ((j * L : ℕ) : ℕ∞) < vExitTime D (WalkPotential.pathShift L x)
        rw [hsh]
        exact (lt_vExitTime_add_iff hk (j * L)).1 h2
    have hE : MeasurableSet {y : ℕ → ℤ | ((j * L : ℕ) : ℕ∞) < vExitTime D y} :=
      measurableSet_natCast_lt_vExitTime D (j * L)
    have hF : MeasurableSet {x : ℕ → ℤ | pathHist L x ∈
        {h : Fin (L + 1) → ℤ | ∀ i : Fin (L + 1), h i ∈ D}} := by
      rw [← exitTime_gt_iff_pathHist D L]
      exact measurableSet_natCast_lt_vExitTime D L
    calc srwLaw m a {x : ℕ → ℤ | (((j + 1) * L : ℕ) : ℕ∞) < vExitTime D x}
        ≤ srwLaw m a {x : ℕ → ℤ | pathHist L x ∈ {h : Fin (L + 1) → ℤ | ∀ i : Fin (L + 1), h i ∈ D} ∧
            WalkPotential.pathShift L x ∈ {y : ℕ → ℤ | ((j * L : ℕ) : ℕ∞) < vExitTime D y}} :=
          measure_mono hsub
      _ = ∫⁻ x in {x : ℕ → ℤ | pathHist L x ∈ {h : Fin (L + 1) → ℤ | ∀ i : Fin (L + 1), h i ∈ D}},
            srwLaw m (x L) {y : ℕ → ℤ | ((j * L : ℕ) : ℕ∞) < vExitTime D y} ∂srwLaw m a :=
          srwLaw_markov m a L _ hE
      _ ≤ ∫⁻ _ in {x : ℕ → ℤ | pathHist L x ∈ {h : Fin (L + 1) → ℤ | ∀ i : Fin (L + 1), h i ∈ D}},
            (1 / 2 : ℝ≥0∞) ^ j ∂srwLaw m a :=
          lintegral_mono fun x => ih (x L)
      _ = (1 / 2 : ℝ≥0∞) ^ j * srwLaw m a {x : ℕ → ℤ | pathHist L x ∈
            {h : Fin (L + 1) → ℤ | ∀ i : Fin (L + 1), h i ∈ D}} :=
          setLIntegral_const _ _
      _ = (1 / 2 : ℝ≥0∞) ^ j * srwLaw m a {x : ℕ → ℤ | (L : ℕ∞) < vExitTime D x} := by
          rw [exitTime_gt_iff_pathHist D L]
      _ ≤ (1 / 2 : ℝ≥0∞) ^ j * (1 / 2) := mul_le_mul_of_nonneg_left (hL a) (by exact zero_le)
      _ = (1 / 2 : ℝ≥0∞) ^ (j + 1) := (pow_succ _ _).symm

/-- Pointwise domination of `n²` by a series over the blocks `k L < n`. -/
lemma nat_sq_le_tsum_block (L : ℕ) (hL : 0 < L) (n : ℕ) :
    ((n : ℝ≥0∞)) ^ 2 ≤ ∑' k : ℕ, (if k * L < n then (((k + 1) * L : ℕ) : ℝ≥0∞) ^ 2 else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hdiv : (m / L) * L + m % L = m := by
      rw [mul_comm]
      exact Nat.div_add_mod m L
    have hmod := Nat.mod_lt m hL
    set q := m / L with hq
    have h1 : q * L < m + 1 := by linarith [Nat.zero_le (m % L)]
    have hmod' : m % L + 1 ≤ L := hmod
    have h2 : m + 1 ≤ (q + 1) * L := by
      rw [add_mul, one_mul]
      linarith
    have h2' : ((m + 1 : ℕ) : ℝ≥0∞) ≤ (((q + 1) * L : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h2
    calc (((m + 1 : ℕ)) : ℝ≥0∞) ^ 2 ≤ (((q + 1) * L : ℕ) : ℝ≥0∞) ^ 2 := by
          gcongr
      _ = (if q * L < m + 1 then (((q + 1) * L : ℕ) : ℝ≥0∞) ^ 2 else 0) := by
          simp [h1]
      _ ≤ _ := ENNReal.le_tsum (f := fun k : ℕ => if k * L < m + 1 then
          (((k + 1) * L : ℕ) : ℝ≥0∞) ^ 2 else 0) q

/-- The geometric-weighted series `∑ ((k+1) L)² 2^{-k}` is finite. -/
lemma tsum_block_sq_ne_top (L : ℕ) :
    ∑' k : ℕ, (((k + 1) * L : ℕ) : ℝ≥0∞) ^ 2 * (1 / 2 : ℝ≥0∞) ^ k ≠ ⊤ := by
  have hg : Summable (fun k : ℕ => (((k + 1) * L : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) := by
    have hs : Summable (fun k : ℕ => (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)
    have hgeo : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) := summable_geometric_two
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((hs.add hgeo).mul_left (2 * (L : ℝ) ^ 2))
    have hk : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    push_cast
    nlinarith [sq_nonneg ((k : ℝ) - 1), mul_nonneg hk (sq_nonneg ((k : ℝ) - 1)),
      mul_nonneg (sq_nonneg (L : ℝ)) hk, sq_nonneg (L : ℝ)]
  have h12 : ENNReal.ofReal (1 / 2 : ℝ) = 1 / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  have hfun : ∀ k : ℕ, (((k + 1) * L : ℕ) : ℝ≥0∞) ^ 2 * (1 / 2 : ℝ≥0∞) ^ k =
      ENNReal.ofReal ((((k + 1) * L : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k) := by
    intro k
    have hp : (0 : ℝ) ≤ (((k + 1) * L : ℕ) : ℝ) := by positivity
    rw [ENNReal.ofReal_mul (pow_nonneg hp 2), ENNReal.ofReal_pow hp,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), ENNReal.ofReal_natCast, h12]
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ (((k + 1) * L : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ k :=
    fun k => by positivity
  rw [tsum_congr hfun, ← ENNReal.ofReal_tsum_of_nonneg hnn hg]
  exact ENNReal.ofReal_ne_top

/-- The second moment of the exit time of a finite domain is finite (from the geometric tail). -/
lemma exitTimeMoment_two_ne_top {m : ℤ → ℤ → ℕ} {D : Set ℤ} (a : ℤ) {L : ℕ}
    (hL0 : 0 < L) (htail : ∀ j : ℕ, ∀ b : ℤ, srwLaw m b {x | ((j * L : ℕ) : ℕ∞) < vExitTime D x} ≤ (1 / 2) ^ j)
    (hae : ∀ᵐ x ∂srwLaw m a, vExitTime D x ≠ ⊤) :
    exitTimeMoment m D a 2 ≠ ⊤ := by
  classical
  have hmeasS : ∀ k : ℕ, MeasurableSet {x : ℕ → ℤ | ((k * L : ℕ) : ℕ∞) < vExitTime D x} :=
    fun k => measurableSet_natCast_lt_vExitTime D (k * L)
  have hle : ∫⁻ x, ((vExitTime D x : ℕ∞) : ℝ≥0∞) ^ 2 ∂srwLaw m a ≤
      ∫⁻ x, ∑' k : ℕ, {x : ℕ → ℤ | ((k * L : ℕ) : ℕ∞) < vExitTime D x}.indicator
        (fun _ => (((k + 1) * L : ℕ) : ℝ≥0∞) ^ 2) x ∂srwLaw m a := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hx
    rw [← hn, ENat.toENNReal_coe]
    refine (nat_sq_le_tsum_block L hL0 n).trans (le_of_eq (tsum_congr fun k => ?_))
    simp only [Set.indicator_apply, mem_ofPred_eq, ← hn, ENat.natCast_lt_natCast]
  have hsum : ∫⁻ x, ∑' k : ℕ, {x : ℕ → ℤ | ((k * L : ℕ) : ℕ∞) < vExitTime D x}.indicator
        (fun _ => (((k + 1) * L : ℕ) : ℝ≥0∞) ^ 2) x ∂srwLaw m a =
      ∑' k : ℕ, (((k + 1) * L : ℕ) : ℝ≥0∞) ^ 2 * srwLaw m a
        {x : ℕ → ℤ | ((k * L : ℕ) : ℕ∞) < vExitTime D x} := by
    rw [lintegral_tsum fun k => ((measurable_const.indicator (hmeasS k))).aemeasurable]
    refine tsum_congr fun k => ?_
    rw [lintegral_indicator_const (hmeasS k)]
  have hbound : ∑' k : ℕ, (((k + 1) * L : ℕ) : ℝ≥0∞) ^ 2 * srwLaw m a
      {x : ℕ → ℤ | ((k * L : ℕ) : ℕ∞) < vExitTime D x} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (tsum_block_sq_ne_top L) (ENNReal.tsum_le_tsum fun k => ?_)
    exact mul_le_mul_of_nonneg_left (htail k a) (by exact zero_le)
  refine ne_top_of_le_ne_top hbound ?_
  rw [← hsum]
  exact hle

/-- The `ℝ≥0∞`-valued square of an `ℕ∞` value, as a real number. -/
lemma toReal_sq_toENNReal (t : ℕ∞) :
    (((t : ℝ≥0∞)) ^ 2).toReal = ((t.toNat : ℕ) : ℝ) ^ 2 := by
  induction t using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/-- **Finite-domain exit moment.** For a finite vertex set `D` of a locally finite multigraph with
`m k (k+1) ≠ 0`, the exit time `τ_D` of simple random walk from `a` is almost surely finite, has finite first
and second moments `E_a[τ_D]`, `E_a[τ_D²]`, and `τ_D` and `τ_D²` are integrable. -/
theorem finiteDomain_exitMoments68 {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) {D : Set ℤ} (hD : D.Finite) (a : ℤ) :
    (∀ᵐ x ∂srwLaw m a, vExitTime D x ≠ ⊤) ∧
      exitTimeMoment m D a 1 ≠ ⊤ ∧ exitTimeMoment m D a 2 ≠ ⊤ ∧
      Integrable (fun x => ((vExitTime D x).toNat : ℝ)) (srwLaw m a) ∧
      Integrable (fun x => ((vExitTime D x).toNat : ℝ) ^ 2) (srwLaw m a) := by
  obtain ⟨N, hN⟩ := exists_nat_bound_expectedExitTime hlf hcons hD
  obtain ⟨L, hL0, hL⟩ := exists_block_le_half hN
  have hae : ∀ᵐ x ∂srwLaw m a, vExitTime D x ≠ ⊤ := by
    have h := ExitNull68.exit_null_of_finite hlf hcons hD a
    rw [measure_eq_zero_iff_ae_notMem] at h
    filter_upwards [h] with x hx
    simpa using hx
  have hmean : expectedExitTime m D a ≠ ⊤ :=
    MatedCRT.Audit.StatementsSec3Sec5M1.finite_expectedExitTime hlf hcons hD (a := a)
  have h2 : exitTimeMoment m D a 2 ≠ ⊤ :=
    exitTimeMoment_two_ne_top a hL0 (srwLaw_tail_le hL) hae
  refine ⟨hae, ?_, h2, integrable_vExitTime_toNat m D a hmean, ?_⟩
  · simpa [exitTimeMoment, expectedExitTime] using hmean
  · have hmeas : Measurable (fun x : ℕ → ℤ => ((vExitTime D x : ℕ∞) : ℝ≥0∞) ^ 2) :=
      (((measurable_of_countable (fun t : ℕ∞ => (t : ℝ≥0∞))).comp (measurable_vExitTime D))).pow_const 2
    have hI := integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable h2
    refine hI.congr (ae_of_all _ fun x => ?_)
    exact toReal_sq_toENNReal (vExitTime D x)

end FiniteExitMoment68
end MatedCRT
