import MatedCRT.Draft.Section2

/-!
# FIRST PASS S4S6c, HVolCutoff68: the random-radius volume bounds from Lemma 2.7

Source. `VolumeGrowthStmt` (Draft/Section2.lean:121; paper Lemma 2.7, BG20 Lemma A.1) bounds the quantum ball masses
`μ(B_δ(z))` from below by `δ^{β⁻}` for all `z ∈ B_{1-δ}`, outside an event of polynomially small probability as
`δ → 0` (`HarmonicBalls.PolyHighProb`). The consumer `hone_exitQ_walk_of_env_direct_repaired` (HspRepair68.lean)
needs the same bound at the random radii `c₀R_k` and `R_k/4` (its binders `hVolC`, `hVolY`). The route
:
1. take an auxiliary exponent `(2+γ)²/2 < β₀ < β⁻` and apply `VolumeGrowthStmt` with exponent `β₀`;
2. Borel–Cantelli over the dyadic scales `2^{-m}`: almost surely the dyadic event holds for all large `m`;
3. for `δ` below a random cutoff `t(μ) > 0`, take the dyadic scale `q ∈ [δ/2, δ)`; then
   `μ(B_δ(z)) ≥ μ(B_q(z)) ≥ q^{β₀} ≥ (δ/2)^{β₀} ≥ δ^{β⁻}` once `δ^{β⁻-β₀} ≤ 2^{-β₀}`.

The cutoff is stated almost surely (`volume_lower_cutoff_ae`, `volume_bounds_ae`), never for every `ω`.

Limit. The cutoff is small and random, so the two bounds below hold only at radii `R/4 < t(μ)`. The walk radii of the
consumer satisfy only `r² ≤ R_k ≤ 1` (`hRr`, HspRepair68.lean), so `VolumeGrowthStmt` does not give `hVolC`, `hVolY`
for every walk event (the all-scales coefficient-one bound is not in the sources). Reported in
-/
namespace MatedCRT
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace Lemma68Cutoff

/-- **Borel–Cantelli on dyadic scales (Armstrong–Kuusi–Mourrat, polynomially high probability).** If the events
`E r` hold with polynomially high probability as `r → 0` (`PolyHighProb P E`), then for `P`-almost every `ω` the
event `E (2^{-m})` holds for all large `m`. The complements have summable probabilities `≤ |C| (2^{-m})^p`
(geometric series with ratio `(1/2)^p`), and `ae_eventually_notMem` is the Borel–Cantelli lemma for outer measures. -/
theorem ae_eventually_dyadic_of_polyHighProb {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (hE : HarmonicBalls.PolyHighProb P E) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ω ∈ E ((1 / 2 : ℝ) ^ m) := by
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := hE
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (1 / 2 : ℝ) < 1)
  have hq0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ p := by positivity
  have hq1 : (1 / 2 : ℝ) ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hterm : ∀ n : ℕ, P (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ ≤ ENNReal.ofReal (|C| * ((1 / 2 : ℝ) ^ p) ^ n) := by
    intro n
    have hr : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + N₀) := by positivity
    have hrr : (1 / 2 : ℝ) ^ (n + N₀) < r₀ :=
      lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left N₀ n)) hN₀
    have hm : (1 / 2 : ℝ) ^ (n + N₀) ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right n N₀)
    have hpow : ((1 / 2 : ℝ) ^ n) ^ p = ((1 / 2 : ℝ) ^ p) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_natCast]
    have hrq : ((1 / 2 : ℝ) ^ (n + N₀)) ^ p ≤ ((1 / 2 : ℝ) ^ p) ^ n := by
      rw [← hpow]; exact Real.rpow_le_rpow (by positivity) hm hp.le
    refine (hb _ hr hrr).trans (ENNReal.ofReal_le_ofReal ?_)
    exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      (mul_le_mul_of_nonneg_left hrq (abs_nonneg C))
  have hsumm : Summable (fun n : ℕ => |C| * ((1 / 2 : ℝ) ^ p) ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hsum : (∑' n : ℕ, P (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ) ≠ ∞ := by
    have hle : (∑' n : ℕ, P (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ)
        ≤ ENNReal.ofReal (∑' n : ℕ, |C| * ((1 / 2 : ℝ) ^ p) ^ n) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
      exact ENNReal.tsum_le_tsum hterm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  filter_upwards [ae_eventually_notMem (s := fun n : ℕ => (E ((1 / 2 : ℝ) ^ (n + N₀)))ᶜ) hsum] with ω hω
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hω
  refine ⟨N' + N₀, fun m hm => ?_⟩
  have h := hN' (m - N₀) (by omega)
  have hm' : m - N₀ + N₀ = m := by omega
  rw [hm'] at h
  simpa using h

/-- **Lower volume bound below a random cutoff, almost surely (Lemma 2.7 at dyadic scales plus Borel–Cantelli).**
For the quantum cone field `μ` and `γ ∈ (0,2)`, every `β > (2+γ)²/2` has an almost surely positive cutoff `t(ω)`
with `μ(B_δ(z)) ≥ δ^β` for all `0 < δ < t(ω)` and all `z ∈ B_{1-δ}`. The cutoff depends on `ω` (the field) and is
never claimed for every `ω`. -/
theorem volume_lower_cutoff_ae {γ β : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    (hVG : VolumeGrowthStmt) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ) :
    ∀ᵐ ω ∂P, ∃ t : ℝ, 0 < t ∧ ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ β) ≤ μ ω (ball z δ) := by
  set β₀ : ℝ := ((2 + γ) ^ 2 / 2 + β) / 2 with hβ₀def
  have hβ₀ : (2 + γ) ^ 2 / 2 < β₀ := by rw [hβ₀def]; linarith
  have hβ₀β : β₀ < β := by rw [hβ₀def]; linarith
  have hβ₀pos : 0 < β₀ := lt_trans (by positivity) hβ₀
  have h2γ : 0 < 2 - γ := by linarith
  have hβp : 0 < (2 - γ) ^ 2 / 4 := by positivity
  have hβpl : (2 - γ) ^ 2 / 4 < (2 - γ) ^ 2 / 2 := by
    have : 0 < (2 - γ) ^ 2 := by positivity
    linarith
  have hE := hVG γ hγ0 hγ2 ((2 - γ) ^ 2 / 4) β₀ hβp hβpl hβ₀ Ω P hC hcirc μ hcone
  filter_upwards [ae_eventually_dyadic_of_polyHighProb hE] with ω hω
  obtain ⟨N, hN⟩ := hω
  refine ⟨min ((1 / 2 : ℝ) ^ N) ((1 / 2 : ℝ) ^ (β₀ / (β - β₀))), lt_min (by positivity) (by positivity), ?_⟩
  intro δ hδ0 hδt z hz
  have hδN : δ < (1 / 2 : ℝ) ^ N := lt_of_lt_of_le hδt (min_le_left _ _)
  have hδe : δ < (1 / 2 : ℝ) ^ (β₀ / (β - β₀)) := lt_of_lt_of_le hδt (min_le_right _ _)
  have hδ1 : δ < 1 := lt_of_lt_of_le hδN (pow_le_one₀ (by norm_num) (by norm_num))
  -- `δ^(β - β₀) ≤ (1/2)^β₀`
  have hpow : δ ^ (β - β₀) ≤ (1 / 2 : ℝ) ^ β₀ := by
    calc δ ^ (β - β₀) ≤ ((1 / 2 : ℝ) ^ (β₀ / (β - β₀))) ^ (β - β₀) :=
          Real.rpow_le_rpow hδ0.le hδe.le (by linarith)
      _ = (1 / 2 : ℝ) ^ β₀ := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          congr 1
          exact div_mul_cancel₀ β₀ (sub_pos.mpr hβ₀β).ne'
  -- the dyadic scale `q = 2^{-(n+1)} ∈ [δ/2, δ)`
  have h1 : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
  have hA : 1 < (2 : ℝ) ^ (n + 1) * δ := (div_lt_iff₀ hδ0).mp hn2
  have hB : (2 : ℝ) ^ n * δ ≤ 1 := (le_div_iff₀ hδ0).mp hn1
  have hqinv : (1 / 2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (n + 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hqpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  have h2n1 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hqδ : (1 / 2 : ℝ) ^ (n + 1) < δ := by
    by_contra hcon
    have hc : δ ≤ (1 / 2 : ℝ) ^ (n + 1) := not_lt.mp hcon
    have := mul_le_mul_of_nonneg_right hc (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n + 1))
    rw [hqinv] at this
    linarith
  have hhalf : δ / 2 ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    by_contra hcon
    have hc : (1 / 2 : ℝ) ^ (n + 1) < δ / 2 := not_le.mp hcon
    have := mul_lt_mul_of_pos_right hc (pow_pos (by norm_num : (0 : ℝ) < 2) (n + 1))
    rw [hqinv] at this
    have h3 : δ / 2 * (2 : ℝ) ^ (n + 1) = δ * 2 ^ n := by rw [h2n1]; ring
    linarith
  have hNn : N ≤ n + 1 := by
    by_contra hcon
    have hc : n + 1 < N := not_le.mp hcon
    have h2N : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hc.le
    have hNδ : (2 : ℝ) ^ N * δ < 1 := by
      have := mul_lt_mul_of_pos_left hδN (pow_pos (by norm_num : (0 : ℝ) < 2) N)
      have hh : (2 : ℝ) ^ N * (1 / 2 : ℝ) ^ N = 1 := by rw [← mul_pow]; norm_num
      linarith
    have := mul_le_mul_of_nonneg_right h2N hδ0.le
    linarith
  -- the dyadic event at scale `q` and the monotone comparison
  set q : ℝ := (1 / 2 : ℝ) ^ (n + 1) with hqdef
  have hωq : ∀ w ∈ ball (0 : ℂ) (1 - q),
      ENNReal.ofReal (q ^ β₀) ≤ μ ω (ball w q) := fun w hw => (hN (n + 1) hNn w hw).1
  have hzq : z ∈ ball (0 : ℂ) (1 - q) := by
    rw [mem_ball_zero_iff] at hz ⊢
    linarith
  have hlow : ENNReal.ofReal (q ^ β₀) ≤ μ ω (ball z q) := hωq z hzq
  have hmono : μ ω (ball z q) ≤ μ ω (ball z δ) := measure_mono (ball_subset_ball hqδ.le)
  have hdelta : δ ^ β ≤ q ^ β₀ := by
    have hsplit : δ ^ β = δ ^ β₀ * δ ^ (β - β₀) := by
      rw [← Real.rpow_add hδ0]; congr 1; ring
    have hhalfpow : (δ / 2) ^ β₀ = δ ^ β₀ * (1 / 2 : ℝ) ^ β₀ := by
      rw [show δ / 2 = δ * (1 / 2) by ring, Real.mul_rpow hδ0.le (by norm_num)]
    calc δ ^ β = δ ^ β₀ * δ ^ (β - β₀) := hsplit
      _ ≤ δ ^ β₀ * (1 / 2 : ℝ) ^ β₀ := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (δ / 2) ^ β₀ := hhalfpow.symm
      _ ≤ q ^ β₀ := Real.rpow_le_rpow (by positivity) hhalf hβ₀pos.le
  exact (ENNReal.ofReal_le_ofReal hdelta).trans (hlow.trans hmono)

/-- **The two local volume bounds below the cutoff (deterministic).** Let `ν` satisfy the cutoff bound of
`volume_lower_cutoff_ae` below `t`. If `0 < R`, `R/4 < t`, `c₀ ≤ 1/4`, then `(c₀R)^{β} ≤ ν(B_{c₀R}(z))` at every
centre `‖z‖ < 1 - R/4` (the consumer's `hVolC`, centre `vertexPoint (ω (T k ω))` by `hx1`) and
`(R/4)^{β} ≤ ν(B_{R/4}(y))` at every `y ∈ B_{1-R/4}` (the consumer's `hVolY`). -/
theorem volume_bounds_of_cutoff {ν : Measure ℂ} {β t c0 R : ℝ} (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 4) (hR : 0 < R)
    (hcut : ∀ δ : ℝ, 0 < δ → δ < t → ∀ z ∈ ball (0 : ℂ) (1 - δ), ENNReal.ofReal (δ ^ β) ≤ ν (ball z δ))
    (hRt : R / 4 < t) {z : ℂ} (hz : ‖z‖ < 1 - R / 4) :
    ENNReal.ofReal ((c0 * R) ^ β) ≤ ν (ball z (c0 * R)) ∧
      ∀ y ∈ ball (0 : ℂ) (1 - R / 4), ENNReal.ofReal ((R / 4) ^ β) ≤ ν (ball y (R / 4)) := by
  have hcR : c0 * R ≤ R / 4 := by nlinarith
  refine ⟨hcut (c0 * R) (by positivity) (lt_of_le_of_lt hcR hRt) z ?_,
    fun y hy => hcut (R / 4) (by positivity) hRt y hy⟩
  rw [mem_ball_zero_iff]
  linarith

/-- **Almost-sure form of the random-radius volume bounds.** For `P`-almost every `ω` there is a cutoff `t > 0`
such that, for every radius `R` with `0 < R`, `R/4 < t`, every centre `‖z‖ < 1 - R/4` and `y ∈ B_{1-R/4}`, the two
bounds of `volume_bounds_of_cutoff` hold for the field `μ ω`. The statement is almost sure in `ω` (the field):
the cutoff is random and is not claimed for every `ω`. -/
theorem volume_bounds_ae {γ β c0 : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    (hc0 : 0 < c0) (hc0' : c0 ≤ 1 / 4)
    (hVG : VolumeGrowthStmt) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hcone : IsConeField γ P hC hcirc μ) :
    ∀ᵐ ω ∂P, ∃ t : ℝ, 0 < t ∧ ∀ R : ℝ, 0 < R → R / 4 < t → ∀ z : ℂ, ‖z‖ < 1 - R / 4 →
      ENNReal.ofReal ((c0 * R) ^ β) ≤ μ ω (ball z (c0 * R)) ∧
        ∀ y ∈ ball (0 : ℂ) (1 - R / 4), ENNReal.ofReal ((R / 4) ^ β) ≤ μ ω (ball y (R / 4)) := by
  filter_upwards [volume_lower_cutoff_ae hγ0 hγ2 hβ hVG Ω P hC hcirc μ hcone] with ω hω
  obtain ⟨t, ht, hcut⟩ := hω
  exact ⟨t, ht, fun R hR hRt z hz => volume_bounds_of_cutoff hc0 hc0' hR hcut hRt hz⟩

end Lemma68Cutoff
end MatedCRT

#print axioms MatedCRT.Lemma68Cutoff.ae_eventually_dyadic_of_polyHighProb
#print axioms MatedCRT.Lemma68Cutoff.volume_lower_cutoff_ae
#print axioms MatedCRT.Lemma68Cutoff.volume_bounds_of_cutoff
#print axioms MatedCRT.Lemma68Cutoff.volume_bounds_ae
