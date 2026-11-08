import MatedCRT.Proofs.Sec4.Prop42Closure.ConeWholePlaneSteps
import MatedCRT.Draft.Section2

/-! # The cone volume-growth input (B1, cone side) from IDLA Lemma 2.7 (closure of Proposition 4.2, z5)

IDLA Lemma 2.7 (`VolumeGrowthStmt`, `MatedCRT/Draft/Section2.lean:121`; [BG20] Lemma A.1) bounds `μ(B_δ(z))` between
`δ^{β_m}` and `δ^{β_p}` for all `z ∈ B_{1-δ}`, with polynomially high probability in `δ` (`PolyHighProb`). This file
proves the almost sure volume growth at radius `3/4` (`VolumeGrowth`) that the Step `ConeVolumeGrowthAeStep` asks for:

* Borel-Cantelli along the dyadic radii `δ_k = c 2^{-k}`: almost surely the two-sided bound holds at every `δ_k` with
  `k ≥ K`;
* interpolation between consecutive dyadic radii, which loses only constants: the lower bound keeps the exponent
  `β_m + 1` and the upper bound uses `β_p / 2`, for radii below a threshold.

Only `VolumeGrowthStmt` is used; no further literature input. -/

namespace MatedCRT

open MeasureTheory Filter Set Metric HarmonicBalls TopologicalSpace

/-- Lower interpolation: if `r ≤ δ` and `r ≤ 2^{-β_m}`, then `r^{β_m + 1} ≤ (δ/2)^{β_m}`. -/
theorem rpow_dyadic_lower_aux {r δ βm : ℝ} (hr : 0 < r) (hrδ : r ≤ δ) (hm : 0 ≤ βm)
    (hrt : r ≤ (1 / 2 : ℝ) ^ βm) : r ^ (βm + 1) ≤ (δ * (1 / 2)) ^ βm := by
  have hδ0 : 0 ≤ δ := hr.le.trans hrδ
  rw [Real.rpow_add hr, Real.rpow_one, Real.mul_rpow (x := δ) (y := 1 / 2) hδ0 (by norm_num)]
  exact mul_le_mul (Real.rpow_le_rpow hr.le hrδ hm) hrt hr.le (Real.rpow_nonneg hδ0 _)

/-- Upper interpolation: if `δ ≤ 2r` and `r ≤ 1/4`, then `δ^{β_p} ≤ r^{β_p / 2}`. -/
theorem rpow_dyadic_upper_aux {r δ βp : ℝ} (hr : 0 < r) (hδ0 : 0 ≤ δ) (hδr : δ ≤ 2 * r)
    (hr4 : r ≤ 1 / 4) (hp : 0 < βp) : δ ^ βp ≤ r ^ (βp / 2) := by
  have h2 : r ^ βp = r ^ (βp / 2) * r ^ (βp / 2) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have h4 : (1 / 4 : ℝ) ^ (βp / 2) = (1 / 2 : ℝ) ^ βp := by
    rw [show (1 / 4 : ℝ) = 1 / 2 * (1 / 2) by norm_num,
      Real.mul_rpow (x := 1 / 2) (y := 1 / 2) (by norm_num) (by norm_num),
      ← Real.rpow_add (x := 1 / 2) (by norm_num)]
    congr 1
    ring
  have h5 : (2 : ℝ) ^ βp * (1 / 2 : ℝ) ^ βp = 1 := by
    rw [← Real.mul_rpow (x := 2) (y := 1 / 2) (by norm_num) (by norm_num)]
    norm_num
  calc δ ^ βp ≤ (2 * r) ^ βp := Real.rpow_le_rpow hδ0 hδr hp.le
    _ = 2 ^ βp * r ^ βp := Real.mul_rpow (by norm_num) hr.le
    _ = 2 ^ βp * (r ^ (βp / 2) * r ^ (βp / 2)) := by rw [h2]
    _ ≤ 2 ^ βp * (r ^ (βp / 2) * (1 / 2) ^ βp) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr.le _))
        (by positivity)
      rw [← h4]
      exact Real.rpow_le_rpow hr.le hr4 (by linarith)
    _ = r ^ (βp / 2) := by rw [mul_left_comm, h5, mul_one]

/-- The dyadic power identity `(c 2^{-k})^q = c^q (2^{-q})^k`. -/
theorem rpow_dyadic_eq {c q : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    (c * (1 / 2 : ℝ) ^ k) ^ q = c ^ q * ((1 / 2 : ℝ) ^ q) ^ k := by
  rw [Real.mul_rpow (x := c) (y := (1 / 2 : ℝ) ^ k) hc (by positivity),
    ← Real.rpow_natCast (1 / 2 : ℝ) k, ← Real.rpow_mul (x := 1 / 2) (by norm_num),
    ← Real.rpow_natCast ((1 / 2 : ℝ) ^ q) k, ← Real.rpow_mul (x := 1 / 2) (by norm_num),
    mul_comm (k : ℝ) q]

/-- The majorant `C (c 2^{-k})^q` is summable in `k` for `q > 0`. -/
theorem summable_dyadic_rpow {c q C : ℝ} (hc : 0 ≤ c) (hq : 0 < q) :
    Summable (fun k : ℕ => C * (c * (1 / 2 : ℝ) ^ k) ^ q) := by
  have hr1 : (1 / 2 : ℝ) ^ q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hq
  have hg := (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) q) hr1).mul_left
    (C * c ^ q)
  refine hg.congr fun k => ?_
  rw [rpow_dyadic_eq hc k]
  ring

/-- For a radius `r` below `δ_K`, some dyadic scale `δ_{k+1} ≤ r < δ_k` has `k ≥ K`. -/
theorem exists_dyadic_index {δ : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (hδ : ∀ k, δ k = c * (1 / 2 : ℝ) ^ k)
    {K : ℕ} {r : ℝ} (hr : 0 < r) (hrK : r < δ K) :
    ∃ k : ℕ, K ≤ k ∧ δ (k + 1) ≤ r ∧ r < δ k := by
  classical
  have hcne : c ≠ 0 := hc.ne'
  have hanti : Antitone δ := fun m n hmn => by
    rw [hδ m, hδ n]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn) hc.le
  have hex : ∃ n : ℕ, δ n ≤ r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hr hc) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    rw [hδ n]
    have h := mul_lt_mul_of_pos_left hn hc
    have h' : c * (r / c) = r := by field_simp
    rw [h'] at h
    exact h.le
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    have h1 : δ 0 ≤ r := by
      have h := Nat.find_spec hex
      rw [h0] at h
      exact h
    have h2 : δ 0 < δ K := lt_of_le_of_lt h1 hrK
    exact absurd (hanti (Nat.zero_le K)) (not_le.mpr h2)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hspec : δ (k + 1) ≤ r := by
    have h := Nat.find_spec hex
    rw [hk] at h
    exact h
  refine ⟨k, ?_, hspec, ?_⟩
  · by_contra hKk
    rw [not_le] at hKk
    have h1 : δ K ≤ δ (k + 1) := hanti (Nat.succ_le_of_lt hKk)
    linarith
  · have h := Nat.find_min hex (show k < Nat.find hex by omega)
    exact not_le.mp h

/-- **Almost sure volume growth from polynomially high probability.** If the two-sided bound
`δ^{β_m} ≤ μ(B_δ(z)) ≤ δ^{β_p}` holds for all `z ∈ B_{1-δ}` with polynomially high probability in `δ`, then almost surely
`μ` has volume growth at radius `3/4`. -/
theorem ae_volumeGrowth_of_polyHighProb {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {βm βp : ℝ} (hm : 0 ≤ βm) (hp : 0 < βp)
    (hpoly : PolyHighProb P (fun δ : ℝ => {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ),
      ENNReal.ofReal (δ ^ βm) ≤ μ ω (ball z δ) ∧ μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ βp)})) :
    ∀ᵐ ω ∂P, ∃ βm' βp' : ℝ, VolumeGrowth (μ ω) (3 / 4) βm' βp' := by
  classical
  set E : ℝ → Set Ω := fun δ : ℝ => {ω | ∀ z ∈ ball (0 : ℂ) (1 - δ),
    ENNReal.ofReal (δ ^ βm) ≤ μ ω (ball z δ) ∧ μ ω (ball z δ) ≤ ENNReal.ofReal (δ ^ βp)} with hE
  obtain ⟨q, hq, C, r₀, hr₀, hbd⟩ := hpoly
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hbd' : ∀ r : ℝ, 0 < r → r < r₀ → P (E r)ᶜ ≤ ENNReal.ofReal (max C 0 * r ^ q) := fun r hr hr' =>
    (hbd r hr hr').trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hr.le q)))
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = min (r₀ / 2) (1 / 4) := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hc_def]
    exact lt_min (half_pos hr₀) (by norm_num)
  have hc_le : c ≤ r₀ / 2 := by
    rw [hc_def]
    exact min_le_left _ _
  have hc14 : c ≤ 1 / 4 := by
    rw [hc_def]
    exact min_le_right _ _
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ k, δ k = c * (1 / 2 : ℝ) ^ k :=
    ⟨fun k => c * (1 / 2 : ℝ) ^ k, fun k => rfl⟩
  have hδc : ∀ k, δ k ≤ c := fun k => by
    rw [hδ k]
    exact mul_le_of_le_one_right hc.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hδpos : ∀ k, 0 < δ k := fun k => by
    rw [hδ k]
    exact mul_pos hc (pow_pos (by norm_num) k)
  have hδ14 : ∀ k, δ k ≤ 1 / 4 := fun k => (hδc k).trans hc14
  have hδlt : ∀ k, δ k < r₀ := fun k => by linarith [hδc k]
  have hδsucc : ∀ k, δ (k + 1) = δ k * (1 / 2) := fun k => by
    rw [hδ (k + 1), hδ k, pow_succ]
    ring
  have hsum : Summable (fun k : ℕ => max C 0 * δ k ^ q) := by
    refine (summable_dyadic_rpow (C := max C 0) hc.le hq).congr fun k => ?_
    rw [hδ k]
  have hBC : ∑' k, P (E (δ k))ᶜ ≠ ⊤ := by
    have hle : ∑' k, P (E (δ k))ᶜ ≤ ∑' k, ENNReal.ofReal (max C 0 * δ k ^ q) :=
      ENNReal.tsum_le_tsum fun k => hbd' (δ k) (hδpos k) (hδlt k)
    have heq : ∑' k, ENNReal.ofReal (max C 0 * δ k ^ q) =
        ENNReal.ofReal (∑' k, max C 0 * δ k ^ q) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun k => mul_nonneg hC0 (Real.rpow_nonneg (hδpos k).le q)) hsum).symm
    exact ne_top_of_le_ne_top (by rw [heq]; exact ENNReal.ofReal_ne_top) hle
  filter_upwards [ae_eventually_notMem (s := fun k => (E (δ k))ᶜ) hBC] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.mp hω
  have hgood : ∀ k, K ≤ k → ω ∈ E (δ k) := fun k hk => by
    have h := hK k hk
    simpa using h
  refine ⟨βm + 1, βp / 2, by linarith, by linarith,
    min (δ K) ((1 / 2 : ℝ) ^ βm), lt_min (hδpos K) (by positivity), ?_⟩
  intro r hr hrlt z hz
  have hrK : r < δ K := lt_of_lt_of_le hrlt (min_le_left _ _)
  have hrt : r ≤ (1 / 2 : ℝ) ^ βm := (lt_of_lt_of_le hrlt (min_le_right _ _)).le
  obtain ⟨k, hKk, hk1, hkr⟩ := exists_dyadic_index hc hδ hr hrK
  have hk14 : δ k ≤ 1 / 4 := hδ14 k
  have hk1_14 : δ (k + 1) ≤ 1 / 4 := hδ14 (k + 1)
  have hz' := mem_ball.mp hz
  have hzk : z ∈ ball (0 : ℂ) (1 - δ k) := mem_ball.mpr (by linarith)
  have hzk1 : z ∈ ball (0 : ℂ) (1 - δ (k + 1)) := mem_ball.mpr (by linarith)
  have hEk : ω ∈ E (δ k) := hgood k hKk
  have hEk1 : ω ∈ E (δ (k + 1)) := hgood (k + 1) (by omega)
  simp only [hE, Set.mem_ofPred_eq] at hEk hEk1
  have hlow := (hEk1 z hzk1).1
  have hup := (hEk z hzk).2
  have hδr : δ k ≤ 2 * r := by
    rw [hδsucc k] at hk1
    linarith
  constructor
  · calc ENNReal.ofReal (r ^ (βm + 1)) ≤ ENNReal.ofReal ((δ (k + 1)) ^ βm) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hδsucc k]
          exact rpow_dyadic_lower_aux hr hkr.le hm hrt
      _ ≤ μ ω (ball z (δ (k + 1))) := hlow
      _ ≤ μ ω (ball z r) := measure_mono (ball_subset_ball hk1)
  · calc μ ω (ball z r) ≤ μ ω (ball z (δ k)) := measure_mono (ball_subset_ball hkr.le)
      _ ≤ ENNReal.ofReal (δ k ^ βp) := hup
      _ ≤ ENNReal.ofReal (r ^ (βp / 2)) :=
          ENNReal.ofReal_le_ofReal (rpow_dyadic_upper_aux hr (hδpos k).le hδr (by linarith) hp)

/-- **B1, cone side (`ConeVolumeGrowthAeStep`), from IDLA Lemma 2.7.** Almost surely the cone LQG measure has volume growth
at radius `3/4`, from the polynomially high probability bound `VolumeGrowthStmt` (`MatedCRT/Draft/Section2.lean:121`). -/
theorem coneVolumeGrowthAeStep_of_volumeGrowthStmt (hVG : VolumeGrowthStmt) : ConeVolumeGrowthAeStep := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ hcone
  have hγ0 : (0 : ℝ) < 2 - γ := by linarith
  have h1 : (0 : ℝ) < (2 - γ) ^ 2 / 4 := div_pos (pow_pos hγ0 2) (by norm_num)
  have h2 : (2 - γ) ^ 2 / 4 < (2 - γ) ^ 2 / 2 := by
    have := pow_pos hγ0 2
    linarith
  have h3 : (2 + γ) ^ 2 / 2 < (2 + γ) ^ 2 / 2 + 1 := by linarith
  have hpoly := hVG γ hγ hγ2 ((2 - γ) ^ 2 / 4) ((2 + γ) ^ 2 / 2 + 1) h1 h2 h3 Ω P hC hcirc μ hcone
  exact ae_volumeGrowth_of_polyHighProb (by positivity) h1 hpoly

end MatedCRT
