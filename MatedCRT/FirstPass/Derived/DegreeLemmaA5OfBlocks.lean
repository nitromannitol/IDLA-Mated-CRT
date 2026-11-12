import MatedCRT.FirstPass.Derived.DegreeCountingBlockBounds
import MatedCRT.FirstPass.Derived.DegreeWeightedMeasureCompactSupport

/-!
# BG20 Lemma A.5 from the block degree estimate

BG20 Lemma A.5 (the degree-weighted counting bound on `B_r`, `r < 1`) follows from the cell size estimate
(Lemma 2.8, `CellSizeEstimateStmt`), the coverage estimate of the mating-of-trees coupling, and the
block degree estimate (BG20 (A.43)): for some `κ > 0`, with polynomially high probability, every block of
`N = ⌊ε^{-1/2}⌋` consecutive cells whose union meets `B_ρ` has degree sum within `ε^{-1/2 + κ}` of `6N`.
The blocks are the cells of scale `δ = Nε ≤ ε^{1/2}`, and the deterministic core is
`IsAreaParametrized.degree_counting_bounds`.

Exponents: `q = 1/(2+γ)²`, `θ = min κ (q/2)`, `α = θ/4`, `b = θ/8`; the cells of scale `δ` meeting `B_ρ`,
`ρ = (1 + r)/2`, have diameter at most `δ^q ≤ ε^θ`, `B_1 ⊆ η([-M, M])` with `M = ε^{-θ/8}`, and the error
`(2M/δ + 5)(L E + L s (12 N + E))` is at most `126 ε^{-1 + 3θ/4} ≤ ε^{-1 + θ/4}` for small `ε`.

* `floor_rpow_neg_half_bounds`: `1 ≤ ⌊ε^{-1/2}⌋ ≤ ε^{-1/2} ≤ 2⌊ε^{-1/2}⌋` for `0 < ε < 1`;
* `blockError_le`: the arithmetic of the error term;
* `lemmaA5_of_blockDegree`: the hypothesis `hA5` of `degreeMeasureConvergenceStmt_of_lemmaA5`;
* `degreeMeasureConvergenceStmt_of_blockDegree`: Lemma 2.10 from Lemma 2.8, the block degree estimate and
  the scaling inputs.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

/-- For `0 < ε < 1` the block length `N = ⌊ε^{-1/2}⌋` satisfies `1 ≤ N ≤ ε^{-1/2} ≤ 2N`, and
`ε^{-1/2} ε^{-1/2} ε = 1`, `ε^{-1/2} ε = ε^{1/2}`. -/
theorem floor_rpow_neg_half_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    1 ≤ (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) ∧ (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) ≤ ε ^ (-(1 / 2 : ℝ)) ∧
      ε ^ (-(1 / 2 : ℝ)) ≤ 2 * (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) ∧
      ε ^ (-(1 / 2 : ℝ)) * ε ^ (-(1 / 2 : ℝ)) * ε = 1 ∧
      ε ^ (-(1 / 2 : ℝ)) * ε = ε ^ (1 / 2 : ℝ) := by
  have hp1 : 1 < ε ^ (-(1 / 2 : ℝ)) :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε hε1 (by norm_num)
  have hn1 : (1 : ℝ) ≤ ⌊ε ^ (-(1 / 2 : ℝ))⌋₊ := by
    have : 1 ≤ ⌊ε ^ (-(1 / 2 : ℝ))⌋₊ := Nat.le_floor (by exact_mod_cast hp1.le)
    exact_mod_cast this
  have hfl := Nat.floor_le (zero_le_one.trans hp1.le)
  have hlt := Nat.lt_floor_add_one (ε ^ (-(1 / 2 : ℝ)))
  refine ⟨hn1, hfl, by linarith, ?_, ?_⟩
  · rw [← Real.rpow_add hε, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one,
      inv_mul_cancel₀ hε.ne']
  · rw [← Real.rpow_add_one hε.ne', show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]

/-- **Error term of BG20 Lemma A.5.** With `p² ε = 1`, `1 ≤ n ≤ p ≤ 2n`, `1 ≤ A`, `0 ≤ E ≤ p T`,
`0 ≤ s ≤ T ≤ 1` and `126 A² T ≤ a`, the error `(2A/(nε) + 5)(A E + A s (12 n + E))` is at most `ε⁻¹ a`. -/
theorem blockError_le {ε p n A E s T a : ℝ} (hε : 0 < ε) (hp : p * p * ε = 1) (hn1 : 1 ≤ n)
    (hnp : n ≤ p) (hpn : p ≤ 2 * n) (hA : 1 ≤ A) (hE : 0 ≤ E) (hET : E ≤ p * T) (hs0 : 0 ≤ s)
    (hsT : s ≤ T) (hT1 : T ≤ 1) (hkey : 126 * (A ^ 2 * T) ≤ a) :
    (2 * A / (n * ε) + 5) * (A * E + A * s * (12 * n + E)) ≤ ε⁻¹ * a := by
  have hn0 : 0 < n := by linarith
  have hp1 : 1 ≤ p := hn1.trans hnp
  have hp0 : 0 < p := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hT0 : 0 ≤ T := hs0.trans hsT
  have hF1 : 2 * A / (n * ε) + 5 ≤ 9 * (A * p) := by
    have hinv : 2 * A / (n * ε) ≤ 4 * (A * p) := by
      rw [div_le_iff₀ (mul_pos hn0 hε)]
      have h1 := mul_nonneg (sub_nonneg.2 hpn) (mul_pos hp0 hε).le
      have h2 : 0 ≤ 4 * (p * n * ε) - 2 := by linarith
      have h3 := mul_nonneg hA0 h2
      linarith
    have hAp : 1 ≤ A * p := one_le_mul_of_one_le_of_one_le hA hp1
    linarith
  have hF1' : 0 ≤ 2 * A / (n * ε) + 5 :=
    add_nonneg (div_nonneg (by linarith) (mul_pos hn0 hε).le) (by norm_num)
  have hF2 : A * E + A * s * (12 * n + E) ≤ 14 * (A * p * T) := by
    have h1 : A * E ≤ A * (p * T) := mul_le_mul_of_nonneg_left hET hA0
    have hpT : p * T ≤ p * 1 := mul_le_mul_of_nonneg_left hT1 hp0.le
    have h2 : 12 * n + E ≤ 13 * p := by linarith
    have h3 : A * s * (12 * n + E) ≤ A * T * (13 * p) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsT hA0) h2 (by linarith) (mul_nonneg hA0 hT0)
    linarith
  have hF2' : 0 ≤ A * E + A * s * (12 * n + E) :=
    add_nonneg (mul_nonneg hA0 hE) (mul_nonneg (mul_nonneg hA0 hs0) (by linarith))
  have hpp : p * p = ε⁻¹ := eq_inv_of_mul_eq_one_left hp
  calc (2 * A / (n * ε) + 5) * (A * E + A * s * (12 * n + E))
      ≤ (9 * (A * p)) * (14 * (A * p * T)) := mul_le_mul hF1 hF2 hF2' (by linarith)
    _ = 126 * (A ^ 2 * T) * (p * p) := by ring
    _ ≤ a * (p * p) := mul_le_mul_of_nonneg_right hkey (mul_pos hp0 hp0).le
    _ = ε⁻¹ * a := by rw [hpp, mul_comm]

/-- **Deterministic form of BG20 Lemma A.5 at one scale.** Let `N = ⌊ε^{-1/2}⌋`, `δ = Nε`, `z = ε^{θ/8}` with
`0 < ε < 1`, `0 < θ ≤ min κ (q/2)` and `z < min (1 - ρ) (1/126)`. If `B_1 ⊆ η([-z⁻¹, z⁻¹])`, the cells of scale
`δ` meeting `B_ρ` have diameter at most `δ^q` and degree sum within `ε^{-1/2+κ}` of `6N`, then for `0 < r ≤ ρ`,
`g` nonnegative, bounded by `ε^{-θ/8}` and `ε^{-θ/8}`-Lipschitz, and `w_k ∈ H^ε_k ∩ cl(B_r)`, the
degree-weighted counting bound of BG20 Lemma A.5 holds with `α = θ/4`. -/
theorem IsAreaParametrized.lemmaA5_bounds_of_blocks {μ : Measure ℂ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ}
    (hpar : IsAreaParametrized μ η) {ε θ κ q r ρ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hθ : 0 < θ)
    (hθκ : θ ≤ κ) (hθq : θ ≤ q / 2) (hq : 0 < q) (hr : 0 < r) (hrρ : r ≤ ρ)
    (hz : ε ^ (θ / 8) < min (1 - ρ) (1 / 126))
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-(ε ^ (-(θ / 8)))) (ε ^ (-(θ / 8))))
    (hdiam : ∀ j : ℤ, (cell ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) η j ∩ ball 0 ρ).Nonempty →
      diam (cell ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) η j) ≤ ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) ^ q)
    (hdeg : ∀ j : ℤ, (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) η j ∩ ball 0 ρ).Nonempty →
      |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
          (matedDeg m k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ))
    {g : ℂ → ℝ} (hg : ∀ x, 0 ≤ g x ∧ |g x| ≤ ε ^ (-(θ / 8)))
    (hgL : ∀ x y, |g x - g y| ≤ ε ^ (-(θ / 8)) * ‖x - y‖) {w : ℤ → ℂ}
    (hw : ∀ k ∈ cellVertices ε η (ball 0 r), w k ∈ cell ε η k ∩ closure (ball 0 r)) :
    6 * ε⁻¹ * ∫ x in ball 0 r \ thickening (ε ^ (θ / 4)) (frontier (ball 0 r)), g x ∂μ -
          ε ^ (-1 + θ / 4) ≤
        ∑' k : cellVertices ε η (ball 0 r), (matedDeg m k : ℝ) * g (w k) ∧
      ∑' k : cellVertices ε η (ball 0 r), (matedDeg m k : ℝ) * g (w k) ≤
        6 * ε⁻¹ * ∫ x in thickening (ε ^ (θ / 4)) (ball 0 r), g x ∂μ + ε ^ (-1 + θ / 4) := by
  obtain ⟨hn1, hnp, hpn, hp, hpε⟩ := floor_rpow_neg_half_bounds hε hε1
  obtain ⟨z, hz_def⟩ : ∃ z, z = ε ^ (θ / 8) := ⟨_, rfl⟩
  rw [← hz_def] at hz
  have hz0 : 0 < z := hz_def ▸ Real.rpow_pos_of_pos hε _
  have hzρ : z < 1 - ρ := hz.trans_le (min_le_left _ _)
  have hz126 : z < 1 / 126 := hz.trans_le (min_le_right _ _)
  have hz1 : z < 1 := by linarith
  have hAz : ε ^ (-(θ / 8)) * z = 1 := by
    rw [hz_def, Real.rpow_neg hε.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hε _).ne']
  have hA1 : 1 ≤ ε ^ (-(θ / 8)) :=
    (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε hε1 (by linarith)).le
  have ha : ε ^ (θ / 4) = z ^ 2 := by
    rw [hz_def, show θ / 4 = θ / 8 * ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_mul hε.le,
      Real.rpow_natCast]
  have hT : ε ^ θ = z ^ 8 := by
    rw [hz_def, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    congr 1
    push_cast
    ring
  have hz2 : z ^ 2 ≤ z :=
    calc z ^ 2 = z * z := sq z
      _ ≤ z * 1 := mul_le_mul_of_nonneg_left hz1.le hz0.le
      _ = z := mul_one z
  have hz8 : z ^ 8 < z ^ 2 :=
    calc z ^ 8 = z ^ 2 * z ^ 6 := by ring
      _ < z ^ 2 * 1 := mul_lt_mul_of_pos_left (pow_lt_one₀ hz0.le hz1 (by norm_num)) (by positivity)
      _ = z ^ 2 := mul_one _
  have hT1 : z ^ 8 ≤ 1 := pow_le_one₀ hz0.le hz1.le
  -- the block cells meeting `B_ρ` have diameter at most `ε^θ = z^8`
  have hdiam' : ∀ j : ℤ, (cell ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) η j ∩ ball 0 ρ).Nonempty →
      diam (cell ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) η j) ≤ z ^ 8 := by
    intro j hj
    have hδ0 : 0 ≤ (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε := mul_nonneg (by linarith) hε.le
    have hδ : (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε ≤ ε ^ (1 / 2 : ℝ) :=
      (mul_le_mul_of_nonneg_right hnp hε.le).trans_eq hpε
    calc diam _ ≤ ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) ^ q := hdiam j hj
      _ ≤ (ε ^ (1 / 2 : ℝ)) ^ q := Real.rpow_le_rpow hδ0 hδ hq.le
      _ = ε ^ (q / 2) := by rw [← Real.rpow_mul hε.le]; ring_nf
      _ ≤ ε ^ θ := Real.rpow_le_rpow_of_exponent_ge hε hε1.le hθq
      _ = z ^ 8 := hT
  -- the block degree bound `E = ε^{-1/2 + κ} ≤ ε^{-1/2} ε^θ`
  have hE0 : 0 ≤ ε ^ (-(1 / 2 : ℝ) + κ) := Real.rpow_nonneg hε.le _
  have hET : ε ^ (-(1 / 2 : ℝ) + κ) ≤ ε ^ (-(1 / 2 : ℝ)) * z ^ 8 := by
    rw [Real.rpow_add hε, ← hT]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hε hε1.le hθκ)
      (Real.rpow_nonneg hε.le _)
  have hkey : 126 * ((ε ^ (-(θ / 8))) ^ 2 * z ^ 8) ≤ z ^ 2 := by
    have h1 : (ε ^ (-(θ / 8))) ^ 2 * z ^ 8 = (ε ^ (-(θ / 8)) * z) ^ 2 * z ^ 6 := by ring
    rw [h1, hAz, one_pow, one_mul]
    have h4 : z ^ 4 ≤ z :=
      calc z ^ 4 = z * z ^ 3 := by ring
        _ ≤ z * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hz0.le hz1.le) hz0.le
        _ = z := mul_one z
    have h5 : 126 * z ^ 4 ≤ 1 := by linarith
    calc 126 * z ^ 6 = z ^ 2 * (126 * z ^ 4) := by ring
      _ ≤ z ^ 2 * 1 := mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = z ^ 2 := mul_one _
  have herr := blockError_le hε hp hn1 hnp hpn hA1 hE0 hET (by positivity) le_rfl hT1 hkey
  have hεα : ε ^ (-1 + θ / 4) = ε⁻¹ * z ^ 2 := by
    rw [Real.rpow_add hε, Real.rpow_neg_one, ha]
  have hN0 : 0 < ⌊ε ^ (-(1 / 2 : ℝ))⌋₊ := by
    have : (0 : ℝ) < ⌊ε ^ (-(1 / 2 : ℝ))⌋₊ := by linarith
    exact_mod_cast this
  have key := hpar.degree_counting_bounds (m := m) hε hN0
    (lt_of_lt_of_le one_pos hA1) (by positivity) (hz8.trans_eq ha.symm)
    (by rw [ha]; linarith) (zero_le_one.trans hA1) hE0 hcov hdiam' hdeg hr hrρ hg hgL hw
  rw [hεα]
  exact ⟨by linarith [key.1], by linarith [key.2]⟩

/-- **BG20 Lemma A.5 from the block degree estimate.** If the cell size estimate (Lemma 2.8) holds and, for some
`κ > 0`, with polynomially high probability every block of `N = ⌊ε^{-1/2}⌋` consecutive cells whose union
`H^{Nε}_j` meets `B_ρ` has degree sum within `ε^{-1/2 + κ}` of `6N` (BG20 (A.43)), then the degree-weighted
counting bound of BG20 Lemma A.5 holds on every ball `B_r`, `r < 1`, with polynomially high probability: this
is the hypothesis `hA5` of `degreeMeasureConvergenceStmt_of_lemmaA5`. -/
theorem lemmaA5_of_blockDegree {𝒮 : SpaceFillingSLEModel} (hcell : CellSizeEstimateStmt 𝒮)
    (hblock : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ)}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α b : ℝ, 0 < α ∧ 0 < b ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ r : ℝ, 0 < r → r < 1 → PolyHighProb S.P fun ε => {ω | ∀ g : ℂ → ℝ,
        (∀ x, 0 ≤ g x ∧ |g x| ≤ ε ^ (-b)) → (∀ x y, |g x - g y| ≤ ε ^ (-b) * ‖x - y‖) →
        ∀ w : ℤ → ℂ,
        (∀ k ∈ cellVertices ε (S.η ω) (ball 0 r), w k ∈ cell ε (S.η ω) k ∩ closure (ball 0 r)) →
        6 * ε⁻¹ * ∫ x in ball 0 r \ thickening (ε ^ α) (frontier (ball 0 r)), g x ∂S.μ ω - ε ^ (-1 + α) ≤
            ∑' k : cellVertices ε (S.η ω) (ball 0 r), (matedDeg (S.mult ε ω) k : ℝ) * g (w k) ∧
          ∑' k : cellVertices ε (S.η ω) (ball 0 r), (matedDeg (S.mult ε ω) k : ℝ) * g (w k) ≤
            6 * ε⁻¹ * ∫ x in thickening (ε ^ α) (ball 0 r), g x ∂S.μ ω + ε ^ (-1 + α)} := by
  intro γ hγ hγ2
  obtain ⟨κ, hκ, hblk⟩ := hblock γ hγ hγ2
  have hq : 0 < 1 / (2 + γ) ^ 2 := by positivity
  have hq1 : 1 / (2 + γ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hθ : 0 < min κ (1 / (2 + γ) ^ 2 / 2) := lt_min hκ (by positivity)
  refine ⟨min κ (1 / (2 + γ) ^ 2 / 2) / 4, min κ (1 / (2 + γ) ^ 2 / 2) / 8, by positivity,
    by positivity, fun Ω _ S hS r hr hr1 => ?_⟩
  obtain ⟨θ, hθ_def⟩ : ∃ θ, θ = min κ (1 / (2 + γ) ^ 2 / 2) := ⟨_, rfl⟩
  rw [← hθ_def] at hθ ⊢
  have hθκ : θ ≤ κ := hθ_def ▸ min_le_left _ _
  have hθq : θ ≤ 1 / (2 + γ) ^ 2 / 2 := hθ_def ▸ min_le_right _ _
  have hρ0 : 0 < (1 + r) / 2 := by linarith
  have hρ1 : (1 + r) / 2 < 1 := by linarith
  have hrρ : r ≤ (1 + r) / 2 := by linarith
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hMoT, hae⟩ := hS.matingOfTrees
  obtain ⟨c, hc, C, hcov⟩ := hMoT.coverage
  have hcovP : PolyHighProb S.P fun ε =>
      {ω | ball (0 : ℂ) 1 ⊆ η' ω '' Icc (-(ε ^ (-(θ / 8)))) (ε ^ (-(θ / 8)))} := by
    refine ⟨c * (θ / 8), by positivity, C, 1, one_pos, fun ε hε hε1 => ?_⟩
    have hM : 1 < ε ^ (-(θ / 8)) :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε hε1 (by linarith)
    have h := hcov _ hM
    rw [← Real.rpow_mul hε.le, show -(θ / 8) * -c = c * (θ / 8) by ring] at h
    exact h
  have hexp : 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 := by ring
  have hφ : ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      0 < (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε ∧ (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε ≤ ε ^ (1 / 2 : ℝ) := by
    refine ⟨1, one_pos, fun ε hε hε1 => ?_⟩
    obtain ⟨hn1, hnp, -, -, hpε⟩ := floor_rpow_neg_half_bounds hε hε1
    exact ⟨mul_pos (by linarith) hε, (mul_le_mul_of_nonneg_right hnp hε.le).trans_eq hpε⟩
  have hdiamP := polyHighProb_comp_of_le_rpow
    (hcell γ hγ hγ2 (1 / (2 + γ) ^ 2) ((1 + r) / 2) hq hq1 hρ0 hρ1 Ω S hS)
    (by norm_num : (0 : ℝ) < 1 / 2) hφ
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | IsAreaParametrized (S.μ ω) (S.η ω) ∧ ⇑(η' ω) = S.η ω} :=
    hS.isAreaParametrized.and (hae.mono fun ω h => h.1)
  have hm0 : 0 < min (1 - (1 + r) / 2) (1 / 126 : ℝ) := lt_min (by linarith) (by norm_num)
  have hε₁ : 0 < min 1 ((min (1 - (1 + r) / 2) (1 / 126 : ℝ)) ^ (8 / θ)) :=
    lt_min one_pos (Real.rpow_pos_of_pos hm0 _)
  refine (((hdiamP.inter hcovP).inter (hblk ((1 + r) / 2) hρ0 hρ1 Ω S hS)).inter_ae hW).mono_of_small
    hε₁ fun ε hε hεε ω hω => ?_
  obtain ⟨⟨⟨hdω, hcω⟩, hbω⟩, hpar, hηω⟩ := hω
  simp only [mem_ofPred_eq] at hdω hcω hbω
  rw [hηω] at hcω
  have hε1 : ε < 1 := hεε.trans_le (min_le_left _ _)
  have hz : ε ^ (θ / 8) < min (1 - (1 + r) / 2) (1 / 126 : ℝ) := by
    have h1 : ε ^ (θ / 8) < ((min (1 - (1 + r) / 2) (1 / 126 : ℝ)) ^ (8 / θ)) ^ (θ / 8) :=
      Real.rpow_lt_rpow hε.le (hεε.trans_le (min_le_right _ _)) (by positivity)
    rwa [← Real.rpow_mul hm0.le, show 8 / θ * (θ / 8) = 1 by field_simp, Real.rpow_one] at h1
  intro g hg hgL w hw
  exact hpar.lemmaA5_bounds_of_blocks hε hε1 hθ hθκ hθq hq hr hrρ hz hcω
    (fun j hj => by have h := (hdω j hj).2; rwa [hexp] at h) hbω hg hgL hw

/-- **Lemma 2.10 from Lemma 2.8 and the block degree estimate** (BG20 Lemma 2.7 via Lemma A.5 and
Corollary A.6): `degreeMeasureConvergenceStmt_of_lemmaA5` with its Lemma A.5 hypothesis supplied by
`lemmaA5_of_blockDegree`. -/
theorem degreeMeasureConvergenceStmt_of_blockDegree {𝒮 : SpaceFillingSLEModel}
    (hcell : CellSizeEstimateStmt 𝒮) (hscale : QuantumConeScalingInput)
    (hEnv : ConeEnvironmentScalingStep 𝒮)
    (hblock : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ)}) :
    DegreeMeasureConvergenceStmt 𝒮 :=
  degreeMeasureConvergenceStmt_of_lemmaA5 hcell hscale hEnv (lemmaA5_of_blockDegree hcell hblock)

end MatedCRT
