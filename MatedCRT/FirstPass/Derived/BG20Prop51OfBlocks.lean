import MatedCRT.FirstPass.Derived.DegreeLemmaA5OfBlocks
import MatedCRT.FirstPass.Derived.DegreeCountingUpperBorel
import MatedCRT.FirstPass.Derived.NearCellCount
import MatedCRT.FirstPass.Derived.BG20Prop51Derived

/-!
# Berestycki-Gwynne Proposition 5.1 from the block degree estimate

The upper half of the degree-weighted counting bound of BG20 Lemma A.5, (A.21), is needed in the proof of
BG20 Proposition 5.1 for every Borel set `D ⊆ B_ρ`, not only for balls. With blocks of `N = ⌊ε^{-1/2}⌋`
consecutive cells, it follows from the cell size estimate (Lemma 2.8) at scale `Nε`, the coverage of `B_1`
by `η([-ε^{-θ/8}, ε^{-θ/8}])` (mating-of-trees coupling) and the block degree estimate (A.43).

## Main results

* `IsAreaParametrized.lemmaA5_upper_of_blocks_of_subset`: the deterministic bound at one scale, for every
  `D ⊆ B_ρ`, with error `ε^{-1+θ/4}`.
* `lemmaA5Upper_of_blockDegree`: the bound with polynomially high probability, uniformly over `D ⊆ B_ρ`,
  over the test functions `g` and the points `w_k ∈ H^ε_k ∩ D`. This is the Lemma A.5 hypothesis of
  `BG20Prop51Derived.bG20Prop51_of_nearCount`.
* `bG20Prop51_of_blockDegree`: BG20 Proposition 5.1 from the Green kernel upper bound (Lemma 5.4), the crude
  Green function bound (Lemma 5.6), the volume growth, the cell size estimate (Lemma 2.8) and the block degree
  estimate (A.43).
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

/-- **Deterministic upper half of BG20 Lemma A.5 at one scale, for `D ⊆ B_ρ`.** Let `N = ⌊ε^{-1/2}⌋`,
`z = ε^{θ/8}` with `0 < ε < 1`, `0 < θ ≤ min κ (q/2)` and `z < min (1 - ρ) (1/126)`. If
`B_1 ⊆ η([-z⁻¹, z⁻¹])` and the cells of scale `Nε` meeting `B_ρ` have diameter at most `(Nε)^q` and degree
sum within `ε^{-1/2+κ}` of `6N`, then for every `D ⊆ B_ρ`, every `g ≥ 0` bounded by `ε^{-θ/8}` and
`ε^{-θ/8}`-Lipschitz, and every choice of `w_k ∈ H^ε_k`, the degree-weighted counting sum over `V^ε(D)` is at
most `6ε⁻¹ ∫_{B_{ε^{θ/4}}(D)} g dμ + ε^{-1+θ/4}`. -/
theorem IsAreaParametrized.lemmaA5_upper_of_blocks_of_subset {μ : Measure ℂ} {η : ℝ → ℂ}
    {m : ℤ → ℤ → ℕ} (hpar : IsAreaParametrized μ η) {ε θ κ q ρ : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hθ : 0 < θ) (hθκ : θ ≤ κ) (hθq : θ ≤ q / 2) (hq : 0 < q)
    (hz : ε ^ (θ / 8) < min (1 - ρ) (1 / 126))
    (hcov : ball (0 : ℂ) 1 ⊆ η '' Icc (-(ε ^ (-(θ / 8)))) (ε ^ (-(θ / 8))))
    (hdiam : ∀ j : ℤ, (cell ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) η j ∩ ball 0 ρ).Nonempty →
      diam (cell ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) η j) ≤ ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℝ) * ε) ^ q)
    (hdeg : ∀ j : ℤ, (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) η j ∩ ball 0 ρ).Nonempty →
      |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
          (matedDeg m k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ))
    {D : Set ℂ} (hDρ : D ⊆ ball 0 ρ) {g : ℂ → ℝ} (hg : ∀ x, 0 ≤ g x ∧ |g x| ≤ ε ^ (-(θ / 8)))
    (hgL : ∀ x y, |g x - g y| ≤ ε ^ (-(θ / 8)) * ‖x - y‖) {w : ℤ → ℂ}
    (hw : ∀ k ∈ cellVertices ε η D, w k ∈ cell ε η k) :
    ∑' k : cellVertices ε η D, (matedDeg m k : ℝ) * g (w k) ≤
      6 * ε⁻¹ * ∫ x in thickening (ε ^ (θ / 4)) D, g x ∂μ + ε ^ (-1 + θ / 4) := by
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
  have key := hpar.tsum_degree_counting_le_of_subset (m := m) hε hN0
    (lt_of_lt_of_le one_pos hA1) (by positivity) (hz8.trans_eq ha.symm)
    (by rw [ha]; linarith) (zero_le_one.trans hA1) hE0 hcov hdiam' hdeg hDρ hg hgL hw
  rw [hεα]
  linarith

/-- **Upper half of BG20 Lemma A.5 for Borel `D ⊆ B_ρ`, from the block degree estimate.** If the cell size
estimate (Lemma 2.8) holds and, for some `κ > 0`, with polynomially high probability every block of
`N = ⌊ε^{-1/2}⌋` consecutive cells whose union `H^{Nε}_j` meets `B_ρ` has degree sum within `ε^{-1/2+κ}` of
`6N` (BG20 (A.43)), then there are `α₁, b > 0` depending only on `γ` such that, for every `ρ < 1`, with
polynomially high probability, for every measurable `D ⊆ B_ρ`, every `g ≥ 0` bounded by `ε^{-b}` and
`ε^{-b}`-Lipschitz and every choice of `w_k ∈ H^ε_k ∩ D`,
`∑_{k ∈ V^ε(D)} deg(k) g(w_k) ≤ 6ε⁻¹ ∫_{B_{ε^{α₁}}(D)} g dμ + ε^{-1+α₁}`. -/
theorem lemmaA5Upper_of_blockDegree {𝒮 : SpaceFillingSLEModel} (hcell : CellSizeEstimateStmt 𝒮)
    (hblock : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ)}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α₁ b : ℝ, 0 < α₁ ∧ 0 < b ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 → PolyHighProb S.P fun ε => {ω | ∀ D : Set ℂ, MeasurableSet D →
        D ⊆ ball 0 ρ → ∀ g : ℂ → ℝ, (∀ x, 0 ≤ g x ∧ |g x| ≤ ε ^ (-b)) →
        (∀ x y, |g x - g y| ≤ ε ^ (-b) * ‖x - y‖) →
        ∀ w : ℤ → ℂ, (∀ k ∈ cellVertices ε (S.η ω) D, w k ∈ cell ε (S.η ω) k ∩ D) →
        ∑' k : cellVertices ε (S.η ω) D, (matedDeg (S.mult ε ω) k : ℝ) * g (w k) ≤
          6 * ε⁻¹ * ∫ x in thickening (ε ^ α₁) D, g x ∂S.μ ω + ε ^ (-1 + α₁)} := by
  intro γ hγ hγ2
  obtain ⟨κ, hκ, hblk⟩ := hblock γ hγ hγ2
  have hq : 0 < 1 / (2 + γ) ^ 2 := by positivity
  have hq1 : 1 / (2 + γ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hθ : 0 < min κ (1 / (2 + γ) ^ 2 / 2) := lt_min hκ (by positivity)
  refine ⟨min κ (1 / (2 + γ) ^ 2 / 2) / 4, min κ (1 / (2 + γ) ^ 2 / 2) / 8, by positivity,
    by positivity, fun Ω _ S hS ρ hρ hρ1 => ?_⟩
  obtain ⟨θ, hθ_def⟩ : ∃ θ, θ = min κ (1 / (2 + γ) ^ 2 / 2) := ⟨_, rfl⟩
  rw [← hθ_def] at hθ ⊢
  have hθκ : θ ≤ κ := hθ_def ▸ min_le_left _ _
  have hθq : θ ≤ 1 / (2 + γ) ^ 2 / 2 := hθ_def ▸ min_le_right _ _
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
    (hcell γ hγ hγ2 (1 / (2 + γ) ^ 2) ρ hq hq1 hρ hρ1 Ω S hS)
    (by norm_num : (0 : ℝ) < 1 / 2) hφ
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | IsAreaParametrized (S.μ ω) (S.η ω) ∧ ⇑(η' ω) = S.η ω} :=
    hS.isAreaParametrized.and (hae.mono fun ω h => h.1)
  have hm0 : 0 < min (1 - ρ) (1 / 126 : ℝ) := lt_min (by linarith) (by norm_num)
  have hε₁ : 0 < min 1 ((min (1 - ρ) (1 / 126 : ℝ)) ^ (8 / θ)) :=
    lt_min one_pos (Real.rpow_pos_of_pos hm0 _)
  refine (((hdiamP.inter hcovP).inter (hblk ρ hρ hρ1 Ω S hS)).inter_ae hW).mono_of_small
    hε₁ fun ε hε hεε ω hω => ?_
  obtain ⟨⟨⟨hdω, hcω⟩, hbω⟩, hpar, hηω⟩ := hω
  simp only [mem_ofPred_eq] at hdω hcω hbω
  rw [hηω] at hcω
  have hε1 : ε < 1 := hεε.trans_le (min_le_left _ _)
  have hz : ε ^ (θ / 8) < min (1 - ρ) (1 / 126 : ℝ) := by
    have h1 : ε ^ (θ / 8) < ((min (1 - ρ) (1 / 126 : ℝ)) ^ (8 / θ)) ^ (θ / 8) :=
      Real.rpow_lt_rpow hε.le (hεε.trans_le (min_le_right _ _)) (by positivity)
    rwa [← Real.rpow_mul hm0.le, show 8 / θ * (θ / 8) = 1 by field_simp, Real.rpow_one] at h1
  intro D _ hDρ g hg hgL w hw
  exact hpar.lemmaA5_upper_of_blocks_of_subset hε hε1 hθ hθκ hθq hq hz hcω
    (fun j hj => by have h := (hdω j hj).2; rwa [hexp] at h) hbω hDρ hg hgL fun k hk => (hw k hk).1

/-- **BG20 Proposition 5.1 from the block degree estimate.** The Green kernel upper bound (Lemma 5.4), the
crude Green function bound (Lemma 5.6), the volume growth, the cell size estimate (Lemma 2.8) and the block
degree estimate (A.43) give the moment bound for exit times of BG20 Proposition 5.1: the near-vertex count
(5.41) comes from the volume growth and Lemma 2.8, and the upper half of Lemma A.5 for Borel `D ⊆ B_ρ` from
`lemmaA5Upper_of_blockDegree`. -/
theorem bG20Prop51_of_blockDegree {𝒮 : SpaceFillingSLEModel} (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h27 : VolumeGrowthStmt) (hcell : CellSizeEstimateStmt 𝒮)
    (hblock : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ j : ℤ,
        (cell (⌊ε ^ (-(1 / 2 : ℝ))⌋₊ * ε) (S.η ω) j ∩ ball 0 ρ).Nonempty →
        |(∑ k ∈ Finset.Ioc ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * (j - 1)) ((⌊ε ^ (-(1 / 2 : ℝ))⌋₊ : ℤ) * j),
            (matedDeg (S.mult ε ω) k : ℝ)) - 6 * ⌊ε ^ (-(1 / 2 : ℝ))⌋₊| ≤ ε ^ (-(1 / 2 : ℝ) + κ)}) :
    BG20Prop51 𝒮 :=
  BG20Prop51Derived.bG20Prop51_of_nearCount h214 h215
    (fun γ hγ hγ2 β hβ => ⟨nearCountExponent γ β, nearCountExponent_pos hγ hγ2 hβ,
      fun _ hρ hρ1 _ _ _ hS =>
        MatedCRTEnv.IsValid.polyHighProb_card_cellVertices_ball_le_exponent h27 hcell hS hγ hγ2 hβ hρ hρ1⟩)
    (lemmaA5Upper_of_blockDegree hcell hblock)

end MatedCRT
