import MatedCRT.FirstPass.Derived.CellInballOfSegmentBalls

/-!
# The lower cell diameter bound from the volume growth of the LQG measure

Lemma 2.8 (BG20 Lemma 2.4) has two halves. The lower half, `diam(H^ε_a) ≥ ε^{2/(2-γ)² + ζ}` for
every cell meeting `B_ρ`, follows from the upper volume bound of Lemma 2.7 (BG20 Lemma A.1):
choose `β⁺ ∈ (1/a, (2-γ)²/2)` with `a = 2/(2-γ)² + ζ`; with polynomially high probability every
Euclidean ball of radius `δ = ε^a` centred in `B_ρ` has `μ_h`-mass at most `δ^{β⁺} = ε^{aβ⁺} < ε`,
so it cannot contain a cell, each cell having `μ_h`-mass `ε` (BG20, proof of Lemma 2.4).

* `MatedCRTEnv.IsValid.polyHighProb_cellDiam_lower`: the lower half from `VolumeGrowthStmt`;
* `cellSizeEstimateStmt_of_volumeGrowth`: `CellSizeEstimateStmt` from `VolumeGrowthStmt` and the
  upper half (GMS19 Lemma 2.7).
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

/-- **Lower cell diameter bound** (BG20 Lemma 2.4, lower half): from the volume growth estimate
(Lemma 2.7), with polynomially high probability as `ε → 0`, every cell `H^ε_k` meeting `B_ρ` has
diameter at least `ε^{2/(2-γ)² + ζ}`. -/
theorem MatedCRTEnv.IsValid.polyHighProb_cellDiam_lower {𝒮 : SpaceFillingSLEModel} {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (h27 : VolumeGrowthStmt)
    (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) {ζ ρ : ℝ} (hζ : 0 < ζ) (hρ1 : ρ < 1) :
    PolyHighProb S.P fun ε => {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
      ε ^ (2 / (2 - γ) ^ 2 + ζ) ≤ diam (cell ε (S.η ω) k)} := by
  set a : ℝ := 2 / (2 - γ) ^ 2 + ζ with ha_def
  have h2γ : 0 < (2 - γ) ^ 2 := by
    have : 0 < 2 - γ := by linarith
    positivity
  have ha : 0 < a := by positivity
  have hinv : a⁻¹ < (2 - γ) ^ 2 / 2 := by
    rw [inv_lt_comm₀ ha (by positivity), inv_div]
    linarith
  set βp : ℝ := (a⁻¹ + (2 - γ) ^ 2 / 2) / 2 with hβp_def
  have hβp0 : 0 < βp := by positivity
  have hβp1 : a⁻¹ < βp := by linarith
  have hβp2 : βp < (2 - γ) ^ 2 / 2 := by linarith
  have haβ : 1 < a * βp := by
    have := mul_lt_mul_of_pos_left hβp1 ha
    rwa [mul_inv_cancel₀ ha.ne'] at this
  have hvol := h27 γ hγ hγ2 βp ((2 + γ) ^ 2 / 2 + 1) hβp0 hβp2 (by linarith) Ω S.P S.hC
    S.hcirc S.μ ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | IsAreaParametrized (S.μ ω) (S.η ω)} := hS.isAreaParametrized
  have hρ' : 0 < 1 - ρ := by linarith
  set ε₁ : ℝ := min 1 ((1 - ρ) ^ (1 / a)) with hε₁_def
  have hε₁ : 0 < ε₁ := lt_min one_pos (Real.rpow_pos_of_pos hρ' _)
  refine ((polyHighProb_comp_rpow hvol ha).inter_ae hW).mono_of_small hε₁
    fun ε hε hεε ω hω => ?_
  obtain ⟨hvolω, hpar⟩ := hω
  have hε1 : ε < 1 := hεε.trans_le (min_le_left _ _)
  have hδρ : ε ^ a < 1 - ρ := by
    have h1 : ε ^ a < ((1 - ρ) ^ (1 / a)) ^ a :=
      Real.rpow_lt_rpow hε.le (hεε.trans_le (min_le_right _ _)) ha
    rwa [← Real.rpow_mul hρ'.le, one_div_mul_cancel ha.ne', Real.rpow_one] at h1
  rintro k ⟨w, hwc, hw0⟩
  by_contra hlt
  rw [not_le] at hlt
  have hbdd : Bornology.IsBounded (cell ε (S.η ω) k) :=
    (isCompact_Icc.image hpar.1).isBounded
  have hsub : cell ε (S.η ω) k ⊆ ball w (ε ^ a) := fun y hy =>
    mem_ball.2 (lt_of_le_of_lt (dist_le_diam_of_mem hbdd hy hwc) hlt)
  have hlt' : ε * ((k : ℝ) - 1) < ε * k := mul_lt_mul_of_pos_left (by linarith) hε
  have hμcell : S.μ ω (cell ε (S.η ω) k) = ENNReal.ofReal ε := by
    rw [cell, hpar.2.2.2 _ _ hlt']
    congr 1
    ring
  have hw1 : w ∈ ball (0 : ℂ) (1 - ε ^ a) := by
    rw [mem_ball] at hw0 ⊢
    linarith
  have hball := (hvolω w hw1).2
  have hle : ENNReal.ofReal ε ≤ ENNReal.ofReal ((ε ^ a) ^ βp) :=
    hμcell ▸ (measure_mono hsub).trans hball
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity), ← Real.rpow_mul hε.le] at hle
  have hlt2 : ε ^ (a * βp) < ε ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_gt hε hε1 haβ
  rw [Real.rpow_one] at hlt2
  linarith

/-- **Lemma 2.8 from Lemma 2.7 and the upper cell diameter bound.** `CellSizeEstimateStmt` from the
volume growth estimate `VolumeGrowthStmt` (which gives the lower half) and the upper half
`diam(H^ε_a) ≤ ε^{2/(2+γ)² - ζ}` (GMS19 Lemma 2.7) with polynomially high probability. -/
theorem cellSizeEstimateStmt_of_volumeGrowth {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt)
    (hup : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ζ ρ : ℝ, 0 < ζ → ζ < 1 → 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        PolyHighProb S.P fun ε => {ω | ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
          diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - ζ)}) :
    CellSizeEstimateStmt 𝒮 := by
  intro γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω _ S hS
  exact ((hS.polyHighProb_cellDiam_lower h27 hγ hγ2 hζ hρ1).inter
    (hup γ hγ hγ2 ζ ρ hζ hζ1 hρ hρ1 Ω S hS)).mono fun ε ω hω k hk =>
      ⟨hω.1 k hk, hω.2 k hk⟩

end MatedCRT
