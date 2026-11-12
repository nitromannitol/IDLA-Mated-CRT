import MatedCRT.FirstPass.Derived.CountingMeasureOfCellSize

/-!
# Number of cells near a point (BG20, (5.41))

In the proof of BG20 Lemma 5.8 the vertices `y ∈ V^ε(D)` with `η(y)` close to `η(x)` are counted:
"since the cells of `𝒢^ε` have `μ_h`-mass `ε`, it is easily seen from Lemmas A.1 and 2.4 that there
exists `α₀ = α₀(β, γ) > 0` such that with polynomially high probability as `ε → 0`, we have
`sup_{z ∈ B_ρ} #V^ε(B_{ε^β}(z)) ≤ ε^{-1+α₀}`".

* `IsAreaParametrized.ofReal_mul_card_le`: if the cells of the finitely many vertices of `s` lie in
  `U`, then `ε · #s ≤ μ(U)` (each cell has mass `ε` and distinct cells meet in null sets);
* `MatedCRTEnv.IsValid.polyHighProb_card_cellVertices_ball_le`: the count (5.41) from the volume
  growth estimate (Lemma 2.7 = BG20 Lemma A.1, upper half) and the cell size estimate
  (Lemma 2.8 = BG20 Lemma 2.4, upper half). It is stated for every finite set of vertices whose cells
  meet `B_{ε^β}(z)`, which is the form consumed by the near/typical split of the exit-time Green sum.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls

namespace MatedCRT

variable {μ : Measure ℂ} {η : ℝ → ℂ}

/-- **Counting by mass.** If the cells of the vertices of a finite set `s` lie in `U`, then
`ε · #s ≤ μ(U)`: each cell has `μ`-mass `ε` and two distinct cells meet in a `μ`-null set. -/
theorem IsAreaParametrized.ofReal_mul_card_le (hpar : IsAreaParametrized μ η) {ε : ℝ}
    (hε : 0 < ε) (s : Finset ℤ) {U : Set ℂ} (hU : ∀ k ∈ s, cell ε η k ⊆ U) :
    ENNReal.ofReal (ε * s.card) ≤ μ U := by
  have hunion : μ (⋃ k ∈ s, cell ε η k) = ∑ k ∈ s, μ (cell ε η k) :=
    measure_biUnion_finset₀ (fun j _ k _ hjk => hpar.measure_cell_inter hε hjk)
      (fun k _ => (isCompact_cell hpar.1 ε k).isClosed.measurableSet.nullMeasurableSet)
  calc ENNReal.ofReal (ε * s.card) = ∑ k ∈ s, μ (cell ε η k) := by
        simp only [hpar.measure_cell hε, Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul hε.le, mul_comm, ENNReal.ofReal_natCast]
    _ = μ (⋃ k ∈ s, cell ε η k) := hunion.symm
    _ ≤ μ U := measure_mono (iUnion₂_subset hU)

/-- **BG20 (5.41).** Let `0 < γ < 2`, `β > 0` and `0 < ρ < 1`. Under the volume growth estimate
(Lemma 2.7) and the cell size estimate (Lemma 2.8) there is `α₀ > 0` such that with polynomially high
probability as `ε → 0`, for every `z ∈ B_ρ`, every finite set of vertices whose cells meet
`B_{ε^β}(z)` has at most `ε^{-1+α₀}` elements. -/
theorem MatedCRTEnv.IsValid.polyHighProb_card_cellVertices_ball_le {𝒮 : SpaceFillingSLEModel}
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} (h27 : VolumeGrowthStmt)
    (hcell : CellSizeEstimateStmt 𝒮) (hS : S.IsValid 𝒮 γ) (hγ : 0 < γ) (hγ2 : γ < 2) {β ρ : ℝ}
    (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ PolyHighProb S.P fun ε => {ω | ∀ z ∈ ball (0 : ℂ) ρ, ∀ s : Finset ℤ,
      (↑s : Set ℤ) ⊆ cellVertices ε (S.η ω) (ball z (ε ^ β)) → (s.card : ℝ) ≤ ε ^ (-1 + α₀)} := by
  set q : ℝ := 1 / (2 + γ) ^ 2 with hq_def
  have hq : 0 < q := by positivity
  have hq1 : q < 1 := by
    rw [hq_def, div_lt_one (by positivity)]
    nlinarith
  have hexp : 2 / (2 + γ) ^ 2 - q = q := by rw [hq_def]; ring
  set b : ℝ := min β q with hb_def
  have hb : 0 < b := lt_min hβ hq
  set a : ℝ := b / 2 with ha_def
  have ha : 0 < a := by positivity
  set βp : ℝ := (2 - γ) ^ 2 / 4 with hβp_def
  have hβp : 0 < βp := by
    have : 0 < 2 - γ := by linarith
    positivity
  have hβp2 : βp < (2 - γ) ^ 2 / 2 := by rw [hβp_def]; linarith
  refine ⟨a * βp, mul_pos ha hβp, ?_⟩
  set ρ' : ℝ := (1 + ρ) / 2 with hρ'_def
  have hdiam := hcell γ hγ hγ2 q ρ' hq hq1 (by rw [hρ'_def]; linarith) (by rw [hρ'_def]; linarith)
    Ω S hS
  have hvol := h27 γ hγ hγ2 βp ((2 + γ) ^ 2 / 2 + 1) hβp hβp2 (by linarith) Ω S.P S.hC
    S.hcirc S.μ ⟨hS.isProbabilityMeasure, hS.isQuantumCone, hS.isLQGMeasure⟩
  have hW : ∀ᵐ ω ∂S.P, ω ∈ {ω | IsAreaParametrized (S.μ ω) (S.η ω)} := hS.isAreaParametrized
  set m : ℝ := min ((1 - ρ) / 2) (1 / 2) with hm_def
  have hm : 0 < m := lt_min (by linarith) (by norm_num)
  set ε₁ : ℝ := min 1 (m ^ (1 / a)) with hε₁_def
  have hε₁ : 0 < ε₁ := lt_min one_pos (Real.rpow_pos_of_pos hm _)
  refine ((hdiam.inter (polyHighProb_comp_rpow hvol ha)).inter_ae hW).mono_of_small hε₁
    fun ε hε hεε ω hω => ?_
  obtain ⟨⟨hdω, hvω⟩, hpar⟩ := hω
  have hε1 : ε < 1 := hεε.trans_le (min_le_left _ _)
  have hδ : ε ^ a < m := by
    have h1 : ε ^ a < (m ^ (1 / a)) ^ a :=
      Real.rpow_lt_rpow hε.le (hεε.trans_le (min_le_right _ _)) ha
    rwa [← Real.rpow_mul hm.le, one_div_mul_cancel ha.ne', Real.rpow_one] at h1
  have hδρ : ε ^ a < (1 - ρ) / 2 := hδ.trans_le (min_le_left _ _)
  have hδ2 : ε ^ a < 1 / 2 := hδ.trans_le (min_le_right _ _)
  have hδ0 : 0 < ε ^ a := Real.rpow_pos_of_pos hε _
  -- `ε^β, ε^q ≤ ε^b = (ε^a)^2 ≤ ε^a / 2`
  have hβb : ε ^ β ≤ ε ^ b := Real.rpow_le_rpow_of_exponent_ge hε hε1.le (min_le_left _ _)
  have hqb : ε ^ q ≤ ε ^ b := Real.rpow_le_rpow_of_exponent_ge hε hε1.le (min_le_right _ _)
  have hba : ε ^ b = ε ^ a * ε ^ a := by
    rw [← Real.rpow_add hε, ha_def]
    ring_nf
  have hb2 : 2 * ε ^ b ≤ ε ^ a := by
    rw [hba]
    nlinarith
  intro z hz s hs
  have hz0 : ‖z‖ < ρ := by simpa using hz
  have hsub : ∀ k ∈ s, cell ε (S.η ω) k ⊆ ball z (ε ^ a) := by
    intro k hk
    obtain ⟨p, hpc, hpz⟩ := hs hk
    have hpz' : dist p z < ε ^ β := mem_ball.1 hpz
    have hp0 : p ∈ ball (0 : ℂ) ρ' := by
      rw [mem_ball, dist_zero_right]
      have h1 : ‖p‖ ≤ dist p z + ‖z‖ := by
        rw [dist_eq_norm]
        calc ‖p‖ = ‖(p - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖p - z‖ + ‖z‖ := norm_add_le _ _
      rw [hρ'_def]
      linarith
    have hd := (hdω k ⟨p, hpc, hp0⟩).2
    rw [hexp] at hd
    have hbdd : Bornology.IsBounded (cell ε (S.η ω) k) := (isCompact_cell hpar.1 ε k).isBounded
    intro y hy
    rw [mem_ball]
    have hyp : dist y p ≤ diam (cell ε (S.η ω) k) := dist_le_diam_of_mem hbdd hy hpc
    calc dist y z ≤ dist y p + dist p z := dist_triangle _ _ _
      _ < ε ^ q + ε ^ β := by linarith
      _ ≤ ε ^ a := by linarith
  have hz1 : z ∈ ball (0 : ℂ) (1 - ε ^ a) := by
    rw [mem_ball, dist_zero_right]
    linarith
  have hmass := (hpar.ofReal_mul_card_le hε s hsub).trans (hvω z hz1).2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity), ← Real.rpow_mul hε.le] at hmass
  rw [Real.rpow_add hε, Real.rpow_neg_one, inv_mul_eq_div, le_div_iff₀ hε]
  linarith

end MatedCRT
