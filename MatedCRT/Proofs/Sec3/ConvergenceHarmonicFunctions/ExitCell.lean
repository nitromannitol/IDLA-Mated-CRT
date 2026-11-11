import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellIntegral
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.Final
import MatedCRT.Proofs.Sec6.IterativeBound.OfSteps
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.External.SLE

/-!
# Lemma 3.6: the exit-cell comparison

`HarmonicExitCellStep` from Theorem 2.11, the scaling of `m_ε` (`MepsScalingInput`), the
Brownian regular-exit input and measurability of LBM path functionals. For a diagonal index
`n`, the comparison is bounded (`abs_discreteExit_sub_interpolatedExit_le`) by
`C (3η)^χ + 2K E[U_n Φ_n(X̂)]`; Theorem 2.11 transfers the expectation to rescaled LBM, where
it tends to `0` almost surely as `n → ∞` (`ae_tendsto_integral_diagonalBad`); the cell-size
estimate (Lemma 2.8) and `m_ε → ∞` make the window parameters smaller than `1/(n+1)`.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The expected diagonal bad-window envelope of the interpolated walk. -/
noncomputable def walkDiagonalBad {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (r : ℝ)
    (z y : ℂ) (η' : ℝ) (n : ℕ) (ε : ℝ) (ω : Ω) : ℝ :=
  ∫ x, pathUpperEnvelope (diagonalBad z r η' n) n (interpolatedWalk ε (S.η ω) (S.mε ε) x)
    ∂(srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))

/-- The expected diagonal bad-window envelope of rescaled LBM. -/
noncomputable def lbmDiagonalBad {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (r : ℝ)
    (z y : ℂ) (η' : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ b, pathUpperEnvelope (diagonalBad z r η' n) n (rescaledLBMPath (S.clock ω) S.m₀ b)
    ∂(planarBrownianMotion y)

/-- **The exit-cell comparison of Lemma 3.6.** -/
theorem harmonicExitCellStep_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (hmeps : MepsScalingInput 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hX : LBMPathFunctionalMeasurableStep 𝒮) :
    HarmonicExitCellStep 𝒮 := by
  intro h28 γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ y hy δ hδ
  have := hS.isProbabilityMeasure
  obtain ⟨s, hs, C, χ, hχ, -, hhol⟩ := hψ
  obtain ⟨K, hK⟩ :=
    (isCompact_closedBall z (r + s)).exists_bound_of_continuousOn (hhol.continuousOn hχ)
  have hK' : ∀ a ∈ closedBall z (r + s), |ψ a| ≤ K := fun a ha => by
    simpa only [Real.norm_eq_abs] using hK a ha
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK' z (mem_closedBall_self (by linarith)))
  -- the Hölder scale
  obtain ⟨η', hη'pos, hη'⟩ : ∃ η' : ℝ, 0 < η' ∧ (C : ℝ) * (3 * η') ^ (χ : ℝ) < δ / 3 := by
    have h1 : Tendsto (fun t : ℝ => 3 * t) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => 3 * t) (𝓝[>] 0) (𝓝 (3 * 0)) :=
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).const_mul 3
      rwa [mul_zero] at h
    have h2 := (h1.rpow_const (Or.inr (NNReal.coe_nonneg χ))).const_mul (C : ℝ)
    rw [Real.zero_rpow (by exact_mod_cast hχ.ne'), mul_zero] at h2
    obtain ⟨t, ht, htpos⟩ :=
      ((h2.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 3))).and
        self_mem_nhdsWithin).exists
    exact ⟨t, htpos, ht⟩
  set θ : ℝ := δ / (6 * (K + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  have hθeq : θ * (6 * (K + 1)) = δ := div_mul_cancel₀ _ (by positivity)
  have hdy : 0 < r - dist y z := by have := mem_ball.mp hy; linarith
  have hBL : ∀ n : ℕ, IsBoundedLipschitzPathFunctional
      (pathUpperEnvelope (diagonalBad z r η' n) n) := fun n =>
    isBoundedLipschitzPathFunctional_pathUpperEnvelope (abs_exitWindowBad_le_one z r _ _ η')
      (Nat.cast_nonneg n)
  have hVtail : Tendsto (fun n => S.P {ω | θ < |lbmDiagonalBad S r z y η' n ω - 0|}) atTop
      (𝓝 0) :=
    tendsto_measure_abs_sub_gt_of_ae_tendsto_nat S.P (lbmDiagonalBad S r z y η') (fun _ => 0)
      (fun n => (hX γ hγ hγ2 Ω S hS y _ (hBL n)).2)
      (hS.ae_tendsto_integral_diagonalBad hγ hγ2 hexc hX hr hy hη'pos) hθ
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  set q : ℝ≥0∞ := e / 2 / 2 with hqdef
  have hq : 0 < q := ENNReal.div_pos (ENNReal.div_pos he.ne' ENNReal.ofNat_ne_top).ne'
    ENNReal.ofNat_ne_top
  have hsum : q + q + q + q = e := by
    rw [hqdef, add_assoc (e / 2 / 2 + e / 2 / 2), ENNReal.add_halves, ENNReal.add_halves]
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ η' ∧ 1 / ((n : ℝ) + 1) ≤ s ∧
      1 / ((n : ℝ) + 1) < r - dist y z := by
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [ht.eventually (ge_mem_nhds hη'pos), ht.eventually (ge_mem_nhds hs),
      ht.eventually (gt_mem_nhds hdy)] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨n, hnV, hn1, hn2, hn3⟩ :=
    ((ENNReal.tendsto_nhds_zero.1 hVtail q hq).and hsmall).exists
  set d : ℝ := 1 / ((n : ℝ) + 1) with hddef
  have hdpos : 0 < d := by positivity
  -- Theorem 2.11 for the envelope
  have hconvU := h211 γ hγ hγ2 Ω S hS {y} isCompact_singleton y (mem_singleton y) _ (hBL n) θ hθ
  -- cell sizes (Lemma 2.8 with `ζ = 1/(2+γ)²`)
  have hζ : (0 : ℝ) < 1 / (2 + γ) ^ 2 := by positivity
  have hζ1 : 1 / (2 + γ) ^ 2 < (1 : ℝ) := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hexp : 2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2 = 1 / (2 + γ) ^ 2 := by ring
  have hcellT := IterativeBound.probTendsToOne_of_polyHighProb
    (h28 γ hγ hγ2 (1 / (2 + γ) ^ 2) ρ hζ hζ1 hρ hρ1 Ω S hS)
  have hcellEv : ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ¬ ∀ k : ℤ,
      (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
        Metric.diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2)} ≤ q := by
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hcellT q hq] with ε hε
    refine (measure_mono ?_).trans hε
    intro ω hω hE
    exact hω fun k hk => (hE k hk).2
  have hpow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2) ≤ d := by
    rw [hexp]
    have h3 : Tendsto (fun ε : ℝ => ε ^ (1 / (2 + γ) ^ 2)) (𝓝[>] 0)
        (𝓝 ((0 : ℝ) ^ (1 / (2 + γ) ^ 2))) :=
      ((Real.continuousAt_rpow_const 0 _ (Or.inr hζ.le)).tendsto).mono_left nhdsWithin_le_nhds
    rw [Real.zero_rpow hζ.ne'] at h3
    exact h3.eventually (Iic_mem_nhds hdpos)
  -- `m_ε → ∞`
  obtain ⟨Cm, hCm, hmC⟩ := hmeps γ hγ hγ2
  obtain ⟨ε₀, hε₀, hmε⟩ := hmC Ω S hS
  have hmεev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ (n : ℝ) + 1 ≤ S.mε ε := by
    have hε₁ : 0 < min ε₀ (1 / (Cm * ((n : ℝ) + 1))) := lt_min hε₀ (by positivity)
    filter_upwards [Ioo_mem_nhdsGT hε₁] with ε hε
    obtain ⟨hε0, hε1⟩ := hε
    refine ⟨hε0, le_trans ?_ (hmε ε hε0 (hε1.trans_le (min_le_left _ _))).1⟩
    have h2 : ε < 1 / (Cm * ((n : ℝ) + 1)) := hε1.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h2
    rw [← mul_inv, ← one_div, le_div_iff₀ (by positivity)]
    nlinarith
  -- the almost sure environment conditions
  have hgood : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω) ∧
      Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
        (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      adjacentCellsMeetAeStep 𝒮 γ hγ hγ2 Ω S hS] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hnull := ae_iff.1 hgood
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hconvU q hq, hcellEv, hpow, hmεev]
    with ε hεU hεC hεp hεm
  obtain ⟨hε0, hεm⟩ := hεm
  calc S.P {ω | δ < |((∫ x, ψ (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
          interpolatedExitExpectation S r z y ψ ε ω) - 0|}
      ≤ S.P ((({ω | θ < |walkDiagonalBad S r z y η' n ε ω - lbmDiagonalBad S r z y η' n ω|} ∪
          {ω | ¬ ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ).Nonempty →
            Metric.diam (cell ε (S.η ω) k) ≤ ε ^ (2 / (2 + γ) ^ 2 - 1 / (2 + γ) ^ 2)}) ∪
          {ω | θ < |lbmDiagonalBad S r z y η' n ω - 0|}) ∪
          {ω | ¬ (IsAreaParametrized (S.μ ω) (S.η ω) ∧
            Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧
            ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
              (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty)}) := by
        apply measure_mono
        intro ω hω
        change δ < |_| at hω
        by_contra hcon
        simp only [mem_union, not_or] at hcon
        obtain ⟨⟨⟨hA, hB⟩, hC'⟩, hD⟩ := hcon
        change ¬ (θ < |_|) at hA
        change ¬ (θ < |_|) at hC'
        change ¬ ¬ _ at hB
        change ¬ ¬ _ at hD
        rw [not_not] at hB hD
        obtain ⟨hηa, hp, hadj⟩ := hD
        have hdiam : ∀ k ∈ cellVertices ε (S.η ω) (ball z r), ∀ a ∈ cell ε (S.η ω) k,
            ∀ b ∈ cell ε (S.η ω) k, dist a b ≤ d := by
          rintro k ⟨w, hwc, hwb⟩ a ha b hb
          have hk := hB k ⟨w, hwc, hball hwb⟩
          exact (Metric.dist_le_diam_of_mem (Sec7.cell_isBounded hηa.1 k) ha hb).trans
            (hk.trans hεp)
        have hmpos : 0 < S.mε ε := by linarith
        have hmh : (1 / S.mε ε : ℝ).toNNReal ≤ d.toNNReal :=
          Real.toNNReal_le_toNNReal (one_div_le_one_div_of_le (by positivity) hεm)
        have hbound := abs_discreteExit_sub_interpolatedExit_le (k := n) hε0 hmpos hmh hηa hp
          (hadj ε hε0) hr hdpos.le hn2 hη'pos.le (by linarith) hhol hK' hdiam
        have hA' := abs_le.mp (not_lt.mp hA)
        have hC'' := abs_le.mp (not_lt.mp hC')
        have hEU : walkDiagonalBad S r z y η' n ε ω ≤ 2 * θ := by linarith [hA'.2, hC''.2]
        have hpowle : (2 * η' + d) ^ (χ : ℝ) ≤ (3 * η') ^ (χ : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) χ.2
        have hCpow : (C : ℝ) * (2 * η' + d) ^ (χ : ℝ) ≤ (C : ℝ) * (3 * η') ^ (χ : ℝ) :=
          mul_le_mul_of_nonneg_left hpowle C.2
        have hKEU : 2 * K * walkDiagonalBad S r z y η' n ε ω ≤ 2 * K * (2 * θ) :=
          mul_le_mul_of_nonneg_left hEU (by positivity)
        have hKθ : 2 * K * (2 * θ) ≤ 2 * δ / 3 := by nlinarith
        rw [sub_zero] at hω
        change δ < |(∫ x, ψ (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
          ∫ x, ψ (ballRetraction z r (pathExitPosition (ball z r)
            (interpolatedWalk ε (S.η ω) (S.mε ε) x)))
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)| at hω
        have : |(∫ x, ψ (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) -
          ∫ x, ψ (ballRetraction z r (pathExitPosition (ball z r)
            (interpolatedWalk ε (S.η ω) (S.mε ε) x)))
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)| ≤
            (C : ℝ) * (2 * η' + d) ^ (χ : ℝ) + 2 * K * walkDiagonalBad S r z y η' n ε ω :=
          hbound
        linarith
    _ ≤ q + q + q + 0 := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        · refine (measure_union_le _ _).trans ?_
          gcongr
          · exact (measure_union_le _ _).trans (add_le_add hεU hεC)
        · exact hnull.le
    _ ≤ e := by rw [← hsum]; gcongr

/-- **Lemma 3.6**, final form: from Theorem 2.11 and Lemma 2.8 (cited), the scaling of
`m_ε` (`MepsScalingInput`), the Brownian regular-exit input
`BrownianOutwardExcursionAtExitStep` and the measurability of LBM path functionals. -/
theorem convergenceHarmonicFunctions_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h211 : RandomWalkToLBMStmt 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (hmeps : MepsScalingInput 𝒮) (hexc : BrownianOutwardExcursionAtExitStep)
    (hX : LBMPathFunctionalMeasurableStep 𝒮) : ConvergenceHarmonicFunctionsStmt 𝒮 :=
  convergenceHarmonicFunctions_final 𝒮 h211 h28 hexc hX
    (harmonicExitCellStep_of_inputs 𝒮 h211 hmeps hexc hX)

end MatedCRT
