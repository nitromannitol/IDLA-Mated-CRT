import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellStructuralEvents
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.ShellExponentChoice
import MatedCRT.Proofs.Sec6.IterativeBound.OfSteps

/-! Localized shell iteration under mesh scaling and measurable exit.
The shell iteration is adapted from the work of Leonardo Bonanno. -/

namespace MatedCRT.Sec7

open MeasureTheory Filter Topology Set Metric _root_.HarmonicBalls

/-- A fixed source-ball localization admits the shell certificate. The mesh
scaling and exit measurability are explicit additional inputs. -/
theorem localized_shell_iteration
    (𝒮 : SpaceFillingSLEModel) (h41 : ConvergenceDivisibleStmt 𝒮)
    (h33 : UniformConvergenceGreenKernelStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    (hlower : ConstantOrderLowerBoundDivLogStmt 𝒮) (h27 : VolumeGrowthStmt)
    (hmass : MassBoundOdometerAboveScaleStmt 𝒮) (hcell : CellSizeEstimateStmt 𝒮)
    (hodo : OdometerBoundMassStmt 𝒮) (hadj : AdjacentCellsMeetAeStep 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ' : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t)
    (hexit : NullMeasurableSet {ω | t < clusterExitTime (Λ ω) ρ} S.P) :
    ∃ ζ ω₀ : ℝ, 0 < ζ ∧ ζ < 1 ∧ 0 < ω₀ ∧ ω₀ < 2 / (2 + γ) ^ 2 - ζ ∧
      ∀ n : ℕ, TendsToOneOn S.P
        {ω | t < clusterExitTime (Λ ω) ρ ∧ ball (0 : ℂ) (1 / ((n : ℝ) + 2)) ⊆ Λ ω t}
        (fun ε => {ω | ∃ (Θ : ℕ → Set ℤ) (r : ℕ → ℝ) (N : ℕ) (D : ℝ),
          0 ≤ D ∧ (∀ k < N, 0 < r k) ∧ (0 : ℤ) ∈ Θ 0 ∧
          Θ 0 ⊆ cellVertices ε (S.η ω) (Λ ω t) ∧
          (∀ k < N, Θ (k + 1) = cellVertices ε (S.η ω)
            (thickening (r k) (fillCells ε (S.η ω) (Θ k)))) ∧
          (∀ k ≤ N, ∀ a ∈ vClosure (S.mult ε ω) (Θ k), diam (cell ε (S.η ω) a) ≤ D) ∧
          (∀ a ∈ vBoundary (S.mult ε ω) (Θ N),
            stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t a ≤ ε ^ (-ω₀)) ∧
          (∑ k ∈ Finset.range N, r k) + ((N : ℝ) + 1) * (2 * D) ≤ δ / 2}) := by
  let βm : ℝ := (2 + γ) ^ 2 / 2 + 1
  have hβm : (2 + γ) ^ 2 / 2 < βm := by dsimp [βm]; linarith
  obtain ⟨ω, hω, hlower'⟩ := hlower γ hγ hγ' ρ hρ hρ' βm hβm
  obtain ⟨C, c, βₘ, hC, hc, hc1, hβₘ, hmass'⟩ := hmass γ hγ hγ' ρ hρ hρ'
  obtain ⟨ζ, ω₀, q, hζ, hζ1, hω₀, hωd, hω1, hωβ, hωω, hq, hqω, hqd⟩ :=
    exists_compatible_shell_exponents hγ hβₘ hω
  refine ⟨ζ, ω₀, hζ, hζ1, hω₀, hωd, ?_⟩
  let d : ℝ := 2 / (2 + γ) ^ 2 - ζ
  have hd : 0 < d := lt_trans hω₀ hωd
  let β : ℝ := 2 * βm
  have hβ : 0 < β := by dsimp [β, βm]; positivity
  let α : ℝ := 1 / β
  have hα : 0 < α := one_div_pos.mpr hβ
  let δ' : ℝ := min (δ / 2) (ρ / 24)
  have hδ' : 0 < δ' := lt_min (by positivity) (by positivity)
  have hδ'δ : δ' ≤ δ / 2 := min_le_left _ _
  have hδ'ρ : δ' ≤ ρ / 24 := min_le_right _ _
  let T : ℝ := ∑' j : ℕ, ((j : ℝ) + 1) ^ 2 * ((1 / 2 : ℝ) ^ α) ^ j
  have hT : 0 ≤ T := tsum_nonneg (fun j => by positivity)
  let hstruct := ae_shell_structural_data hγ hγ' hρ hρ' hadj hodo hS Λ hΛ
  have hmassprob := IterativeBound.probTendsToOne_of_polyHighProb (hmass' Ω S hS)
  have hcellprob := IterativeBound.probTendsToOne_of_polyHighProb
    (hcell γ hγ hγ' ζ ρ hζ hζ1 hρ hρ' Ω S hS)
  intro n
  let s₀ : ℝ := 1 / ((n : ℝ) + 2)
  have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
  have hs₀1 : s₀ < 1 := by
    dsimp [s₀]
    rw [div_lt_one (by positivity)]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  obtain ⟨s₁, s₂, hs₁, _, hs₂, hs₂1, hlower''⟩ := hlower' s₀ hs₀ hs₀1
  obtain ⟨dd, hdd, hddpos, hgoodprob⟩ := hlower'' Ω S hS
  let dd' : Ω → ℝ := fun ω => min 1 (dd ω)
  have hdd' : Measurable[S.fieldSigma] dd' := measurable_const.min hdd
  have hdd'pos : ∀ ω, 0 < dd' ω := fun ω => lt_min zero_lt_one (hddpos ω)
  obtain ⟨K, hK, hcoeff⟩ := exists_shell_radius_coefficient (β := β) (C := C)
    (by positivity : 0 < c / 8) hs₁ hC.le
  have hbudget := initial_delayed_shell_budget_and_margins
    𝒮 h41 h33 hscale γ hγ hγ' h27 ρ hρ hρ' Ω S hS Λ hΛ t ht hexit
    dd' hdd' hdd'pos K ω₀ α c s₂ T δ' q d ω₀ hK hω₀.le hω1 hα hc hc1.le
    hs₂ hT hδ' hq hqd hqω
  have hprob := IterativeBound.probTendsToOne_inter hmassprob hcellprob
  have hboth := tendsToOneOn_shell_good_events S.P
    {ω | t < clusterExitTime (Λ ω) ρ}
    {ω | t < clusterExitTime (Λ ω) ρ ∧ ball (0 : ℂ) s₀ ⊆ Λ ω t}
    _ _ _ _ (fun _ h => h.1) hbudget hgoodprob hprob hstruct
  unfold TendsToOneOn at hboth ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hboth
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with ε hε hε1
  apply measure_mono
  rintro ω ⟨hG, hbad⟩
  refine ⟨hG, ?_⟩
  rintro ⟨⟨⟨hbudgetω, hgoodω⟩, hmassω, hcellω⟩, hfam, harea, hstrω, hlapω, hadjω, hodoω⟩
  apply hbad
  let Θ := initialDelayedShells S Λ ρ t K α q ε ω
  let O : ℕ → ℝ := fun k => ⨆ v : vBoundary (S.mult ε ω) (Θ k),
    stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t v
  let r := delayedShellRadius O (ε * K) α (ε ^ q)
  let S₀ := max (O 0) (ε ^ (-ω₀))
  obtain ⟨⟨N, n', htarget, hn', hbudget'⟩, hmargins⟩ := hbudgetω
  have hsource := initialDelayedShells_source S Λ ρ t K α q ε ω hε harea.2.1 harea.2.2.1
    (hfam.1 t ht).2.1 hG.2
  have hΛout : Λ ω t ⊆ closedBall (0 : ℂ) (ρ / 3) :=
    (coneFamily_subset_before_exit hfam ht hG.1).trans ball_subset_closedBall
  have hS₀ : 0 < S₀ := lt_of_lt_of_le (Real.rpow_pos_of_pos hε (-ω₀)) (le_max_right _ _)
  have hgood : ∀ u : ℝ, 10 * ε ^ ω₀ ≤ u → u ≤ dd' ω → ∀ U : Set ℤ,
      closure (fillCells ε (S.η ω) U) ⊆ ball 0 (ρ / 2) → ball 0 s₀ ⊆ fillCells ε (S.η ω) U →
      ∀ A ⊆ cellVertices ε (S.η ω) (thickening u (fillCells ε (S.η ω) U)) \ U,
        (∀ z : ℂ, ((A ∩ cellVertices ε (S.η ω) (ball z u)).ncard : ℝ) < s₁ * u ^ β / ε) →
        ∀ a ∈ cellVertices ε (S.η ω) (frontier (thickening (u / 2) (fillCells ε (S.η ω) U))),
          srwLaw (S.mult ε ω) a {x | ∀ j : ℕ,
            (j : ℕ∞) < vExitTime (cellVertices ε (S.η ω) (thickening u (fillCells ε (S.η ω) U)) \ U) x →
            x j ∈ A} ≤ ENNReal.ofReal (1 - s₂ / (1 + |Real.log u|) ^ 2) := by
    intro u hu hu' U hU hU' A hA hA' a ha
    exact hgoodω u (shell_survival_lower_radius_of_exponent_le hε hε1.le hωω hu)
      (hu'.trans (min_le_right _ _)) U hU hU' A hA (by simpa [β] using hA') a ha
  obtain ⟨T', r', τ, D, hD, hr', hzero, hinit, hstep, hdiam, hbound, hsum⟩ :=
    delayed_dyadic_certificate_of_mass_and_log_survival_events
      (R₀ := ρ / 3) (R := 5 * ρ / 12) (D := ε ^ d) (c := c) (K := K) (C := C)
      (β := β) (βₘ := βₘ) (s₀ := s₀) (s₁ := s₁) (s₂ := s₂) (ω₀ := ω₀)
      (dd := dd' ω) (B := ε ^ (-ω₀)) (δ := δ') (F := ε ^ q) (S := S₀)
      Θ r O n' N rfl rfl hε hε1.le hωβ ht hc hc1.le hs₂ hs₂1.le harea.1
      (Real.rpow_nonneg hε.le _) (by positivity) (by linarith) (Real.rpow_pos_of_pos hε _)
      (S.mult_symm ε ω) (hstrω ε hε).1 (S.mult_succ_ne_zero hε.le ω) (hadjω ε hε)
      ((hstrω ε hε).2 ρ) (hlapω ε t hε ht) hsource.1
      (initialDelayedShells_spec S Λ ρ t K α q ε ω).1 hΛout hsource.2
      (fun k _ => (initialDelayedShells_spec S Λ ρ t K α q ε ω).2 k)
      (by linarith) hK hC.le hβ hs₁ hcoeff
      (fun k _ => hmargins k) (fun a ha => (hcellω a ha).2)
      (hmassω t ht) (hodoω ε t hε ht) hgood (min_le_left _ _)
      hS₀ (le_max_left _ _) htarget (by simpa [T, α, r, O, S₀, Θ] using hbudget') (by simpa [α] using hn')
  exact ⟨T', r', τ, D, hD, hr', hzero, hinit, hstep, hdiam, hbound, hsum.trans hδ'δ⟩

end MatedCRT.Sec7
