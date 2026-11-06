import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LBMExitTimeIntegrableProb
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkFunctionalConvergence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkKilledConvergence
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LBMExitTimeIntegrableTruncated
import MatedCRT.Steps.Sec3.ConvergenceHarmonicFunctions

/-!
# LBM exit time: the bound on the LBM expectation of an inner truncated exit functional

From the convergence in probability of the walk expectations (`walkFunctional_tendstoInProbability_of_ae_continuousWithin`)
and the bound on the good events (`walk_integral_le_of_good`), the LBM expectation of the truncated exit functional
of an inner disk is bounded almost surely by a random constant. The comparison uses only outer measures, so no
measurability in the environment is needed.
-/

namespace MatedCRT

open MeasureTheory Set Filter Topology Metric _root_.HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Comparison.** A limit in probability of `X ε` to `Y`, with `X ε ≤ C` on events `Good ε` of vanishing
complement, gives `Y ≤ C` almost surely. -/
theorem ae_le_of_tendstoInProbability {P : Measure Ω} {X : ℝ → Ω → ℝ} {Y C : Ω → ℝ}
    {Good : ℝ → Set Ω} (hXY : TendstoInProbability P X Y)
    (hGood : Tendsto (fun ε => P (Good ε)ᶜ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ Good ε, X ε ω ≤ C ω) :
    ∀ᵐ ω ∂P, Y ω ≤ C ω := by
  have key : ∀ η : ℝ, 0 < η → P {ω | C ω + η < Y ω} = 0 := by
    intro η hη
    have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {ω | C ω + η < Y ω} ≤
        P {ω | η < |X ε ω - Y ω|} + P (Good ε)ᶜ := by
      filter_upwards [hbound] with ε hε
      have hsub : {ω | C ω + η < Y ω} ⊆ {ω | η < |X ε ω - Y ω|} ∪ (Good ε)ᶜ := by
        intro ω hω
        by_cases hG : ω ∈ Good ε
        · refine Or.inl ?_
          have hωY : C ω + η < Y ω := hω
          have hXC : X ε ω ≤ C ω := hε ω hG
          show η < |X ε ω - Y ω|
          have habs : Y ω - X ε ω ≤ |X ε ω - Y ω| := by
            rw [abs_sub_comm]
            exact le_abs_self _
          linarith
        · exact Or.inr hG
      exact le_trans (measure_mono hsub) (measure_union_le _ _)
    have hlim : Tendsto (fun ε => P {ω | η < |X ε ω - Y ω|} + P (Good ε)ᶜ) (𝓝[>] (0 : ℝ))
        (𝓝 0) := by
      have := (hXY η hη).add hGood
      rwa [add_zero] at this
    have hcle : P {ω | C ω + η < Y ω} ≤ 0 := ge_of_tendsto hlim hle
    exact le_antisymm hcle zero_le
  have hnull : P {ω | ¬ Y ω ≤ C ω} = 0 := by
    have hsub : {ω | ¬ Y ω ≤ C ω} ⊆ ⋃ n : ℕ, {ω | C ω + 1 / ((n : ℝ) + 1) < Y ω} := by
      intro ω hω
      have hω' : C ω < Y ω := not_le.mp hω
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hω')
      exact mem_iUnion.2 ⟨n, by show C ω + 1 / ((n : ℝ) + 1) < Y ω; linarith⟩
    exact measure_mono_null hsub (measure_iUnion_null fun n => key _ (by positivity))
  exact ae_iff.2 hnull

/-- The a.s. facts on the LBM path for the inner ball `B(z, s)` with `y ∈ B(z, s)`: the rescaled path is
continuous, and the truncated exit functional is continuous within continuous paths at it. -/
theorem ae_lbm_facts {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (hm : 0 < S.m₀) (hexc : BrownianOutwardExcursionAtExitStep) {y z : ℂ} {s : ℝ}
    (hys : y ∈ ball z s) (hs : 0 < s) (n : ℕ) :
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      rescaledLBMPath (S.clock ω) S.m₀ b ∈ {w : ℝ≥0 → ℂ | Continuous w} ∧
      PathFunctionalContinuousWithinAt {w : ℝ≥0 → ℂ | Continuous w}
        (truncatedExitFunctional (ball z s) n) (rescaledLBMPath (S.clock ω) S.m₀ b) := by
  have hclock := hS.isLQGClock
  have hreg := hS.ae_rescaledLBM_ball_regular_of_brownian_outward_radial_excursion hm hys
    (hexc y z s hys)
  have hfin := hS.ae_rescaledLBMExitTime_any_ball_lt_top hm y z s
  have hcl : closure (ball z s) = closedBall z s := closure_ball z hs.ne'
  filter_upwards [hclock, hreg, hfin] with ω hω hreg_ω hfin_ω
  filter_upwards [(hω y).2, hreg_ω, hfin_ω] with b hb hregb hfinb
  have hcb : Continuous (rescaledLBMPath (S.clock ω) S.m₀ b) := continuous_rescaledLBMPath hb
  refine ⟨hcb, ?_⟩
  have hfin' : ContinuousPath.exitTime (ball z s) (⟨_, hcb⟩ : ContinuousPath ℂ) < ⊤ :=
    (ContinuousPath.exitTime_lt_top_iff _ _).2 (exists_not_mem_of_pathExitTime_lt_top hfinb)
  have hreg' : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z s) (⟨_, hcb⟩ : ContinuousPath ℂ)).toNNReal,
      (⟨_, hcb⟩ : ContinuousPath ℂ) t ∉ closedBall z s := by
    refine hregb.mono fun t ht => ?_
    rw [← hcl]
    exact ht
  exact pathFunctionalContinuousWithinAt_truncatedExit (⟨_, hcb⟩ : ContinuousPath ℂ) z hfin' hreg' n

/-- **LBM bound for an inner disk.** The LBM expectation of the truncated exit functional of `B(z, s)` is almost
surely at most the random constant `(1 + B · L²).toReal`, for an inner radius `s < r` and `y ∈ B(z, s)`. -/
theorem ae_lbm_integral_le_inner {𝒮 : SpaceFillingSLEModel}
    (hscale : MepsScalingInput 𝒮) (h211 : RandomWalkToLBMStmt 𝒮) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (hcell : CellSizeEstimateStmt 𝒮) (hexc : BrownianOutwardExcursionAtExitStep)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {α B : ℝ} (hα : 0 < α)
    (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) {z y : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hsr : s < r) (hD : ball z r ⊆ ball 0 ρ) (hys : y ∈ ball z s) (n : ℕ)
    (hmomE : HarmonicBalls.PolyHighProb S.P (lbmMomEv S ρ α B)) :
    ∀ᵐ ω ∂S.P, ∫ b, truncatedExitFunctional (ball z s) n (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion y ≤
      (1 + ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2).toReal := by
  set ρ' : ℝ := (1 + ρ) / 2 with hρ'_def
  have hρρ' : ρ < ρ' := by rw [hρ'_def]; linarith
  have hρ'0 : 0 < ρ' := by rw [hρ'_def]; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ'_def]; linarith
  have hy : y ∈ ball z r := ball_subset_ball hsr.le hys
  have hm0 : 0 < S.m₀ := hS.m₀_pos hγ hγ2
  have hcellE : HarmonicBalls.PolyHighProb S.P (lbmCellEv S ρ' γ (1 / 16)) :=
    hcell γ hγ hγ2 (1 / 16) ρ' (by norm_num) (by norm_num) hρ'0 hρ'1 Ω S hS
  have hmassD : ∀ δ : ℝ≥0∞, 0 < δ → ∃ q : ℝ, 0 < q ∧
      S.P {ω | S.μ ω (ball z r) < ENNReal.ofReal q} < δ :=
    fun δ hδ => hS.exists_ball_mass_lower_bound z hr hδ
  have hgeo : ∀ᵐ ω ∂S.P, ω ∈ lbmGeoEv S := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω h1 h2
    exact ⟨h1.1, h1.2.2.1, h2⟩
  have hGoodT := tendsto_compl_lbmGoodEv S ρ α B ρ' γ (1 / 16) (ball z r) hmomE hcellE hmassD hα hgeo
  have hXY := walkFunctional_tendstoInProbability_of_ae_continuousWithin 𝒮 h211 hX hγ hγ2 S hS y
    (truncatedExitFunctional (ball z s) n) (n : ℝ)
    (fun w _ => abs_truncatedExitFunctional_le _ _ _)
    (fun ε ω => (measurable_truncatedExitFunctional_interpolatedWalk ε (S.η ω) (S.mε ε) z s n).aestronglyMeasurable)
    (ae_lbm_facts S hS hm0 hexc hys hs n)
  obtain ⟨C, hC, hsc⟩ := hscale γ hγ hγ2
  obtain ⟨ε₀, hε₀, hbd⟩ := hsc Ω S hS
  have hbexp : 0 < 2 / (2 + γ) ^ 2 - 1 / 16 := by
    have h16 : (2 + γ) ^ 2 < 16 := by nlinarith
    have hpos : 0 < (2 + γ) ^ 2 := by positivity
    have h18 : 1 / 8 < 2 / (2 + γ) ^ 2 := by
      rw [lt_div_iff₀ hpos]
      nlinarith
    linarith
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ lbmGoodEv S ρ α B ρ' γ (1 / 16) (ball z r) ε,
      ∫ x, truncatedExitFunctional (ball z s) n (interpolatedWalk ε (S.η ω) (S.mε ε) x)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) ≤
        (1 + ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2).toReal := by
    filter_upwards [Ioo_mem_nhdsGT hε₀, eventually_rpow_le hbexp (sub_pos.2 hsr)] with ε hε hpow
    intro ω hω
    have hεpos : 0 < ε := hε.1
    have hmpos : 0 < S.mε ε :=
      lt_of_lt_of_le (by positivity) (hbd ε hε.1 hε.2).1
    have hcellω : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ').Nonempty →
        Metric.diam (cell ε (S.η ω) k) ≤ r - s := fun k hk =>
      ((hω.1.2 k hk).2).trans hpow
    have key := walk_integral_le_of_good S hεpos hmpos hr (sub_pos.2 hsr) n hy hD hρρ'
      hω.2 hω.1.1.1 hω.1.1.2 hcellω
    rwa [sub_sub_cancel] at key
  have hfinal := ae_le_of_tendstoInProbability hXY hGoodT hbound
  exact hfinal

end MatedCRT
