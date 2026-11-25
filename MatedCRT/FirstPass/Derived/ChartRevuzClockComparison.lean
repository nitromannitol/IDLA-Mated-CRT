import MatedCRT.FirstPass.Derived.KilledOccupationVagueComparison
import MatedCRT.FirstPass.Derived.ExitRateClockOccupation
import MatedCRT.FirstPass.Derived.ChartTransportRateConvergence

/-!
# Comparison of the transported clocks with the canonical clocks of the transported measure

Let `T` be a random path with the law of Brownian motion from `0` stopped at its exit from the unit disc. For two
families of rates `e_n`, `g_k ≥ 0` on the disc such that `e_n(v) dv` and `g_k(v) dv` converge vaguely on every closed
disc `B̄(0, r)`, `r < 1`, to the same measure `ν₀`, with common upper power growth and mass bounds, the probability that
the exit-rate clocks of `e_n` and `g_k` along `T` differ by more than `η` at some time tends to `0` as `n, k → ∞`
(`tendsto_measure_exists_lt_abs_exitRateClock_sub`): the occupation functionals are almost surely finite
(`measure_killedOccupation_eq_top_eq_zero`, `eventually_killedPotential_ball_one_zero_ne_top`), the gap of the clocks is
the gap of the occupation functionals (`measure_exists_lt_abs_exitRateClock_sub_le`), which tends to `0` in probability
(`tendsto_measure_exists_lt_abs_killedOccupationGapUpTo`).

For an inverse chart `ψ` of a bounded open set `U`, this applies to the transported approximating LQG rates
`e_n = chartTransportRate U ψ (lqgApproxRate γ h n)` and the canonical rates `g_k = discCanonicalRate k ν₀` of the image
`ν₀ = ψ_*(μ|_U)` of the LQG measure, under a uniform small-ball power bound of the approximations
(`tendsto_measure_exists_lt_abs_exitRateClock_chartTransportRate_sub`): the clocks of the transported approximating
LQG measures and the clocks of the absolutely continuous approximations of the additive functional with Revuz measure
`ν₀` (Fukushima–Oshima–Takeda (2011), §5.1, §6.2) are uniformly close in probability. This is the identification of the
limit of the transported clocks in the Revuz route to Berestycki (2015), Theorem 1.3.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Metric Topology
open scoped NNReal ENNReal

namespace MatedCRT

open MarkovProcess _root_.HarmonicBalls

/-! ### Rates that agree on the disc -/

/-- The exit rate only depends on the rate on `D`. -/
theorem exitRate_congr {D : Set ℂ} {ρ ρ' : ℂ → ℝ} (h : EqOn ρ ρ' D) : exitRate D ρ = exitRate D ρ' := by
  funext w r
  by_cases hr : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime D w
  · rw [exitRate_of_lt_exitTime hr, exitRate_of_lt_exitTime hr,
      h (ContinuousPath.mem_of_lt_exitTime D w _ hr)]
  · rw [exitRate_of_exitTime_le (not_lt.1 hr), exitRate_of_exitTime_le (not_lt.1 hr)]

/-- The exit-rate clock only depends on the rate on `D`. -/
theorem exitRateClock_congr {D : Set ℂ} {ρ ρ' : ℂ → ℝ} (h : EqOn ρ ρ' D) :
    exitRateClock D ρ = exitRateClock D ρ' := by
  funext w σ
  unfold exitRateClock
  rw [exitRate_congr h]

/-- Rates that agree on a measurable set `D` give the same density measure on `D`. -/
theorem restrict_withDensity_ofReal_eq_of_eqOn {ρ ρ' : ℂ → ℝ} {D : Set ℂ} (hD : MeasurableSet D)
    (h : EqOn ρ ρ' D) :
    (volume.withDensity fun v => ENNReal.ofReal (ρ v)).restrict D =
      (volume.withDensity fun v => ENNReal.ofReal (ρ' v)).restrict D := by
  rw [restrict_withDensity hD, restrict_withDensity hD]
  refine withDensity_congr_ae ((ae_restrict_iff' hD).2 (ae_of_all _ fun v hv => ?_))
  simp only [h hv]

theorem withDensity_ofReal_apply_eq_of_eqOn {ρ ρ' : ℂ → ℝ} {D A : Set ℂ} (hD : MeasurableSet D)
    (h : EqOn ρ ρ' D) (hA : A ⊆ D) :
    volume.withDensity (fun v => ENNReal.ofReal (ρ v)) A =
      volume.withDensity (fun v => ENNReal.ofReal (ρ' v)) A := by
  calc volume.withDensity (fun v => ENNReal.ofReal (ρ v)) A
      = volume.withDensity (fun v => ENNReal.ofReal (ρ v)) (A ∩ D) := by rw [inter_eq_left.2 hA]
    _ = (volume.withDensity fun v => ENNReal.ofReal (ρ v)).restrict D A := (Measure.restrict_apply' hD).symm
    _ = (volume.withDensity fun v => ENNReal.ofReal (ρ' v)).restrict D A := by
        rw [restrict_withDensity_ofReal_eq_of_eqOn hD h]
    _ = volume.withDensity (fun v => ENNReal.ofReal (ρ' v)) (A ∩ D) := Measure.restrict_apply' hD
    _ = volume.withDensity (fun v => ENNReal.ofReal (ρ' v)) A := by rw [inter_eq_left.2 hA]

theorem integral_withDensity_ofReal_eq_of_eqOn {ρ ρ' : ℂ → ℝ} {D : Set ℂ} (hD : MeasurableSet D)
    (h : EqOn ρ ρ' D) {F : ℂ → ℝ} (hF0 : ∀ v, v ∉ D → F v = 0) :
    ∫ v, F v ∂(volume.withDensity fun v => ENNReal.ofReal (ρ v)) =
      ∫ v, F v ∂(volume.withDensity fun v => ENNReal.ofReal (ρ' v)) := by
  have h1 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume.withDensity fun v => ENNReal.ofReal (ρ v)) hF0
  have h2 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume.withDensity fun v => ENNReal.ofReal (ρ' v)) hF0
  rw [← h1, ← h2, restrict_withDensity_ofReal_eq_of_eqOn hD h]

/-! ### Almost sure finiteness of the occupation functionals -/

/-- Stopping a path at its exit time from an open set does not change its occupation functional. -/
theorem killedOccupation_stopAtExitTime {D : Set ℂ} (hD : IsOpen D) (f : ℂ → ℝ≥0∞) (W : ContinuousPath ℂ) :
    killedOccupation D f (stopAtExitTime D W) = killedOccupation D f W := by
  simp only [killedOccupation, killedRate_stopAtExitTime hD]

/-- If the potential `u_f(0)` for Brownian motion killed on exiting the unit disc is finite, then the occupation
functional of `f` along a random path with the law of stopped disc Brownian motion from `0` is almost surely finite. -/
theorem measure_killedOccupation_eq_top_eq_zero {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    {T : Ω' → ContinuousPath ℂ} (hT : AEMeasurable T P)
    (hTmap : P.map T = (planarBrownianMotion 0).map (stopAtExitTime (ball (0 : ℂ) 1)))
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) (hfin : killedPotential (ball 0 1) f 0 ≠ ⊤) :
    P {ω | killedOccupation (ball 0 1) f (T ω) = ⊤} = 0 := by
  have hm : Measurable (killedOccupation (ball (0 : ℂ) 1) f) := measurable_killedOccupation isOpen_ball hf
  have hS : MeasurableSet {W : ContinuousPath ℂ | killedOccupation (ball 0 1) f W = ⊤} :=
    hm (measurableSet_singleton ⊤)
  have hae : ∀ᵐ W ∂planarBrownianMotion 0, killedOccupation (ball 0 1) f W < ⊤ := ae_lt_top hm hfin
  calc P {ω | killedOccupation (ball 0 1) f (T ω) = ⊤}
      = P.map T {W | killedOccupation (ball 0 1) f W = ⊤} :=
        (Measure.map_apply_of_aemeasurable hT hS).symm
    _ = planarBrownianMotion 0
          (stopAtExitTime (ball (0 : ℂ) 1) ⁻¹' {W | killedOccupation (ball 0 1) f W = ⊤}) := by
        rw [hTmap, Measure.map_apply (measurable_stopAtExitTime _ isOpen_ball) hS]
    _ = 0 := by
        refine measure_mono_null (fun W hW => ?_) (ae_iff.1 hae)
        have hW' : killedOccupation (ball 0 1) f (stopAtExitTime (ball (0 : ℂ) 1) W) = ⊤ := hW
        rw [killedOccupation_stopAtExitTime isOpen_ball] at hW'
        exact not_lt_top_iff.2 hW'

/-! ### Exit-rate clocks of two vaguely convergent families -/

/-- **Exit-rate clocks of two vaguely convergent families of rates are close in probability.** Let `T` have the law
of Brownian motion from `0` stopped at its exit from the unit disc, and let `e_n, g_k ≥ 0` be Borel rates on the disc
such that `e_n(v) dv` and `g_k(v) dv` converge vaguely to `ν₀` on every closed disc `B̄(0, r)`, `r < 1`, with common
upper power growth on `B(0, r)` (eventually) and common mass bounds on the unit disc. Then for every `η > 0` the
probability that the exit-rate clocks of `e_n` and `g_k` along `T` differ by more than `η` at some time tends to `0`
as `(n, k) → ∞`. -/
theorem tendsto_measure_exists_lt_abs_exitRateClock_sub {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'}
    {T : Ω' → ContinuousPath ℂ} (hT : AEMeasurable T P)
    (hTmap : P.map T = (planarBrownianMotion 0).map (stopAtExitTime (ball (0 : ℂ) 1)))
    {e g : ℕ → ℂ → ℝ} (he : ∀ n, Measurable (e n)) (hg : ∀ n, Measurable (g n))
    (he0 : ∀ n, ∀ v ∈ ball (0 : ℂ) 1, 0 ≤ e n v) (hg0 : ∀ n, ∀ v ∈ ball (0 : ℂ) 1, 0 ≤ g n v)
    {ν₀ : Measure ℂ}
    (hpow : ∀ r, r < 1 → ∃ β > (0 : ℝ), ∃ r₀ > (0 : ℝ),
      (∀ᶠ n in atTop, ∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r,
        volume.withDensity (fun v => ENNReal.ofReal (e n v)) (ball z s) ≤ ENNReal.ofReal (s ^ β)) ∧
      (∀ᶠ n in atTop, ∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r,
        volume.withDensity (fun v => ENNReal.ofReal (g n v)) (ball z s) ≤ ENNReal.ofReal (s ^ β)) ∧
      ∀ s, 0 < s → s < r₀ → ∀ z ∈ ball (0 : ℂ) r, ν₀ (ball z s) ≤ ENNReal.ofReal (s ^ β))
    {m : ℝ}
    (hem : ∀ᶠ n in atTop, volume.withDensity (fun v => ENNReal.ofReal (e n v)) (ball 0 1) ≤ ENNReal.ofReal m)
    (hgm : ∀ᶠ n in atTop, volume.withDensity (fun v => ENNReal.ofReal (g n v)) (ball 0 1) ≤ ENNReal.ofReal m)
    (hνm : ν₀ (ball 0 1) ≤ ENNReal.ofReal m)
    (hev : ∀ r, r < 1 → ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 r →
      Tendsto (fun n => ∫ y, F y ∂(volume.withDensity fun v => ENNReal.ofReal (e n v))) atTop
        (𝓝 (∫ y, F y ∂ν₀)))
    (hgv : ∀ r, r < 1 → ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 r →
      Tendsto (fun n => ∫ y, F y ∂(volume.withDensity fun v => ENNReal.ofReal (g n v))) atTop
        (𝓝 (∫ y, F y ∂ν₀)))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun p : ℕ × ℕ => P {ω | ∃ σ : ℝ≥0,
      η < |exitRateClock (ball 0 1) (e p.1) (T ω) σ - exitRateClock (ball 0 1) (g p.2) (T ω) σ|})
      atTop (𝓝 0) := by
  have hfm : ∀ n, Measurable fun v => ENNReal.ofReal (e n v) := fun n =>
    ENNReal.measurable_ofReal.comp (he n)
  have hgm' : ∀ n, Measurable fun v => ENNReal.ofReal (g n v) := fun n =>
    ENNReal.measurable_ofReal.comp (hg n)
  have hgap := tendsto_measure_exists_lt_abs_killedOccupationGapUpTo
    (f := fun n v => ENNReal.ofReal (e n v)) (g := fun n v => ENNReal.ofReal (g n v))
    hfm hgm' hpow hem hgm hνm hev hgv hη
  obtain ⟨β, hβ, r₀, hr₀, hep, hgp, hνp⟩ := hpow (1 / 2) (by norm_num)
  have hefin := eventually_killedPotential_ball_one_zero_ne_top (f := fun n v => ENNReal.ofReal (e n v))
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hr₀ hβ hfm hep hem hνp hνm (hev (1 / 2) (by norm_num))
  have hgfin := eventually_killedPotential_ball_one_zero_ne_top (f := fun n v => ENNReal.ofReal (g n v))
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hr₀ hβ hgm' hgp hgm hνp hνm (hgv (1 / 2) (by norm_num))
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := tendsto_fst.mono_left prod_atTop_atTop_eq.ge
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := tendsto_snd.mono_left prod_atTop_atTop_eq.ge
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgap
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hfst.eventually hefin, hsnd.eventually hgfin] with p hp1 hp2
  have hz1 := measure_killedOccupation_eq_top_eq_zero hT hTmap (hfm p.1) hp1
  have hz2 := measure_killedOccupation_eq_top_eq_zero hT hTmap (hgm' p.2) hp2
  have hle := measure_exists_lt_abs_exitRateClock_sub_le hT hTmap (he p.1) (hg p.2) (he0 p.1) (hg0 p.2) η
  calc P {ω | ∃ σ : ℝ≥0, η < |exitRateClock (ball 0 1) (e p.1) (T ω) σ -
        exitRateClock (ball 0 1) (g p.2) (T ω) σ|}
      ≤ P ({ω | killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (e p.1 v)) (T ω) = ⊤} ∪
          {ω | killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (g p.2 v)) (T ω) = ⊤} ∪
          {ω | killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (e p.1 v)) (T ω) ≠ ⊤ ∧
            killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (g p.2 v)) (T ω) ≠ ⊤ ∧
            ∃ σ : ℝ≥0, η < |exitRateClock (ball 0 1) (e p.1) (T ω) σ -
              exitRateClock (ball 0 1) (g p.2) (T ω) σ|}) := by
        refine measure_mono fun ω hω => ?_
        by_cases h1 : killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (e p.1 v)) (T ω) = ⊤
        · exact Or.inl (Or.inl h1)
        by_cases h2 : killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (g p.2 v)) (T ω) = ⊤
        · exact Or.inl (Or.inr h2)
        exact Or.inr ⟨h1, h2, hω⟩
    _ ≤ P {ω | killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (e p.1 v)) (T ω) = ⊤} +
          P {ω | killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (g p.2 v)) (T ω) = ⊤} +
          P {ω | killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (e p.1 v)) (T ω) ≠ ⊤ ∧
            killedOccupation (ball 0 1) (fun v => ENNReal.ofReal (g p.2 v)) (T ω) ≠ ⊤ ∧
            ∃ σ : ℝ≥0, η < |exitRateClock (ball 0 1) (e p.1) (T ω) σ -
              exitRateClock (ball 0 1) (g p.2) (T ω) σ|} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := by
        rw [hz1, hz2, zero_add, zero_add]
        exact hle

/-! ### The transported clocks and the canonical clocks of the transported measure -/

/-- **The transported approximating clocks and the canonical clocks of `ψ_*(μ|_U)` are close in probability.** Let
`ψ` be an inverse chart of the bounded open set `U ⊆ B̄(0, R₁)`, let `μ` be the LQG limit of the approximations
`μ_{ε_n}` of the circle averages `h_ε` (continuous at the dyadic scales), with `μ_{ε_n}(B(x, t)) ≤ t^β` for all `n`,
`x ∈ B̄(0, R₁)` and `t < t₀`, and let `T` have the law of Brownian motion from `0` stopped at its exit from the unit
disc. Then for every `η > 0`, the probability that the exit-rate clocks along `T` of the transported rates
`e_n = chartTransportRate U ψ (lqgApproxRate γ h n)` and of the canonical rates `g_k = discCanonicalRate k ν₀`,
`ν₀ = ψ_*(μ|_U)`, differ by more than `η` at some time tends to `0` as `(n, k) → ∞`. -/
theorem tendsto_measure_exists_lt_abs_exitRateClock_chartTransportRate_sub {U : Set ℂ} {z : ℂ} {ψ : C(ℂ, ℂ)}
    (hψ : IsInverseChart U z ψ) (hU : IsOpen U) (hUb : Bornology.IsBounded U) {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {μ : Measure ℂ} (hμ : IsLQGLimit γ hε μ) (hcont : ∀ n : ℕ, Continuous (hε (dyadicScale n)))
    {R₁ β t₀ : ℝ} (hβ : 0 < β) (ht₀ : 0 < t₀) (hU₁ : U ⊆ closedBall 0 R₁)
    (hpow : ∀ n : ℕ, ∀ x ∈ closedBall (0 : ℂ) R₁, ∀ t, 0 < t → t < t₀ →
      lqgApprox γ hε (dyadicScale n) (ball x t) ≤ ENNReal.ofReal (t ^ β))
    {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} {T : Ω' → ContinuousPath ℂ} (hT : AEMeasurable T P)
    (hTmap : P.map T = (planarBrownianMotion 0).map (stopAtExitTime (ball (0 : ℂ) 1)))
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun p : ℕ × ℕ => P {ω | ∃ σ : ℝ≥0,
      η < |exitRateClock (ball 0 1) (chartTransportRate U ψ (lqgApproxRate γ hε p.1)) (T ω) σ -
        exitRateClock (ball 0 1) (discCanonicalRate p.2 ((μ.restrict U).map ψ)) (T ω) σ|})
      atTop (𝓝 0) := by
  classical
  set ν₀ : Measure ℂ := (μ.restrict U).map ψ with hν₀
  obtain ⟨e, he_def⟩ : ∃ e : ℕ → ℂ → ℝ, e = fun n =>
      (ball (0 : ℂ) 1).piecewise (chartTransportRate U ψ (lqgApproxRate γ hε n)) fun _ => 1 := ⟨_, rfl⟩
  have heq : ∀ n, EqOn (e n) (chartTransportRate U ψ (lqgApproxRate γ hε n)) (ball 0 1) := by
    intro n v hv
    rw [he_def]
    exact piecewise_eq_of_mem _ _ _ hv
  have he : ∀ n, Measurable (e n) := by
    intro n
    rw [he_def]
    exact (continuousOn_chartTransportRate hψ hU hUb (continuous_lqgApproxRate (hcont n))).measurable_piecewise
      continuousOn_const isOpen_ball.measurableSet
  have he0 : ∀ n, ∀ v ∈ ball (0 : ℂ) 1, 0 ≤ e n v := by
    intro n v hv
    rw [heq n hv]
    exact div_nonneg (lqgApproxRate_pos _).le (pow_nonneg (norm_nonneg _) 2)
  have hg : ∀ k, Measurable (discCanonicalRate k ν₀) := fun k =>
    (continuous_discCanonicalRate k ν₀).measurable
  have hg0 : ∀ k, ∀ v ∈ ball (0 : ℂ) 1, 0 ≤ discCanonicalRate k ν₀ v := fun k v _ =>
    (discCanonicalRate_pos k ν₀ v).le
  -- the mass of `ν₀` on the unit disc is finite
  have hν1 : ν₀ (ball 0 1) < ⊤ := by
    have := hμ.isLocallyFiniteMeasure
    obtain ⟨R, hR⟩ := hUb.subset_closedBall 0
    calc ν₀ (ball 0 1) ≤ ν₀ univ := measure_mono (subset_univ _)
      _ = μ U := by
          rw [hν₀, Measure.map_apply ψ.continuous.measurable MeasurableSet.univ, preimage_univ,
            Measure.restrict_apply_univ]
      _ ≤ μ (closedBall 0 R) := measure_mono hR
      _ < ⊤ := (isCompact_closedBall (0 : ℂ) R).measure_lt_top
  -- power bounds with one exponent
  have hpow' : ∀ r, r < 1 → ∃ β' > (0 : ℝ), ∃ r₀ > (0 : ℝ),
      (∀ᶠ n in atTop, ∀ s, 0 < s → s < r₀ → ∀ v ∈ ball (0 : ℂ) r,
        volume.withDensity (fun v => ENNReal.ofReal (e n v)) (ball v s) ≤ ENNReal.ofReal (s ^ β')) ∧
      (∀ᶠ k in atTop, ∀ s, 0 < s → s < r₀ → ∀ v ∈ ball (0 : ℂ) r,
        volume.withDensity (fun v => ENNReal.ofReal (discCanonicalRate k ν₀ v)) (ball v s) ≤
          ENNReal.ofReal (s ^ β')) ∧
      ∀ s, 0 < s → s < r₀ → ∀ v ∈ ball (0 : ℂ) r, ν₀ (ball v s) ≤ ENNReal.ofReal (s ^ β') := by
    intro r hr
    obtain ⟨q, hq, s₁, hs₁, hen, hνn⟩ :=
      exists_chartTransportRate_ball_le_and_map_restrict_ball_le hψ hU hUb hμ hβ ht₀ hU₁ hpow hr
    obtain ⟨q', hq', hq'q, hq'2⟩ : ∃ q' > (0 : ℝ), q' ≤ q ∧ q' ≤ 2 :=
      ⟨min q 2, lt_min hq two_pos, min_le_left _ _, min_le_right _ _⟩
    obtain ⟨s₀, hs₀, hs₀1, hs₀s₁⟩ : ∃ s₀ > (0 : ℝ), s₀ ≤ 1 ∧ s₀ ≤ s₁ :=
      ⟨min s₁ 1, lt_min hs₁ one_pos, min_le_right _ _, min_le_left _ _⟩
    obtain ⟨K, hK_def⟩ : ∃ K : ℝ,
        K = Real.pi + 1 * 2 ^ q' + Real.pi * 1 * 2 ^ q' / discMollifierMass 0 := ⟨_, rfl⟩
    have hK : 0 ≤ K := by
      rw [hK_def]
      exact add_nonneg (add_nonneg Real.pi_pos.le (by positivity))
        (div_nonneg (by positivity) (discMollifierMass_pos 0).le)
    obtain ⟨s₂, hs₂, hKs⟩ := exists_forall_mul_rpow_le_rpow_half hK hq'
    have hνC : ∀ w ∈ ball (0 : ℂ) r, ∀ s, 0 < s → s < s₀ → ν₀ (ball w s) ≤ ENNReal.ofReal (1 * s ^ q') := by
      intro w hw s hs hss
      rw [one_mul]
      exact (hνn s hs (hss.trans_le hs₀s₁) w hw).trans (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hs (hss.le.trans hs₀1) hq'q))
    have hk : ∀ᶠ k : ℕ in atTop, 2 / ((k : ℝ) + 1) < s₀ := by
      have h2 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
      rw [mul_zero] at h2
      filter_upwards [h2.eventually (gt_mem_nhds hs₀)] with k hk
      rwa [mul_one_div] at hk
    have hq2 : q' / 2 ≤ q := (half_le_self hq'.le).trans hq'q
    refine ⟨q' / 2, half_pos hq', min (min (s₀ / 2) s₂) ((1 - r) / 2),
      lt_min (lt_min (half_pos hs₀) hs₂) (by linarith), ?_, ?_, ?_⟩
    · refine Eventually.of_forall fun n s hs hsr v hv => ?_
      have hsa : s < s₀ / 2 := hsr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      have hsc : s < (1 - r) / 2 := hsr.trans_le (min_le_right _ _)
      have hsub : ball v s ⊆ ball 0 1 := ball_subset_ball' (by
        rw [dist_zero_right]
        linarith [mem_ball_zero_iff.1 hv])
      rw [withDensity_ofReal_apply_eq_of_eqOn measurableSet_ball (heq n) hsub]
      exact (hen n s hs (by linarith) v hv).trans (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hs (by linarith) hq2))
    · filter_upwards [hk] with k hk s hs hsr v hv
      have hsa : s < s₀ / 2 := hsr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      have hsb : s < s₂ := hsr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
      rw [withDensity_apply _ measurableSet_ball]
      have h1 := lintegral_ball_discCanonicalRate_le hs₀1 hq'2 zero_le_one hνC hk hv hs (by linarith)
      rw [← hK_def] at h1
      exact h1.trans (ENNReal.ofReal_le_ofReal (hKs s hs hsb))
    · intro s hs hsr v hv
      have hsa : s < s₀ / 2 := hsr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      exact (hνn s hs (by linarith) v hv).trans (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hs (by linarith) hq2))
  -- masses
  obtain ⟨Me, hMe⟩ := exists_eventually_withDensity_lqgApproxRate_le hμ hcont hUb
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = max Me 0 + (Real.pi + (ν₀ (ball 0 1)).toReal) := ⟨_, rfl⟩
  have hνt : 0 ≤ (ν₀ (ball 0 1)).toReal := ENNReal.toReal_nonneg
  have hem : ∀ᶠ n in atTop,
      volume.withDensity (fun v => ENNReal.ofReal (e n v)) (ball 0 1) ≤ ENNReal.ofReal m := by
    filter_upwards [hMe] with n hn
    rw [withDensity_ofReal_apply_eq_of_eqOn measurableSet_ball (heq n) subset_rfl,
      withDensity_chartTransportRate_ball_one hψ hU (lqgApproxRate γ hε n)]
    exact hn.trans (ENNReal.ofReal_le_ofReal (by
      rw [hm_def]
      linarith [le_max_left Me 0, Real.pi_pos]))
  have hgm : ∀ᶠ k in atTop,
      volume.withDensity (fun v => ENNReal.ofReal (discCanonicalRate k ν₀ v)) (ball 0 1) ≤
        ENNReal.ofReal m := by
    refine Eventually.of_forall fun k => ?_
    rw [withDensity_apply _ measurableSet_ball]
    refine (lintegral_ball_zero_discCanonicalRate_le k ν₀ zero_le_one).trans ?_
    calc ENNReal.ofReal (Real.pi * 1 ^ 2) + ν₀ (ball 0 1)
        = ENNReal.ofReal (Real.pi * 1 ^ 2) + ENNReal.ofReal (ν₀ (ball 0 1)).toReal := by
          rw [ENNReal.ofReal_toReal hν1.ne]
      _ = ENNReal.ofReal (Real.pi * 1 ^ 2 + (ν₀ (ball 0 1)).toReal) :=
          (ENNReal.ofReal_add (by positivity) hνt).symm
      _ ≤ ENNReal.ofReal m := ENNReal.ofReal_le_ofReal (by
          rw [hm_def, one_pow, mul_one]
          linarith [le_max_right Me 0])
  have hνm : ν₀ (ball 0 1) ≤ ENNReal.ofReal m := by
    calc ν₀ (ball 0 1) = ENNReal.ofReal (ν₀ (ball 0 1)).toReal := (ENNReal.ofReal_toReal hν1.ne).symm
      _ ≤ ENNReal.ofReal m := ENNReal.ofReal_le_ofReal (by
          rw [hm_def]
          linarith [le_max_right Me 0, Real.pi_pos])
  -- vague convergence
  have hev : ∀ r, r < 1 → ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 r →
      Tendsto (fun n => ∫ y, F y ∂(volume.withDensity fun v => ENNReal.ofReal (e n v))) atTop
        (𝓝 (∫ y, F y ∂ν₀)) := by
    intro r hr F hF hFs
    have hF0 : ∀ v, v ∉ ball (0 : ℂ) 1 → F v = 0 := fun v hv =>
      image_eq_zero_of_notMem_tsupport fun h => hv (closedBall_subset_ball hr (hFs h))
    exact Tendsto.congr (fun n => (integral_withDensity_ofReal_eq_of_eqOn measurableSet_ball (heq n) hF0).symm)
      (tendsto_integral_withDensity_chartTransportRate hψ hU hUb hμ hcont hF hr hFs)
  have hgv : ∀ r, r < 1 → ∀ F : ℂ → ℝ, Continuous F → tsupport F ⊆ closedBall 0 r →
      Tendsto (fun k => ∫ y, F y ∂(volume.withDensity fun v => ENNReal.ofReal (discCanonicalRate k ν₀ v)))
        atTop (𝓝 (∫ y, F y ∂ν₀)) := by
    intro r hr F hF hFs
    refine Tendsto.congr (fun k => ?_) (tendsto_integral_mul_discCanonicalRate hν1 hr hF hFs)
    rw [integral_withDensity_eq_integral_toReal_smul (hg k).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [smul_eq_mul, ENNReal.toReal_ofReal (discCanonicalRate_pos k ν₀ v).le, mul_comm]
  refine Tendsto.congr (fun p => ?_)
    (tendsto_measure_exists_lt_abs_exitRateClock_sub hT hTmap he hg he0 hg0 hpow' hem hgm hνm hev hgv hη)
  rw [exitRateClock_congr (heq p.1)]

end MatedCRT
