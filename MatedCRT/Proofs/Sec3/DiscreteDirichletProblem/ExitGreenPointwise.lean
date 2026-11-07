import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.ExitGreenOccupation
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.DiscreteTailProbability

/-! Pointwise ordinary exit-time convergence from Green occupation. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- The Green sum over all cells meeting a ball equals the ordinary expected
exit time on its interior-cell domain. -/
theorem cell_green_occupation_one_eq_expectedExitTime
    (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (z : ℂ) (r : ℝ) (a : ℤ)
    (hC : (cellVertices ε η (ball z r)).Finite)
    (hmean : expectedExitTime m (interiorCellVertices ε η (ball z r)) a ≠ ⊤) :
    (∑' b : cellVertices ε η (ball z r),
      greenFn m (interiorCellVertices ε η (ball z r)) a b * 1) =
      (expectedExitTime m (interiorCellVertices ε η (ball z r)) a).toReal := by
  rw [green_occupation_tsum_eq_finset m _ _ hC a (fun _ => 1)]
  simpa using sum_greenFn_eq_expectedExitTime_toReal m _ hC.toFinset
    (fun b hb => hC.mem_toFinset.2 hb.1) a hmean

/-- Lemma 3.4 yields pointwise convergence of ordinary exit times when the
probability of infinite expected exit time vanishes. -/
theorem pointwise_expectedExitTime_of_green_and_finiteness
    {𝒮 : SpaceFillingSLEModel} (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r)
    (hfinite : Tendsto (fun ε => S.P {ω | expectedExitTime (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) = ⊤})
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    TendstoInProbability S.P
      (fun ε ω => (S.mε ε)⁻¹ * (expectedExitTime (S.mult ε ω)
        (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y)).toReal)
      (fun ω => S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x ∂S.μ ω) := by
  have hgreen := h34 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy
    (fun _ _ => 1) (fun _ => measurable_const) (fun _ => ⟨1, by simp⟩)
    (fun _ => by
      refine ⟨0, 1, by norm_num, by norm_num, ?_⟩
      intro x hx x' hx'
      simp)
  intro δ hδ
  have hlim := (hgreen δ hδ).add hfinite
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hlim)
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  calc
    _ ≤ S.P ({ω | δ < |(S.mε ε)⁻¹ * (∑' b : cellVertices ε (S.η ω) (ball z r),
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (vertexOf ε (S.η ω) y) b * 1) -
        S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * 1 ∂S.μ ω|} ∪
        {ω | expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (vertexOf ε (S.η ω) y) = ⊤}) := by
      apply measure_mono_ae
      filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω harea hp hbad
      by_contra hnot
      have hmean : expectedExitTime (S.mult ε ω)
          (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) ≠ ⊤ :=
        fun h => hnot (Or.inr h)
      have hC : (cellVertices ε (S.η ω) (ball z r)).Finite :=
        Tightness.cellVertices_finite harea.1 hp hε isBounded_ball
      have heq := cell_green_occupation_one_eq_expectedExitTime (S.mult ε ω) ε (S.η ω)
        z r (vertexOf ε (S.η ω) y) hC hmean
      simp only [mul_one] at heq
      apply hnot
      left
      simpa only [mem_ofPred_eq, heq, mul_one] using hbad
    _ ≤ _ := by simpa only [mul_one] using
      (measure_union_le _ _)

/-- The exit-time estimates make infinite expected exit times negligible at a
fixed interior point. -/
theorem expectedExitTime_finite_in_probability
    {𝒮 : SpaceFillingSLEModel} (h17 : BoundedExitTimeRVStmt)
    (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) :
    Tendsto (fun ε => S.P {ω | expectedExitTime (S.mult ε ω)
      (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) = ⊤})
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro e he
  let d : ℝ≥0∞ := min e 1
  have hd : 0 < d := lt_min he zero_lt_one
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  let b : ℝ≥0∞ := d / 2 / 2
  have hb : 0 < b := ENNReal.half_pos (ENNReal.half_pos hd.ne').ne'
  obtain ⟨q, hq, hqmass⟩ := hS.exists_ball_mass_lower_bound z hr hb
  obtain ⟨α, hα, hmoment⟩ := scaled_secondMoment_bounded_in_probability h17 h18 hscale hγ hγ2
  obtain ⟨C, hC, hCprob⟩ := hmoment ρ hρ hρ1 Ω S hS b hb
  obtain ⟨K, hK, hKscale⟩ := hscale γ hγ hγ2
  obtain ⟨ε₀, hε₀, hscaleε⟩ := hKscale Ω S hS
  obtain ⟨ε₁, hε₁, hεsmall⟩ := exists_pos_rpow_lt hα hq
  filter_upwards [hCprob, Ioo_mem_nhdsGT (lt_min hε₀ hε₁)] with ε hCε hε
  have hεpos : 0 < ε := hε.1
  have hmpos : 0 < S.mε ε :=
    (mul_pos (inv_pos.mpr (by linarith : 0 < K)) (inv_pos.mpr hεpos)).trans_le
      (hscaleε ε hεpos (hε.2.trans_le (min_le_left _ _))).1
  have hsmall : ε ^ α < q := hεsmall ε hεpos (hε.2.trans_le (min_le_right _ _))
  let E : Set Ω := {ω | ∃ D : Set ℂ,
    MeasurableSet D ∧ D ⊆ ball 0 ρ ∧ ENNReal.ofReal (ε ^ α) ≤ S.μ ω D ∧
    ∃ a ∈ cellVertices ε (S.η ω) D,
      C < ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
        exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a 2}
  let G : Set Ω := {ω | S.μ ω (ball z r) < ENNReal.ofReal q}
  have hsub : ∀ᵐ ω ∂S.P, ω ∉ E → ω ∉ G →
      expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
        (vertexOf ε (S.η ω) y) ≠ ⊤ := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω harea hp hE hG
    have hmass : ENNReal.ofReal (ε ^ α) ≤ S.μ ω (ball z r) :=
      (ENNReal.ofReal_le_ofReal hsmall.le).trans (le_of_not_gt hG)
    have ha : vertexOf ε (S.η ω) y ∈ cellVertices ε (S.η ω) (ball z r) :=
      ⟨y, Tightness.mem_cell_vertexOf harea.1 hp harea.2.2.1 hεpos y, hy⟩
    have hmoment' : ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
        exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (vertexOf ε (S.η ω) y) 2 ≤ C := by
      apply le_of_not_gt
      intro hbad
      exact hE ⟨ball z r, isOpen_ball.measurableSet, hball, hmass, _, ha, hbad⟩
    have hc : 0 < Real.toNNReal (S.mε ε)⁻¹ := by simp [Real.toNNReal_pos, hmpos]
    have hfin := exitTimeMoment_ne_top_of_scaled_bound _ _ _ _ hc C hC hmoment'
    exact ne_of_lt ((expectedExitTime_le_secondMoment _ _ _).trans_lt (lt_top_iff_ne_top.2 hfin))
  apply le_of_lt
  calc
    _ ≤ S.P (E ∪ G) := by
      apply measure_mono_ae
      filter_upwards [hsub] with ω hω hbad
      by_contra hn
      exact hω (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)) hbad
    _ ≤ S.P E + S.P G := measure_union_le _ _
    _ ≤ b + b := add_le_add hCε hqmass.le
    _ = d / 2 := ENNReal.add_halves _
    _ < e := (ENNReal.half_lt_self hd.ne' hdtop).trans_le (min_le_left _ _)

/-- Pointwise convergence of ordinary exit times follows from Lemma 3.4 and
the exit-time and median-scaling estimates. -/
theorem pointwise_expectedExitTime_of_green_and_estimates
    {𝒮 : SpaceFillingSLEModel} (h34 : IntegralConvergenceGreenFunctionStmt 𝒮)
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) :
    TendstoInProbability S.P
      (fun ε ω => (S.mε ε)⁻¹ * (expectedExitTime (S.mult ε ω)
        (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y)).toReal)
      (fun ω => S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x ∂S.μ ω) :=
  pointwise_expectedExitTime_of_green_and_finiteness h34 hγ hγ2 hρ hρ1 S hS hr hball hy
    (expectedExitTime_finite_in_probability h17 h18 hscale hγ hγ2 hρ hρ1 S hS hr hball hy)

end MatedCRT

#print axioms MatedCRT.cell_green_occupation_one_eq_expectedExitTime
#print axioms MatedCRT.pointwise_expectedExitTime_of_green_and_finiteness

#print axioms MatedCRT.expectedExitTime_finite_in_probability
#print axioms MatedCRT.pointwise_expectedExitTime_of_green_and_estimates
