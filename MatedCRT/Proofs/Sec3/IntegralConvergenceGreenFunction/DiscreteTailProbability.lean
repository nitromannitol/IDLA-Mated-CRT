import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.OccupationSecondMoment
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.AreaParametrizedMass
import MatedCRT.Proofs.Infra.MatingOfTrees

/-! Truncation of discrete Green occupation in probability. -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Lemmas 2.17 and 2.18 and the median scaling estimate imply the discrete
Green occupation tail bound needed in the proof of Lemma 3.4. -/
theorem discrete_green_occupation_tail_in_probability
    {𝒮 : SpaceFillingSLEModel} (h17 : BoundedExitTimeRVStmt)
    (h18 : ExitTimeUpperBoundStmt 𝒮) (hscale : MepsScalingInput 𝒮)
    {γ ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {r : ℝ} {z y : ℂ} (hr : 0 < r) (hball : ball z r ⊆ ball 0 ρ)
    (hy : y ∈ ball z r) (f : Ω → ℂ → ℝ)
    (hfmeas : ∀ x, Measurable[S.envSigma] fun ω => f ω x)
    (hfbound : ∀ ω, ∃ M : ℝ, ∀ x ∈ ball z r, |f ω x| ≤ M)
    (hfcont : ∀ ω, IsHolderContinuousOn (f ω) (ball z r)) :
    ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ T : ℝ, 0 < T ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | t < |(S.mε ε)⁻¹ *
        (∑' x : cellVertices ε (S.η ω) (ball z r),
          greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (vertexOf ε (S.η ω) y) x * f ω (vertexPoint ε (S.η ω) x)) -
          truncatedDiscreteOccupation S (ball z r) y f ⌊T * S.mε ε⌋₊ ε ω|} < e := by
  intro t ht e he
  let d : ℝ≥0∞ := min e 1
  have hd : 0 < d := lt_min he zero_lt_one
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  let qprob : ℝ≥0∞ := (d / 2) / 2 / 2
  have hqprob : 0 < qprob := ENNReal.half_pos (ENNReal.half_pos (ENNReal.half_pos hd.ne').ne').ne'
  obtain ⟨M, hM, hMf⟩ := hS.exists_testFunction_bound_in_probability z r f hfmeas hfcont hfbound hqprob
  obtain ⟨q, hq, hqmass⟩ := hS.exists_ball_mass_lower_bound z hr hqprob
  obtain ⟨α, hα, hmoment⟩ := scaled_secondMoment_bounded_in_probability h17 h18 hscale hγ hγ2
  obtain ⟨C, hC, hCprob⟩ := hmoment ρ hρ hρ1 Ω S hS qprob hqprob
  obtain ⟨K, hK, hKscale⟩ := hscale γ hγ hγ2
  obtain ⟨ε₀, hε₀, hscaleε⟩ := hKscale Ω S hS
  obtain ⟨ε₁, hε₁, hεsmall⟩ := exists_pos_rpow_lt hα hq
  let T : ℝ := ((M + 1) * (C.toReal + 1)) / t
  have hT : 0 < T := div_pos (by positivity) ht
  have hbound : ENNReal.ofReal M * C < ENNReal.ofReal T * ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_mul hT.le]
    have heq : T * t = (M + 1) * (C.toReal + 1) := by dsimp [T]; field_simp
    rw [heq, ← ENNReal.ofReal_toReal hC.ne, ← ENNReal.ofReal_mul hM.le]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
    simp only [ENNReal.toReal_ofReal C.toReal_nonneg]
    nlinarith [C.toReal_nonneg]
  refine ⟨T, hT, ?_⟩
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
  let F : Set Ω := {ω | ∃ x ∈ ball z r, M < |f ω x|}
  let G : Set Ω := {ω | S.μ ω (ball z r) < ENNReal.ofReal q}
  have hsub : ∀ᵐ ω ∂S.P, ω ∉ E → ω ∉ F → ω ∉ G →
      ¬ t < |(S.mε ε)⁻¹ * (∑' x : cellVertices ε (S.η ω) (ball z r),
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
          (vertexOf ε (S.η ω) y) x * f ω (vertexPoint ε (S.η ω) x)) -
        truncatedDiscreteOccupation S (ball z r) y f ⌊T * S.mε ε⌋₊ ε ω| := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact] with ω harea hp hE hF hG
    have hf : ∀ w ∈ ball z r, |f ω w| ≤ M := by
      intro w hw
      exact le_of_not_gt (fun hw' => hF ⟨w, hw, hw'⟩)
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
    have herr := normalized_cell_green_error_mul_le_secondMoment S ε ω z y r f M hM.le
      hf hεpos harea.1 hp hfin hmpos T
    intro hbad
    have hbad' : ENNReal.ofReal t < ENNReal.ofReal |(S.mε ε)⁻¹ *
        (∑' x : cellVertices ε (S.η ω) (ball z r),
          greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (vertexOf ε (S.η ω) y) x * f ω (vertexPoint ε (S.η ω) x)) -
        truncatedDiscreteOccupation S (ball z r) y f ⌊T * S.mε ε⌋₊ ε ω| :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).2 hbad
    have hle : ENNReal.ofReal T * ENNReal.ofReal t ≤ ENNReal.ofReal M * C := by
      calc
        _ ≤ ENNReal.ofReal T * _ := by gcongr
        _ ≤ _ := herr
        _ ≤ _ := by gcongr
    exact (not_le_of_gt hbound) hle
  calc
    _ ≤ S.P (E ∪ (F ∪ G)) := by
      apply measure_mono_ae
      filter_upwards [hsub] with ω hω hbad
      by_contra hn
      exact hω (fun h => hn (Or.inl h)) (fun h => hn (Or.inr (Or.inl h)))
        (fun h => hn (Or.inr (Or.inr h))) hbad
    _ ≤ S.P E + (S.P F + S.P G) :=
      (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ qprob + (qprob + qprob) := add_le_add hCε (add_le_add hMf.le hqmass.le)
    _ ≤ d / 2 := by
      dsimp [qprob]
      calc
        _ ≤ ((d / 2) / 2) + ((d / 2) / 2) := by
          gcongr
          · exact ENNReal.half_le_self
          · exact le_of_eq (ENNReal.add_halves _)
        _ = d / 2 := ENNReal.add_halves _
    _ < e := (ENNReal.half_lt_self hd.ne' hdtop).trans_le (min_le_left _ _)

end MatedCRT
