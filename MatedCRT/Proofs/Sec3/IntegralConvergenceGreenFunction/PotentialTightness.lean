import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.LogPotentialMeasurable
import MatedCRT.Proofs.Infra.Setting
import MatedCRT.Draft.Section2
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.UniformSecondMoment

/-! Tightness of the logarithmic potential on an enlarged ball. -/

namespace MatedCRT

open MeasureTheory Set Metric HarmonicBalls Filter Topology
open scoped ENNReal NNReal

/-- An almost-everywhere finite extended nonnegative random variable has
arbitrarily large finite quantiles under a finite measure. -/
theorem exists_nat_measure_gt_lt {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ≥0∞)
    (hX : AEMeasurable X P) (hfinite : ∀ᵐ ω ∂P, X ω < ⊤)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, P {ω | (n : ℝ≥0∞) < X ω} < δ := by
  let E : ℕ → Set Ω := fun n => {ω | (n : ℝ≥0∞) < X ω}
  have hnull (n : ℕ) : NullMeasurableSet (E n) P :=
    hX.nullMeasurableSet_preimage measurableSet_Ioi
  have hant : Antitone E := by
    intro m n hmn ω hω
    change (n : ℝ≥0∞) < X ω at hω
    change (m : ℝ≥0∞) < X ω
    exact lt_of_le_of_lt (by exact_mod_cast hmn) hω
  have hzero : P (⋂ n, E n) = 0 := by
    apply measure_mono_null _ (ae_iff.mp hfinite)
    intro ω hω hωfinite
    obtain ⟨n, hn⟩ := exists_nat_gt (X ω).toReal
    have hle : X ω ≤ (n : ℝ≥0∞) := by
      calc
        X ω = ENNReal.ofReal (X ω).toReal := (ENNReal.ofReal_toReal hωfinite.ne).symm
        _ ≤ ENNReal.ofReal n := ENNReal.ofReal_le_ofReal hn.le
        _ = (n : ℝ≥0∞) := by simp
    exact (not_lt_of_ge hle) (mem_iInter.mp hω n)
  have hlim : Tendsto (fun n => P (E n)) atTop (𝓝 0) := by
    rw [← hzero]
    exact tendsto_measure_iInter_atTop hnull hant ⟨0, measure_ne_top P _⟩
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  exact ⟨n, hn⟩

/-- The largest-exit-time random variable of an LQG measure on a ball inside
the unit disk is bounded in probability. -/
theorem MatedCRTEnv.IsValid.exists_largestExitTimeRV_quantile
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (h17 : BoundedExitTimeRVStmt) (hγ : 0 < γ) (hγ2 : γ < 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, S.P {ω | (n : ℝ≥0∞) < largestExitTimeRV (S.μ ω) (ball 0 ρ)} < δ := by
  let := hS.isProbabilityMeasure
  obtain ⟨q, hq, hq17⟩ := h17 γ hγ hγ2
  have hae := (hq17 ρ hρ hρ1 Ω S.P S.hC S.hcirc S.μ hS.isConeField).1
  have hfinite : ∀ᵐ ω ∂S.P, largestExitTimeRV (S.μ ω) (ball 0 ρ) < ⊤ := by
    filter_upwards [hae] with ω hω
    have hle : largestExitTimeRV (S.μ ω) (ball 0 ρ) ≤
        (⨆ (D : Set ℂ) (_ : D ⊆ ball 0 ρ), largestExitTimeRV (S.μ ω) D) :=
      le_iSup₂_of_le (ball 0 ρ) Subset.rfl le_rfl
    exact hle.trans_lt hω
  exact exists_nat_measure_gt_lt S.P _ (hS.aemeasurable_largestExitTimeRV_ball ρ) hfinite hδ

/-- The normalized second moments are uniformly bounded in probability over
all admissible domains and starting vertices. -/
theorem scaled_secondMoment_bounded_in_probability {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮)
    (hscale : MepsScalingInput 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ e : ℝ≥0∞, 0 < e → ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ D : Set ℂ,
        MeasurableSet D ∧ D ⊆ ball 0 ρ ∧ ENNReal.ofReal (ε ^ α) ≤ S.μ ω D ∧
        ∃ a ∈ cellVertices ε (S.η ω) D,
          C < ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a 2} ≤ e := by
  obtain ⟨α, hα, hmoment⟩ := scaled_secondMoment_finite_bound_polyHighProb h17 h18 hscale hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro ρ hρ hρ1 Ω _ S hS e he
  obtain ⟨B, hB, hP⟩ := hmoment ρ hρ hρ1
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  have hρ' : 0 < (1 + ρ) / 2 := by linarith
  have hρ'1 : (1 + ρ) / 2 < 1 := by linarith
  obtain ⟨n, hn⟩ := hS.exists_largestExitTimeRV_quantile h17 hγ hγ2 hρ' hρ'1 he2
  refine ⟨ENNReal.ofReal B * (n : ℝ≥0∞) ^ 2,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness), ?_⟩
  obtain ⟨p, hp, K, r₀, hr₀, hpol⟩ := hP Ω S hS
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (K * ε ^ p)) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_ofReal_mul_rpow K 1 p hp
  filter_upwards [Ioo_mem_nhdsGT hr₀, (ENNReal.tendsto_nhds_zero.1 hlim) (e / 2) he2] with ε hε hsmall
  let E : Set Ω := {ω | largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) < ⊤ ∧
    ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ →
      ENNReal.ofReal (ε ^ α) ≤ S.μ ω D →
      ∀ a ∈ cellVertices ε (S.η ω) D,
        ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
          exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a 2 ≤
          ENNReal.ofReal B * (largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))) ^ 2}
  calc
    _ ≤ S.P (Eᶜ ∪ {ω | (n : ℝ≥0∞) < largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))}) := by
      apply measure_mono
      rintro ω ⟨D, hD, hDsub, hμ, a, ha, hbad⟩
      by_cases hE : ω ∈ E
      · right
        by_contra hnle
        have hle : largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2)) ≤ n := le_of_not_gt hnle
        have hbound := hE.2 D hD hDsub hμ a ha
        have : ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 2 *
            exitTimeMoment (S.mult ε ω) (interiorCellVertices ε (S.η ω) D) a 2 ≤
            ENNReal.ofReal B * (n : ℝ≥0∞) ^ 2 := hbound.trans (by gcongr)
        exact (not_lt_of_ge this) hbad
      · exact Or.inl hE
    _ ≤ S.P Eᶜ + S.P {ω | (n : ℝ≥0∞) < largestExitTimeRV (S.μ ω) (ball 0 ((1 + ρ) / 2))} :=
      measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add ((hpol ε hε.1 hε.2).trans hsmall) hn.le
    _ = e := ENNReal.add_halves e

/-- The normalized exit-time tails converge to zero uniformly in probability
over admissible domains and starting vertices. -/
theorem scaled_exitTime_tail_small_in_probability {𝒮 : SpaceFillingSLEModel}
    (h17 : BoundedExitTimeRVStmt) (h18 : ExitTimeUpperBoundStmt 𝒮)
    (hscale : MepsScalingInput 𝒮) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ t : ℝ, 0 < t → ∀ e : ℝ≥0∞, 0 < e → ∃ T : ℝ, 0 < T ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), S.P {ω | ∃ D : Set ℂ,
        MeasurableSet D ∧ D ⊆ ball 0 ρ ∧ ENNReal.ofReal (ε ^ α) ≤ S.μ ω D ∧
        ∃ a ∈ cellVertices ε (S.η ω) D,
          ENNReal.ofReal t < (∫⁻ x in {x | ENNReal.ofReal T ≤
            ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) *
              (vExitTime (interiorCellVertices ε (S.η ω) D) x : ℝ≥0∞)},
            ((Real.toNNReal (S.mε ε)⁻¹ : ℝ≥0) : ℝ≥0∞) *
              (vExitTime (interiorCellVertices ε (S.η ω) D) x : ℝ≥0∞)
              ∂srwLaw (S.mult ε ω) a)} ≤ e := by
  obtain ⟨α, hα, hmoment⟩ := scaled_secondMoment_bounded_in_probability h17 h18 hscale hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro ρ hρ hρ1 Ω _ S hS t ht e he
  obtain ⟨C, hC, hprob⟩ := hmoment ρ hρ hρ1 Ω S hS e he
  let T : ℝ := (C.toReal + 1) / t
  have hT : 0 < T := div_pos (by positivity) ht
  have hTC : C < ENNReal.ofReal T * ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_mul hT.le]
    have heq : T * t = C.toReal + 1 := by dsimp [T]; field_simp
    rw [heq]
    calc
      C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC.ne).symm
      _ < ENNReal.ofReal (C.toReal + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  refine ⟨T, hT, ?_⟩
  filter_upwards [hprob] with ε hε
  apply (measure_mono ?_).trans hε
  rintro ω ⟨D, hD, hDsub, hμ, a, ha, hbad⟩
  refine ⟨D, hD, hDsub, hμ, a, ha, ?_⟩
  have htail := scaled_exitTime_tail_le_secondMoment (S.mult ε ω)
    (interiorCellVertices ε (S.η ω) D) a (Real.toNNReal (S.mε ε)⁻¹)
    (ENNReal.ofReal T) ENNReal.ofReal_ne_top
  apply hTC.trans_le
  calc
    _ ≤ _ := by gcongr
    _ ≤ _ := htail

end MatedCRT
