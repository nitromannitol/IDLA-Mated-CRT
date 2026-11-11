import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.GMSCellSizeEvent
import MatedCRT.Proofs.Sec3.UniformConvergenceGreenKernel.EnvironmentCells

/-! # Environment-measurable cell-size event -/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology _root_.HarmonicBalls

/-- For continuous curves, exceeding a nonnegative diameter is an open
condition in the topology of uniform convergence on compact sets. -/
theorem isOpen_curve_cell_diam_gt (ε d : ℝ) (k : ℤ) (hd : 0 ≤ d) :
    IsOpen {p : C(ℝ, ℂ) | d < diam (cell ε p k)} := by
  let I : Set ℝ := Icc (ε * (k - 1)) (ε * k)
  have heq : {p : C(ℝ, ℂ) | d < diam (cell ε p k)} =
      ⋃ u : I, ⋃ v : I, {p : C(ℝ, ℂ) | d < dist (p u) (p v)} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      by_contra hn
      push Not at hn
      have hdiam : diam (cell ε p k) ≤ d := by
        apply diam_le_of_forall_dist_le hd
        rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
        exact hn ⟨u, hu⟩ ⟨v, hv⟩
      exact (not_lt_of_ge hdiam) h
    · rintro ⟨u, v, huv⟩
      have hu : p u ∈ cell ε p k := ⟨u, u.property, rfl⟩
      have hv : p v ∈ cell ε p k := ⟨v, v.property, rfl⟩
      exact huv.trans_le (dist_le_diam_of_mem (isCompact_Icc.image p.continuous).isBounded hu hv)
  rw [heq]
  exact isOpen_iUnion fun u => isOpen_iUnion fun v =>
    isOpen_lt continuous_const ((continuous_eval_const (u : ℝ)).dist (continuous_eval_const (v : ℝ)))

/-- The upper cell-size event has a field-and-curve measurable version. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_measurable_cellSize
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ)
    (ε ρ d : ℝ) (hd : 0 ≤ d) :
    ∃ A : Set Ω, MeasurableSet[S.envSigma] A ∧ ∀ᵐ ω ∂S.P,
      (ω ∈ A ↔ ∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ d) := by
  obtain ⟨η, hηm, hη⟩ := hS.exists_envSigma_measurable_curve
  let A : Set Ω := {ω | ∀ i, (cell ε (η ω) i ∩ ball 0 ρ).Nonempty →
    diam (cell ε (η ω) i) ≤ d}
  refine ⟨A, ?_, ?_⟩
  · let : MeasurableSpace Ω := S.envSigma
    have hi : ∀ i : ℤ, MeasurableSet {ω | (cell ε (η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (η ω) i) ≤ d} := by
      intro i
      have hm : MeasurableSet {ω | (cell ε (η ω) i ∩ ball 0 ρ).Nonempty} :=
        (isOpen_curve_cell_meets ε i (ball 0 ρ) isOpen_ball).measurableSet.preimage hηm
      have hb : MeasurableSet {ω | d < diam (cell ε (η ω) i)} :=
        (isOpen_curve_cell_diam_gt ε d i hd).measurableSet.preimage hηm
      convert hm.compl.union hb.compl using 1
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, not_lt]
      exact imp_iff_not_or
    convert MeasurableSet.iInter hi using 1
    ext ω
    simp only [A, mem_ofPred_eq, mem_iInter]
  · filter_upwards [hη] with ω hω
    change (∀ i, (cell ε (η ω) i ∩ ball 0 ρ).Nonempty →
      diam (cell ε (η ω) i) ≤ d) ↔ _
    rw [hω]

/-- The polynomial cell-size estimate admits an environment-measurable
good event at any exponent below the critical exponent. -/
theorem MatedCRTEnv.IsValid.exists_envSigma_cellSize_polyHighProb
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ a : ℝ} (hS : S.IsValid 𝒮 γ)
    (h28 : CellSizeEstimateStmt 𝒮) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (ha : a < 2 / (2 + γ) ^ 2) :
    ∃ A : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (A ε)) ∧
      PolyHighProb S.P A ∧ ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
        (ω ∈ A ε ↔ ∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
          diam (cell ε (S.η ω) i) ≤ ε ^ a) := by
  classical
  choose A hAm hAe using fun ε : ℝ =>
    hS.exists_envSigma_measurable_cellSize ε ρ (max 0 (ε ^ a)) (le_max_left _ _)
  have hmatch : ∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (ω ∈ A ε ↔ ∀ i, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a) := by
    intro ε hε
    simpa only [max_eq_right (Real.rpow_nonneg hε.le _)] using hAe ε
  refine ⟨A, hAm, ?_, hmatch⟩
  obtain ⟨p, hp, C, ε₀, hε₀, hprob⟩ :=
    cellSize_polyHighProb_of_lt_critical 𝒮 h28 hγ hγ2 hρ hρ1 ha S hS
  refine ⟨p, hp, C, ε₀, hε₀, ?_⟩
  intro ε hε hε₀'
  have heq : S.P (A ε)ᶜ = S.P {ω | ¬ ∀ i,
      (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a} := by
    apply measure_congr
    filter_upwards [hmatch ε hε] with ω hω
    exact propext (not_congr hω)
  rw [heq]
  exact hprob ε hε hε₀'

end MatedCRT

#print axioms MatedCRT.isOpen_curve_cell_diam_gt
#print axioms MatedCRT.MatedCRTEnv.IsValid.exists_envSigma_measurable_cellSize

#print axioms MatedCRT.MatedCRTEnv.IsValid.exists_envSigma_cellSize_polyHighProb
