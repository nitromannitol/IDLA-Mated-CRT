import MatedCRT.FirstPass.S3S4c
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.WalkKilledConvergence

/-!
# First pass: the fixed-time truncated quenched laws, derived from Theorem 2.11 (task fp-S3-truncated-laws-bridge)

Target: `FrozenTruncatedQuenchedLawsFixedTime 𝒮` (`MatedCRT/FirstPass/Frozen/S3S4b.lean`).

Route, with each step tied to a declaration:
1. The quenched expectation of the discrete occupation is the discrete truncated occupation
   (`MatedCRT.S3S4c.quenched_integral_eq_truncatedDiscrete`).
2. The walk-side limit of the continuum truncated occupation of the interpolated walk is Theorem 2.11 for path functionals
   continuous at regular exits (`walkFunctional_tendstoInProbability_of_ae_continuousWithin`), applied to
   `truncatedOccupationFunctional`. Here the walk starts at `y ∈ B_r(z)`, not at the centre `z`; the proof of
   `truncatedOccupation_tendstoInProbability_of_holder` is repeated with the starting point separated from the centre
   (`truncatedOccupation_tendstoInProbability_of_start`).
3. The LBM side: `FrozenLBMGreenOccupationRescaled` gives a.s. finite exit times, on which the `ENNReal` truncation agrees with
   the `toReal` truncation (`MatedCRT.S3S4c.toReal_min_ofReal_eq`), as in `truncatedDetFixedTimeStep_of_quenched`.
4. NAMED INPUT `TruncatedDiscreteWalkComparisonStmt`: the discrete truncated occupation and the continuum truncated occupation
   of the interpolated walk differ, in probability, by a term tending to 0. The repository contains no written argument for
   this comparison (only the discrete-to-discrete bound `truncatedDiscreteOccupation_sub_le`); this is the open step.
-/

namespace MatedCRT.TruncatedLawsBridge

open MeasureTheory Set Metric Filter Topology MarkovProcess
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- **NAMED INPUT (open step, no written argument).** The discrete truncated occupation of the killed walk (the quenched
summand with `⌊T m_ε⌋` steps, `truncatedDiscreteOccupation`) and the continuum truncated occupation of the interpolated
walk, both started at `y ∈ B_r(z)`, differ by a term that tends to `0` in probability as `ε → 0`. -/
def TruncatedDiscreteWalkComparisonStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ g : ℂ → ℝ, Continuous g → (∃ M : ℝ, ∀ x, |g x| ≤ M) →
  (∃ (C χ : ℝ≥0), 0 < χ ∧ HolderOnWith C χ g (ball z r)) →
  ∀ T : ℝ, 0 < T → TendstoInProbability S.P
    (fun ε ω => truncatedDiscreteOccupation S (ball z r) y (fun _ => g) ⌊T * S.mε ε⌋₊ ε ω
      - ∫ x, truncatedOccupationFunctional (ball z r) g T (interpolatedWalk ε (S.η ω) (S.mε ε) x)
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (fun _ : Ω => (0 : ℝ))

/-- Theorem 2.11 for the truncated occupation functional, for the walk started at `y ∈ B_r(z)` (the proof of
`truncatedOccupation_tendstoInProbability_of_holder` with the starting point separated from the centre `z`). -/
theorem truncatedOccupation_tendstoInProbability_of_start {𝒮 : SpaceFillingSLEModel}
    (h211 : RandomWalkToLBMStmt 𝒮) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ) (hm : 0 < S.m₀)
    {z y : ℂ} {r : ℝ} (hr : 0 < r) (hy : y ∈ ball z r) {g : ℂ → ℝ} (hg : Continuous g) {M : ℝ}
    (hgM : ∀ x, |g x| ≤ M) {C χ : ℝ≥0} (hχ : 0 < χ) (hhol : HolderOnWith C χ g (ball z r)) {T : ℝ}
    (hT : 0 ≤ T) :
    TendstoInProbability S.P
      (fun ε ω => ∫ x, truncatedOccupationFunctional (ball z r) g T (interpolatedWalk ε (S.η ω) (S.mε ε) x)
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, truncatedOccupationFunctional (ball z r) g T (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion y) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hgM 0)
  have hM : ∀ w : ℝ≥0 → ℂ, Continuous w → |truncatedOccupationFunctional (ball z r) g T w| ≤ M * T :=
    fun w _ => abs_truncatedOccupationFunctional_le hM0 hT hgM w
  have hGW : ∀ (ε : ℝ) (ω : Ω), AEStronglyMeasurable
      (fun x => truncatedOccupationFunctional (ball z r) g T (interpolatedWalk ε (S.η ω) (S.mε ε) x))
      (srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) := fun ε ω =>
    aestronglyMeasurable_truncatedOccupation_interpolatedWalk ε (S.η ω) (S.mε ε) z r T hg
  have hclock := hS.isLQGClock
  have hreg := hS.ae_rescaledLBM_ball_regular_of_brownian_outward_radial_excursion hm hy (hexc y z r hy)
  have hfin := hS.ae_rescaledLBMExitTime_any_ball_lt_top hm y z r
  have hcl : closure (ball z r) = closedBall z r := closure_ball z hr.ne'
  have hcont : ∀ᵐ ω ∂S.P, ∀ᵐ b ∂planarBrownianMotion y,
      rescaledLBMPath (S.clock ω) S.m₀ b ∈ {w : ℝ≥0 → ℂ | Continuous w} ∧
        PathFunctionalContinuousWithinAt {w : ℝ≥0 → ℂ | Continuous w}
          (truncatedOccupationFunctional (ball z r) g T) (rescaledLBMPath (S.clock ω) S.m₀ b) := by
    filter_upwards [hclock, hreg, hfin] with ω hω hreg_ω hfin_ω
    filter_upwards [(hω y).2, hreg_ω, hfin_ω] with b hb hregb hfinb
    have hcb : Continuous (rescaledLBMPath (S.clock ω) S.m₀ b) := continuous_rescaledLBMPath hb
    refine ⟨hcb, ?_⟩
    have hfin' : ContinuousPath.exitTime (ball z r) (⟨_, hcb⟩ : ContinuousPath ℂ) < ⊤ :=
      (ContinuousPath.exitTime_lt_top_iff _ _).2 (exists_not_mem_of_pathExitTime_lt_top hfinb)
    have hreg' : ∃ᶠ t in 𝓝[>] (ContinuousPath.exitTime (ball z r) (⟨_, hcb⟩ : ContinuousPath ℂ)).toNNReal,
        (⟨_, hcb⟩ : ContinuousPath ℂ) t ∉ closedBall z r := by
      refine hregb.mono fun t ht => ?_
      rw [← hcl]
      exact ht
    exact pathFunctionalContinuousWithinAt_truncatedOccupation (⟨_, hcb⟩ : ContinuousPath ℂ) z hfin' hreg'
      (fun x _ => hgM x) hχ hhol hT
  exact walkFunctional_tendstoInProbability_of_ae_continuousWithin 𝒮 h211 hX hγ hγ2 S hS y
    (truncatedOccupationFunctional (ball z r) g T) (M * T) hM hGW hcont

/-- Convergence in probability is stable under adding a sequence tending to `0` in probability. -/
theorem tendstoInProbability_add_of_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D X : ℝ → Ω → ℝ} {Y : Ω → ℝ}
    (hD : TendstoInProbability P D (fun _ : Ω => (0 : ℝ))) (hX : TendstoInProbability P X Y) :
    TendstoInProbability P (fun ε ω => D ε ω + X ε ω) Y := by
  intro δ hδ
  have h2 : (0 : ℝ) < δ / 2 := by positivity
  have hsum : Tendsto (fun ε => P {ω | δ / 2 < |D ε ω - (0 : ℝ)|} + P {ω | δ / 2 < |X ε ω - Y ω|})
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hD (δ / 2) h2).add (hX (δ / 2) h2)
    rwa [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le) ?_
  intro ε
  have hsub : {ω | δ < |D ε ω + X ε ω - Y ω|} ⊆
      {ω | δ / 2 < |D ε ω - (0 : ℝ)|} ∪ {ω | δ / 2 < |X ε ω - Y ω|} := by
    intro ω hω
    have htri := abs_add_le (D ε ω - 0) (X ε ω - Y ω)
    have heq : D ε ω - 0 + (X ε ω - Y ω) = D ε ω + X ε ω - Y ω := by ring
    rw [heq] at htri
    rcases lt_or_ge (δ / 2) |D ε ω - 0| with h1 | h1
    · exact Or.inl h1
    rcases lt_or_ge (δ / 2) |X ε ω - Y ω| with h2 | h2
    · exact Or.inr h2
    have hω' : δ < |D ε ω + X ε ω - Y ω| := hω
    linarith
  exact (measure_mono hsub).trans (measure_union_le _ _)

/-- **Fixed-time truncated quenched laws, from Theorem 2.11** (`FrozenTruncatedQuenchedLawsFixedTime 𝒮`, the statement
of `MatedCRT/FirstPass/Frozen/S3S4b.lean`). Inputs: Theorem 2.11 (`RandomWalkToLBMStmt`), the measurability input
`LBMPathFunctionalMeasurableStep`, the planar Brownian outward excursion `BrownianOutwardExcursionAtExitStep`, the Revuz
occupation identity `FrozenLBMGreenOccupationRescaled` (only its a.s. finite exit clause is used), and the named open step
`TruncatedDiscreteWalkComparisonStmt`. -/
theorem frozenTruncatedQuenchedLawsFixedTime_of_211 {𝒮 : SpaceFillingSLEModel}
    (h211 : RandomWalkToLBMStmt 𝒮) (hX : LBMPathFunctionalMeasurableStep 𝒮)
    (hexc : BrownianOutwardExcursionAtExitStep) (hrev : FrozenLBMGreenOccupationRescaled 𝒮)
    (hN3 : TruncatedDiscreteWalkComparisonStmt 𝒮) : FrozenTruncatedQuenchedLawsFixedTime 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hball hy g hgc hgb hgh T hT
  have hD := hN3 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy g hgc hgb hgh T hT
  obtain ⟨M, hM⟩ := hgb
  obtain ⟨C, χ, hχ, hhol⟩ := hgh
  have hm : 0 < S.m₀ := hS.m₀_pos hγ hγ2
  have hW := truncatedOccupation_tendstoInProbability_of_start h211 hX hexc hγ hγ2 S hS hm hr hy hgc hM hχ
    hhol hT.le
  have hsum := tendstoInProbability_add_of_zero hD hW
  have hae := hrev γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy
  have hY : (fun ω => ∫ b, rescaledLBMOccupation S ω (ball z r) (ENNReal.ofReal T) g b
      ∂planarBrownianMotion y) =ᵐ[S.P]
      (fun ω => ∫ b, truncatedOccupationFunctional (ball z r) g T (rescaledLBMPath (S.clock ω) S.m₀ b)
        ∂planarBrownianMotion y) := by
    filter_upwards [hae] with ω hω
    apply integral_congr_ae
    filter_upwards [hω.1] with b hb
    unfold rescaledLBMOccupation truncatedOccupationFunctional
    rw [MatedCRT.S3S4c.toReal_min_ofReal_eq hT.le hb.ne]
  have hfun : (fun ε ω => ∫ q, quenchedDiscreteOccupation S ω (ball z r) g T ε q
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) =
      (fun ε ω => (truncatedDiscreteOccupation S (ball z r) y (fun _ => g) ⌊T * S.mε ε⌋₊ ε ω
        - ∫ x, truncatedOccupationFunctional (ball z r) g T (interpolatedWalk ε (S.η ω) (S.mε ε) x)
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
        + ∫ x, truncatedOccupationFunctional (ball z r) g T (interpolatedWalk ε (S.η ω) (S.mε ε) x)
          ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)) := by
    funext ε ω
    rw [sub_add_cancel, MatedCRT.S3S4c.quenched_integral_eq_truncatedDiscrete]
  rw [hfun]
  exact MatedCRT.S3S4c.tendstoInProbability_congr_ae hY.symm hsum

end MatedCRT.TruncatedLawsBridge
