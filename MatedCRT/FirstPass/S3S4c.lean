import MatedCRT.FirstPass.Frozen.S3S4b
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.Truncation
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.FixedTimeReduction
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.TruncatedStepsProved
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.GreenIntegralMeasurable
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ContinuumOccupation
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.ContinuumTailAssembly
import MatedCRT.Steps.Sec2.BoundedExitTimeRV

/-!
# First pass: paper-owned result 3.4 on the quenched route

`MatedCRT.S3S4c.firstPass_3_4` proves `IntegralConvergenceGreenFunctionStmt` (Draft Lemma 3.4, corrected [C1, C16]) from

* the Draft statements `VolumeGrowthStmt` (Lemma 2.7, giving Lemma 2.17 `BoundedExitTimeRVStmt`) and
  `ExitTimeUpperBoundStmt` (Lemma 2.18, which gives the quenched exit-time moments used to remove the time truncation);
* the EXTERNAL input `MepsScalingInput` (scaling of `m_ε`);
* the FIRST-PASS FROZEN quenched inputs of `MatedCRT/FirstPass/Frozen/S3S4b.lean`:
  `FrozenLBMGreenOccupationRescaled` (quenched expected occupation of the median-rescaled LBM, `c₀ = 2/m₀`) and
  `FrozenTruncatedQuenchedLawsFixedTime` (convergence in probability of the quenched laws of the truncated discrete
  occupation at fixed time `T`).

No sample-path step is used: the deterministic fixed-time input of the lifting lemma `truncatedOccupationFixedTimeStep_of_det`
is supplied by `truncatedDetFixedTimeStep_of_quenched` below, from the quenched inputs. The lifting to environment-measurable
`f` (countable approximation), the truncation tail and the continuum limit are the proved helpers of
`MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/`.
-/

namespace MatedCRT.S3S4c

open MeasureTheory Set Metric MarkovProcess Filter Topology
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- The walk has not left `A` before time `n` iff it stays in `A` at all times `j ≤ n` (`vExitTime` is the first exit
time, Lehmann-Ornstein style: `τ_A = inf {n ≥ 0 : x n ∉ A}`). -/
theorem lt_vExitTime_iff (A : Set ℤ) (x : ℕ → ℤ) (n : ℕ) :
    (n : ℕ∞) < vExitTime A x ↔ ∀ j ≤ n, x j ∈ A := by
  classical
  unfold vExitTime
  split_ifs with h
  · constructor
    · intro hlt j hj
      by_contra hj'
      have hle : Nat.find h ≤ j := Nat.find_min' h hj'
      have : n < Nat.find h := by exact_mod_cast hlt
      omega
    · intro hall
      have hlt : n < Nat.find h := by
        by_contra hle
        push Not at hle
        exact absurd (hall _ hle) (Nat.find_spec h)
      exact_mod_cast hlt
  · push Not at h
    exact ⟨fun _ j _ => h j, fun _ => ENat.natCast_lt_top n⟩

/-- The quenched discrete occupation (the summand of `Q_ε` in `FrozenTruncatedQuenchedLawsFixedTime`), averaged over the
walk law from `vertexOf ε η y`, is the truncated discrete occupation `truncatedDiscreteOccupation` of Truncation.lean. -/
theorem quenched_integral_eq_truncatedDiscrete {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω)
    (D : Set ℂ) (y : ℂ) (g : ℂ → ℝ) (T ε : ℝ) :
    ∫ q, quenchedDiscreteOccupation S ω D g T ε q ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) =
      truncatedDiscreteOccupation S D y (fun _ => g) ⌊T * S.mε ε⌋₊ ε ω := by
  classical
  unfold quenchedDiscreteOccupation truncatedDiscreteOccupation
  rw [integral_const_mul]
  congr 1
  congr 1
  funext x
  refine Finset.sum_congr rfl fun n _ => ?_
  exact if_congr (lt_vExitTime_iff _ x n).symm rfl rfl

/-- For `T ≥ 0` and a finite exit time `τ`, the truncation level `min(T, τ)` of the rescaled LBM occupation agrees with the
one of `truncatedLBMOccupation` (which uses `τ.toReal`). -/
theorem toReal_min_ofReal_eq {T : ℝ} (hT : 0 ≤ T) {τ : ℝ≥0∞} (hτ : τ ≠ ⊤) :
    (min (ENNReal.ofReal T) τ).toReal = min T τ.toReal := by
  lift τ to ℝ≥0 using hτ
  rw [ENNReal.ofReal, ← ENNReal.coe_min, ENNReal.coe_toReal, ENNReal.coe_toReal, NNReal.coe_min,
    Real.coe_toNNReal T hT]

/-- Convergence in probability is unchanged when the limit is modified on a null set. -/
theorem tendstoInProbability_congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ → Ω → ℝ}
    {Y Y' : Ω → ℝ} (hY : Y =ᵐ[P] Y') (hX : TendstoInProbability P X Y) : TendstoInProbability P X Y' := by
  intro δ hδ
  refine Tendsto.congr' (Eventually.of_forall fun ε => ?_) (hX δ hδ)
  dsimp only
  apply measure_congr
  filter_upwards [hY] with ω hω
  simp only [hω]

/-- The deterministic fixed-time input `TruncatedDetFixedTimeStep` of the lifting lemma, obtained from the quenched inputs:
the quenched expectation of the discrete occupation is the truncated discrete occupation, and the LBM occupation is
`truncatedLBMOccupation` almost surely (the exit time is finite `PB`-a.e., by `FrozenLBMGreenOccupationRescaled`). -/
theorem truncatedDetFixedTimeStep_of_quenched {𝒮 : SpaceFillingSLEModel}
    (hrev : FrozenLBMGreenOccupationRescaled 𝒮) (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮) :
    TruncatedDetFixedTimeStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hball hy g hgc hgb hgh T hT
  have hq := hdet γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy g hgc hgb hgh T hT
  have hae := hrev γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy
  have hY : (fun ω => ∫ b, rescaledLBMOccupation S ω (ball z r) (ENNReal.ofReal T) g b
      ∂planarBrownianMotion y) =ᵐ[S.P]
      (fun ω => truncatedLBMOccupation S (ball z r) y (fun _ => g) T ω) := by
    filter_upwards [hae] with ω hω
    unfold truncatedLBMOccupation
    apply integral_congr_ae
    filter_upwards [hω.1] with b hb
    unfold rescaledLBMOccupation
    rw [toReal_min_ofReal_eq hT.le hb.ne]
  simp only [quenched_integral_eq_truncatedDiscrete] at hq
  exact tendstoInProbability_congr_ae hY hq

/-- **Lemma 3.4** (lemma:integral-convergence-of-greens-function), corrected [C1, C16], on the quenched route:
`IntegralConvergenceGreenFunctionStmt 𝒮`. Hypotheses: Lemma 2.7 (`VolumeGrowthStmt`), Lemma 2.18 (`ExitTimeUpperBoundStmt`),
`MepsScalingInput` (External), and the two FIRST-PASS FROZEN quenched inputs `FrozenLBMGreenOccupationRescaled` and
`FrozenTruncatedQuenchedLawsFixedTime`.

Route: the quenched proof, steps 1-10,
each realised by a declaration already proved in `MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/`:
* step 1 (parameters, normalisation `c₀ = 2/m₀`, `MepsScalingInput` = eq:meps-scaling, the lower bound of (2.20)): `MatedCRTEnv.c₀`
  (Defs/Setting.lean:188), `MepsScalingInput` (External/SLE.lean:63);
* steps 2-3 (extension of the random test function, countable approximation, fixed-time convergence for env-measurable `f`):
  `truncatedOccupationFixedTimeStep_of_det` (FixedTimeReduction.lean:163), fed by `truncatedDetFixedTimeStep_of_quenched` (this file);
* step 4 (`P[μ(D) < ε^α] → 0`, finite measurable potential): `MatedCRTEnv.IsValid.exists_ball_mass_lower_bound`
  (AreaParametrizedMass.lean:34, small-mass probability bound), `boundedExitTimeRV_of_steps` (Steps/Sec2/BoundedExitTimeRV.lean:26);
* step 5 (quenched uniform integrability from Lemma 2.18 with N = 2): `scaled_secondMoment_bounded_in_probability`
  (PotentialTightness.lean:65);
* step 6 (Green sum = expected occupation, Fubini under integrable visit counts): `sum_greenFn_mul_eq_integral_occupation`
  (OccupationGreen.lean:96);
* steps 7 and 10 (removal of the discrete cutoff; assembly in probability): `discrete_green_occupation_tail_in_probability`
  (DiscreteTailProbability.lean:126), `integralConvergenceGreenFunction_of_fixed_and_ae_continuum` (ContinuumTailAssembly.lean:31);
* step 8 (removal of the continuum cutoff, dominated convergence in `b`): `truncatedLBMOccupation_tendsto_of_integrable_exit`
  (ContinuumOccupation.lean:100);
* step 9 (identification of the limit with the Green integral): the identity clause of `FrozenLBMGreenOccupationRescaled`.

Section 11 obligations of the write-up, against the Lean definitions (the proof is closed: `#print axioms` is transitive):
* 11.1: `c₀ = 2/m₀` is definitional (Defs/Setting.lean:188); the lower scaling `c ε⁻¹ ≤ m_ε` is `MepsScalingInput`
  (External/SLE.lean:63), which gives `C⁻¹ ε⁻¹ ≤ m_ε` for small `ε`.
* 11.2: `IsHolderContinuousOn` is global with exponent in `(0,1]` (Defs/Notation.lean:103). The Lean inclusion is
  `envSigma ≤` the NULL-MEASURABLE σ-algebra (Proofs/Measurability/EnvSigmaCore.lean:11), not the ambient one of the write-up; it
  suffices through `IsValid.aemeasurable_of_envSigma` (EnvSigmaCore.lean:37), used by GreenIntegralMeasurable.lean:147 and
  TestFunctionTightness.lean:62.
* 11.3: `MatedCRTEnv` (Defs/Setting.lean:105) has no path-realisation field. The functional form is `exists_truncated_joint`
  (Proofs/Sec3/IntegralConvergenceGreenFunction/TruncatedJointAE.lean:27): a jointly measurable version, a.e. equal to the
  truncated path integrals. The write-up's `Xbar` for the path itself is not needed, since `rescaledLBMPath` is defined directly.
* 11.4: the walk law `srwLaw` (Defs/RandomWalk.lean:72) needs no kernel interface. Cell facts: `vertexPoint ∈ cell`
  (Proofs/Sec6/ConstantOrderLowerBoundDiv/Geometry.lean:106); `k ∈ interiorCellVertices ε η (ball z r)` gives
  `vertexPoint ε η k ∈ ball z r` (Sec3/IntegralConvergenceGreenFunction/OccupationTail.lean:12), write-up step 2 (5).
* 11.5: `greenFn` is `(∫⁻ visits).toReal` (Defs/RandomWalk.lean:95), the write-up's formula; the exit moments are ENNReal
  lintegrals (`exitTimeMoment`, RandomWalk.lean:108; `ExitTimeUpperBoundStmt`, Draft/Section2.lean:239), so no `toReal` encoding. -/
theorem firstPass_3_4 {𝒮 : SpaceFillingSLEModel} (h27 : VolumeGrowthStmt) (h18 : ExitTimeUpperBoundStmt 𝒮)
    (hscale : MepsScalingInput 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮) :
    IntegralConvergenceGreenFunctionStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z y hr hball hy f hfmeas hfbound hfcont
  have hfixed := truncatedOccupationFixedTimeStep_of_det hscale (truncatedDetFixedTimeStep_of_quenched hrevuz hdet)
    (truncatedFixedTimeIntegrableStep_holds 𝒮) γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy f hfmeas hfbound hfcont
  obtain ⟨hmeas, hVm⟩ := lbmTruncatedOccupationMeasurableStep_holds 𝒮 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy f
    hfmeas hfbound hfcont
  have hUm := lbmGreenIntegralMeasurableStep_holds 𝒮 γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy f hfmeas hfbound hfcont
  have hexit : ∀ᵐ ω ∂S.P, Integrable (fun b =>
      (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal) (planarBrownianMotion y) := by
    filter_upwards [hrevuz γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy] with ω hω
    exact hω.2.1
  have hmin : ∀ τ : ℝ≥0∞, min ⊤ τ = τ := fun τ => min_eq_right le_top
  have hid : ∀ᵐ ω ∂S.P, (∫ b, (∫ t in Ioc (0 : ℝ)
      (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal,
        f ω (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)) ∂planarBrownianMotion y) =
      S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂S.μ ω := by
    filter_upwards [hrevuz γ hγ hγ2 ρ hρ hρ1 Ω S hS r z y hr hball hy] with ω hω
    have h := hω.2.2 (f ω) (hfbound ω) (hfcont ω)
    simp only [rescaledLBMOccupation, hmin] at h
    unfold MatedCRTEnv.c₀
    exact h
  have hV : ∀ᵐ ω ∂S.P, Tendsto (fun n : ℕ => truncatedLBMOccupation S (ball z r) y f n ω) atTop
      (𝓝 (S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂S.μ ω)) := by
    filter_upwards [hexit, hmeas, hid] with ω hωexit hωmeas hωid
    obtain ⟨M, hM⟩ := hfbound ω
    rw [← hωid]
    exact truncatedLBMOccupation_tendsto_of_integrable_exit S (ball z r) y f ω (max M 0)
      (le_max_right _ _) (fun x hx => (hM x hx).trans (le_max_left _ _)) hωmeas hωexit
  exact integralConvergenceGreenFunction_of_fixed_and_ae_continuum (boundedExitTimeRV_of_steps h27) h18 hscale hγ hγ2
    hρ hρ1 S hS hr hball hy f hfmeas hfbound hfcont hfixed hVm hUm hV

#print axioms firstPass_3_4

end MatedCRT.S3S4c
