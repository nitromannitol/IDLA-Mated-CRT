import MatedCRT.Proofs.Sec5.StoppedActualMarginCode

/-!
# The stopped margin step assembled from the actual code producers

The erosion
minimum `M̂ = m(K, f)` of the actual code, the everywhere positive choice `c_pos = M̂` where `M̂ > 0` and `1`
otherwise, and the almost-sure identity `t < T → M̂ = M` added to the good event.

Chain, using no mathematics beyond the named inputs:
* `StoppedActualMarginCode.stoppedMarginCode_of_inputs` gives `StoppedInterior.StoppedMarginCodeStep 𝒮` from the
  producers. The family `Λ` stays arbitrary with its almost-sure premise `IsConeHarmonicBallFamily`; the compact code
  equals `closure (Λ ω t)` almost surely on `{t < T}`.
* `StoppedInterior.stoppedInteriorMeasurable_of_code` (StoppedInterior.lean:210) gives
  `StoppedInterior.StoppedInteriorMeasurableStep 𝒮`.
* `StoppedInterior.stoppedSurplusInterior_of_gap` (StoppedInterior.lean:316), the repaired consumer, takes that step.
  It already contains `cpos`, `cfin` and the good event `Good` (`t < T → Mhat = cinf`), and is reused unchanged. The
  margin measurability is therefore not a premise of the assembled theorems.

Named inputs, kept at their own scope (none is proved here):
* Preston: `PrestonAnalyticUniversallyMeasurableStmt`, `PrestonAnalyticCantorStmt`, `PrestonTheorem61Stmt`
  (`MatedCRT/Proposed/PrestonAnalytic2008.lean`, lines 43, 35, 60).
* Residual producers: `CodeSectionStmt` (`ConeOriginNullMeasurableProof.lean:575`) and `FieldCircleVersionStmt`
  (`StoppedActualMarginCode.lean:44`).
* The strict obstacle gap `HarmonicBallStrictObstacleGapStep` (`Sec4/DivSandpileLowerBound/Final.lean:32`), the pole and
  geometry steps and `MepsScalingInput`, exactly as in `stoppedSurplusInterior_of_gap`.
-/

namespace MatedCRT.StoppedMarginStepAssembly

open MeasureTheory Filter Topology Set Metric

/-- The measurable positive choice `c_pos` of the margin: `M` where `M > 0`, and `1` otherwise.
It is everywhere positive, and measurable for every σ-algebra for which `M` is measurable. -/
noncomputable def cPos {Ω : Type} (M : Ω → ℝ) : Ω → ℝ :=
  fun ω => if 0 < M ω then M ω else 1

theorem cPos_pos {Ω : Type} (M : Ω → ℝ) (ω : Ω) : 0 < cPos M ω := by
  unfold cPos
  split_ifs with h
  · exact h
  · exact one_pos

theorem cPos_eq_of_pos {Ω : Type} {M : Ω → ℝ} {ω : Ω} (h : 0 < M ω) : cPos M ω = M ω := by
  simp [cPos, h]

/-- The positive choice depends only on the value of the margin at the point. -/
theorem cPos_congr {Ω : Type} {M N : Ω → ℝ} {ω : Ω} (h : M ω = N ω) : cPos M ω = cPos N ω := by
  unfold cPos
  rw [h]

theorem measurable_cPos {Ω : Type} {m : MeasurableSpace Ω} {M : Ω → ℝ} (hM : Measurable[m] M) :
    Measurable[m] (cPos M) := by
  unfold cPos
  exact Measurable.ite (measurableSet_lt measurable_const hM) hM measurable_const

/-- The raw continuum margin of the obstacle problem (the target of `StoppedInteriorMeasurableStep`): the infimum of
the continuum surplus `w̄_t + t G_{B_ρ}(0, ·)` over the random compact set `{x ∈ Λ_t : s ≤ |x|, δ ≤ dist(x, Λ_tᶜ)}`. -/
noncomputable def rawMargin {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (Λ : Ω → ℝ → Set ℂ)
    (ρ δ s t : ℝ) (ω : Ω) : ℝ :=
  ⨅ x : {x : ℂ | x ∈ Λ ω t ∧ s ≤ ‖x‖ ∧ δ ≤ infDist x (Λ ω t)ᶜ},
    (HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t (x : ℂ) + t * HarmonicBalls.greenFunction (ball 0 ρ) 0 (x : ℂ))

/-- **The measurable positive margin on the good event.** From the stopped margin code, through
`stoppedInteriorMeasurable_of_code`, there is an `S.envSigma`-measurable everywhere positive `c` with `c = c_pos(M)`
almost surely on `{t < T}`: the good-event identity `M̂ = M` passes to the positive choice. -/
theorem cPos_margin_spec (𝒮 : SpaceFillingSLEModel) (hcode : MatedCRT.StoppedInterior.StoppedMarginCodeStep 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ s t : ℝ) (hδ : 0 < δ) (hs : 0 < s) (ht : 0 < t) :
    ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → c ω = cPos (rawMargin S Λ ρ δ s t) ω := by
  obtain ⟨Mhat, hMm, hMae⟩ :=
    MatedCRT.StoppedInterior.stoppedInteriorMeasurable_of_code 𝒮 hcode γ hγ hγ2 ρ hρ hρ1 Ω S hS Λ hΛ δ s t hδ hs ht
  refine ⟨cPos Mhat, measurable_cPos hMm, cPos_pos Mhat, ?_⟩
  filter_upwards [hMae] with ω hω hT
  exact cPos_congr (hω hT)

/-- **`StoppedMarginCodeStep` from the actual code producers.** This is
`StoppedActualMarginCode.stoppedMarginCode_of_inputs`. The family `Λ` is arbitrary with its almost-sure
`IsConeHarmonicBallFamily` premise, exactly as in `StoppedMarginCodeStep` (StoppedInterior.lean:193-205). -/
theorem stoppedMarginCodeStep_of_producers (𝒮 : SpaceFillingSLEModel)
    (hP : MatedCRT.PrestonAnalyticUniversallyMeasurableStmt) (hCantor : MatedCRT.PrestonAnalyticCantorStmt)
    (hT61 : MatedCRT.PrestonTheorem61Stmt) (hCS : MatedCRT.ConeOriginNull.CodeSectionStmt 𝒮)
    (hFC : MatedCRT.StoppedActualMarginCode.FieldCircleVersionStmt 𝒮) :
    MatedCRT.StoppedInterior.StoppedMarginCodeStep 𝒮 :=
  MatedCRT.StoppedActualMarginCode.stoppedMarginCode_of_inputs 𝒮 hP hCantor hT61 hCS hFC

/-- **`StoppedInteriorMeasurableStep` from the actual code.** `stoppedInteriorMeasurable_of_code` applied to
`stoppedMarginCodeStep_of_producers`; no margin measurability is assumed. -/
theorem stoppedInteriorMeasurableStep_of_producers (𝒮 : SpaceFillingSLEModel)
    (hP : MatedCRT.PrestonAnalyticUniversallyMeasurableStmt) (hCantor : MatedCRT.PrestonAnalyticCantorStmt)
    (hT61 : MatedCRT.PrestonTheorem61Stmt) (hCS : MatedCRT.ConeOriginNull.CodeSectionStmt 𝒮)
    (hFC : MatedCRT.StoppedActualMarginCode.FieldCircleVersionStmt 𝒮) :
    MatedCRT.StoppedInterior.StoppedInteriorMeasurableStep 𝒮 :=
  MatedCRT.StoppedInterior.stoppedInteriorMeasurable_of_code 𝒮
    (stoppedMarginCodeStep_of_producers 𝒮 hP hCantor hT61 hCS hFC)

/-- **The measurable positive margin from the actual code producers.** The positive choice of the actual margin has
the measurability, positivity and good-event identification of `cPos_margin_spec`. -/
theorem cPos_margin_of_producers (𝒮 : SpaceFillingSLEModel)
    (hP : MatedCRT.PrestonAnalyticUniversallyMeasurableStmt) (hCantor : MatedCRT.PrestonAnalyticCantorStmt)
    (hT61 : MatedCRT.PrestonTheorem61Stmt) (hCS : MatedCRT.ConeOriginNull.CodeSectionStmt 𝒮)
    (hFC : MatedCRT.StoppedActualMarginCode.FieldCircleVersionStmt 𝒮)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    (Λ : Ω → ℝ → Set ℂ) (hΛ : ∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω))
    (δ s t : ℝ) (hδ : 0 < δ) (hs : 0 < s) (ht : 0 < t) :
    ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ → c ω = cPos (rawMargin S Λ ρ δ s t) ω :=
  cPos_margin_spec 𝒮 (stoppedMarginCodeStep_of_producers 𝒮 hP hCantor hT61 hCS hFC) γ hγ hγ2 ρ hρ hρ1 Ω S hS
    Λ hΛ δ s t hδ hs ht

/-- **`StoppedSurplusInteriorStep` from the actual code producers and the strict obstacle gap.** The repaired consumer
`stoppedSurplusInterior_of_gap` receives its margin measurability from the actual code. The strict gap `hgap`, the
pole and geometry steps and the mepsScaling input stay named hypotheses at their own scope. -/
theorem stoppedSurplusInteriorStep_of_producers (𝒮 : SpaceFillingSLEModel)
    (hgap : MatedCRT.HarmonicBallStrictObstacleGapStep 𝒮)
    (hpoleS : MatedCRT.StoppedInterior.StoppedSurplusPoleStep 𝒮)
    (hgeo : MatedCRT.StoppedInterior.StoppedInteriorGeometryStep 𝒮)
    (hmeps : MatedCRT.MepsScalingInput 𝒮)
    (hP : MatedCRT.PrestonAnalyticUniversallyMeasurableStmt) (hCantor : MatedCRT.PrestonAnalyticCantorStmt)
    (hT61 : MatedCRT.PrestonTheorem61Stmt) (hCS : MatedCRT.ConeOriginNull.CodeSectionStmt 𝒮)
    (hFC : MatedCRT.StoppedActualMarginCode.FieldCircleVersionStmt 𝒮) :
    MatedCRT.StoppedSurplusInteriorStep 𝒮 :=
  MatedCRT.StoppedInterior.stoppedSurplusInterior_of_gap 𝒮 hgap hpoleS hgeo
    (stoppedInteriorMeasurableStep_of_producers 𝒮 hP hCantor hT61 hCS hFC) hmeps

end MatedCRT.StoppedMarginStepAssembly
