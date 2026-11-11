import MatedCRT.FirstPass.S5S6S7
import MatedCRT.Proofs.Sec7.OdometerBoundMass.Corrected
import MatedCRT.Steps.Sec7.CrudeUpperBound

/-!
# Lemma 7.4 in the positive-support form, with one event in `t`

Audit item 4 of the minimal correction list (section "The neighboring Lemma 7.4"): the printed Lemma 7.4 starts at `a ∈ D_ε(t/ε) \ {0}`, the unstopped sandpile cluster, while
the stopped odometer `u^ε_t` vanishes at far points of that cluster. The correct starting set and path set are the
positive stopped support `Λ^ε_t = {u^ε_t > 0}`, which is `matedDiscreteCluster` (MatedCRT/Defs/Sandpile.lean:87).
The audit also requires `∀ t > 0` inside the `PolyHighProb` event, since the degree-bound event does not depend on `t`.

`CrudeUpperBoundStmt` (MatedCRT/Draft/Section7.lean) already uses `Λ^ε_t` as start and path set, but quantifies
`∀ t > 0` outside `PolyHighProb`. `CrudeUpperBoundSupportStmt` below is the audit's interface. Its proof is that of
`crudeUpperBound_of_mapSteps` (MatedCRT/Steps/Sec7/CrudeUpperBound.lean) with `t` moved inside: the almost sure inputs
`MatedMapStructureStep` and `StoppedOdometerLaplacianStep` hold for all `ε` and all `t`, and the degree bound is an
event independent of `t`. The fixed-`t` interface is recovered by `crudeUpperBound_of_support`, the form that
`divSandpileUpperBound_of_meshScaling` consumes.

No Draft statement is edited, and no Prop is frozen.
-/

namespace MatedCRT

open MeasureTheory Set Metric

/-- **Lemma 7.4, positive-support form** (lemma:crude-upper-bound, line 3058; Levine-Peres 2009, Lemma 4.2; audit item 4). For all `t > 0` simultaneously, with polynomially high probability as `ε → 0`: for every
`a ∈ Λ^ε_t \ {0}`, where `Λ^ε_t = {u^ε_t > 0}` is the positive stopped support (`matedDiscreteCluster`), there is a
path `a = a₀ ∼ a₁ ∼ ⋯ ∼ a_m = 0` in `Λ^ε_t` with `u^ε_t(a_{i+1}) ≥ u^ε_t(a_i) + log(ε⁻¹)⁻²`. -/
def CrudeUpperBoundSupportStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  _root_.HarmonicBalls.PolyHighProb S.P fun ε => {ω | ∀ t : ℝ, 0 < t → ∀ a ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t \ {0},
    ∃ p : List ℤ, IsVPathIn (S.mult ε ω) (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t) p a 0 ∧
    p.IsChain fun c d => stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c + (Real.log ε⁻¹)⁻¹ ^ 2 ≤
      stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t d}

/-- **Lemma 7.4, positive-support form**, from the map structure, the stopped-odometer Laplacian step and the degree
bound. All three inputs hold on one almost sure event (for every `ε` and `t`), so the conclusion is simultaneous in `t`. -/
theorem crudeUpperBoundSupport_of_mapSteps (𝒮 : SpaceFillingSLEModel) (hstr : MatedMapStructureStep 𝒮)
    (hlap : StoppedOdometerLaplacianStep 𝒮) (hdeg : DegreeBoundInput 𝒮) : CrudeUpperBoundSupportStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  refine polyHighProb_mono_ae (hdeg γ hγ hγ2 ρ hρ hρ1 Ω S hS)
    ((hstr γ hγ hγ2 Ω S hS).and (hlap γ hγ hγ2 ρ hρ hρ1 Ω S hS)) ?_
  rintro ε hε ω hωdeg ⟨hωstr, hωlap⟩
  have hωdeg' : ∀ a ∈ cellVertices ε (S.η ω) (ball 0 ρ),
      ((mdeg (S.mult ε ω) a : ℕ) : ℝ) ≤ Real.log ε⁻¹ ^ 2 := hωdeg
  obtain ⟨hlf, hfin⟩ := hωstr ε hε
  have hsucc : ∀ k : ℤ, S.mult ε ω k (k + 1) ≠ 0 := fun k =>
    Sec7.bmEdgeCount_succ_ne_zero hε (S.bm ω).continuous.fst _ k
  have hD : ∀ c, (0 : ℝ) < (mdeg (S.mult ε ω) c : ℕ) := fun c => by
    exact_mod_cast Nat.pos_of_ne_zero (mdeg_ne_zero_of_ne_zero hlf (hsucc c))
  rw [mem_ofPred_eq]
  intro t ht
  have hΛfin : (matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t).Finite :=
    (hfin ρ).subset fun a ha => Sec7.cellVertices_mono ball_subset_closedBall
      (show a ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧ _ from ha).1
  have hstep : ∀ c ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t, c ≠ 0 →
      ∃ b ∈ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
      S.mult ε ω c b ≠ 0 ∧
        stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t c + (Real.log ε⁻¹)⁻¹ ^ 2 ≤
          stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b := by
    intro c hc hc0
    have hcV : c ∈ cellVertices ε (S.η ω) (ball 0 ρ) :=
      (show c ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧ _ from hc).1
    have hL : mLaplacian (S.mult ε ω) (stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t) c =
        ((mdeg (S.mult ε ω) c : ℕ) : ℝ)⁻¹ := hωlap ε t hε ht c hc hc0
    obtain ⟨b, hmb, hub⟩ := exists_nbr_add_inv_le hlf (hsucc c) hL
    have hδle : (Real.log ε⁻¹)⁻¹ ^ 2 ≤ ((mdeg (S.mult ε ω) c : ℕ) : ℝ)⁻¹ := by
      rw [inv_pow]
      exact inv_anti₀ (hD c) (hωdeg' c hcV)
    have hbpos : 0 < stoppedOdometer (S.mult ε ω) ε (S.η ω) ρ t b := by
      have h0 := Sec7.stoppedOdometer_nonneg (m := S.mult ε ω) (η := S.η ω) (ρ := ρ) hε ht c
      have h1 := inv_pos.2 (hD c)
      linarith
    exact ⟨b, Sec7.mem_matedDiscreteCluster_of_stoppedOdometer_pos hε ht hbpos, hmb, by linarith⟩
  rintro a ⟨haΛ, ha0⟩
  have haV : a ∈ cellVertices ε (S.η ω) (ball 0 ρ) :=
    (show a ∈ cellVertices ε (S.η ω) (ball 0 ρ) ∧ _ from haΛ).1
  have hδ : 0 < (Real.log ε⁻¹)⁻¹ ^ 2 := by
    rw [inv_pow]
    exact inv_pos.2 ((hD a).trans_le (hωdeg' a haV))
  exact exists_vPath_chain hΛfin hδ hstep a haΛ

/-- **Lemma 7.4, positive-support form**, from the corrected Lemma 4.4 (`DiscreteLaplacianBoundCorrectedStmt`), the
degree bound (GMS19 Lemma 2.6, `DegreeBoundInput`) and `AdjacentCellsMeetAeStep`. -/
theorem crudeUpperBoundSupport_of_corrected (𝒮 : SpaceFillingSLEModel) (h44 : DiscreteLaplacianBoundCorrectedStmt 𝒮)
    (hdeg : DegreeBoundInput 𝒮) : CrudeUpperBoundSupportStmt 𝒮 :=
  crudeUpperBoundSupport_of_mapSteps 𝒮 (matedMapStructureStep_of_adjacentCellsMeet 𝒮 (adjacentCellsMeetAeStep 𝒮))
    (stoppedOdometerLaplacianStep_of_corrected h44 (adjacentCellsMeetAeStep 𝒮)) hdeg

/-- The fixed-`t` interface `CrudeUpperBoundStmt` (Draft, Section 7) follows from the positive-support form: for each
`t`, the event of the support form is contained in the event of `CrudeUpperBoundStmt` for that `t`. -/
theorem crudeUpperBound_of_support (𝒮 : SpaceFillingSLEModel) (h : CrudeUpperBoundSupportStmt 𝒮) :
    CrudeUpperBoundStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS t ht
  exact polyHighProb_mono_ae (h γ hγ hγ2 ρ hρ hρ1 Ω S hS) (q := fun _ => True)
    (Filter.Eventually.of_forall fun _ => trivial) fun _ _ ω hω _ => hω t ht

/-- **Proposition 7.1** (`firstPass_7_1`) with Lemma 7.4 in the positive-support form `CrudeUpperBoundSupportStmt`
(the audit's interface), in place of the fixed-`t` `crudeUpperBound_of_corrected`. Same hypotheses and conclusion as
`firstPass_7_1`. -/
theorem firstPass_7_1_support (𝒮 : SpaceFillingSLEModel) (hscale : MepsScalingInput 𝒮) (hcone : ConeHarmonicBallsStmt)
    (hdeg : DegreeBoundInput 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮) (h27 : VolumeGrowthStmt)
    (h28 : CellSizeEstimateStmt 𝒮) (h29 : CountingMeasureConvergenceStmt 𝒮) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hconv : ConvergenceDivisibleStmt 𝒮) (hgreen : UniformConvergenceGreenKernelStmt 𝒮)
    (h0 : FPWholePlaneLQGExistence) (h2 : FPWholePlaneLQGCoordinateChange)
    (hV : FPWholePlaneUpperVolumeTail) (hR : FPConeMeanZeroRestriction) : DivSandpileUpperBoundStmt 𝒮 :=
  divSandpileUpperBound_of_meshScaling 𝒮 hscale hcone
    (constantOrderLowerBoundDivLog_final 𝒮 h216 h27 h28 h29 h218 h0 AnnulusHitField.coneWholePlaneWeylComparison h2 hV hR
      Field.ConeCircle.circleAverageModConstStep (LQGMeasureField.lqgMeasureFieldMeasurableStep 𝒮))
    h27 (firstPass_7_2_corrected 𝒮 h216 h28) hconv hgreen h28 (firstPass_7_3 𝒮)
    (crudeUpperBound_of_support 𝒮 (crudeUpperBoundSupport_of_corrected 𝒮 (discreteLaplacianBoundCorrected 𝒮) hdeg))

end MatedCRT
