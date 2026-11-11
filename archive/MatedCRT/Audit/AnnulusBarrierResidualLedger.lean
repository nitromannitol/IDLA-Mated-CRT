import MatedCRT.Audit.ActualAnnulusBarrierComponents
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ActualAnnulusBarrier
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.AnnulusEnvelopeProof
import MatedCRT.Proposed.GwynneMillerSheffield
import MatedCRT.Steps.Sec3.UniformCellSize

/-! # Residual ledger of the annulus barrier consumer against the pointwise envelope input

Task `z5-steps2-annulus-barrier-residual-ledger`. Audit only: this file proves no numbered result and adds no
literature input. It connects the checked one-stage barrier and survival consumer of
`MatedCRT.Audit.ActualAnnulusBarrierComponents` to the exact pointwise annulus input `AnnulusGoodEvent` used by
`AnnulusEnvelopeProof`, and records the premises that remain as the fields of `AnnulusBarrierResidualLedger`.
Sources: `notes/wpn-steps2/steps2-r3.tex`, lines 359-429 (measurable version of the annulus event) and 695-739
(factor-four strong-Markov iteration over annuli).

## Connection

* The envelope's pointwise annulus condition on its event `E ε` is `ω ∈ AnnulusGoodEvent S ρ β p ε`.
* The barrier's stage input is `AnnulusStayGood S ε ρ β p ω`. The almost-sure implication between the two is
  `MatedCRTEnv.IsValid.ae_annulus_stay_le_of_disconnection` (ActualAnnulusBarrier.lean:81). Its almost-sure inputs are
  `IsValid` fields and `ae_outward_segment_walk` (ActualAnnulusBarrier.lean:49).
* The top-region input `AnnulusTopCellSizeGood` follows from the envelope's cell condition, every cell meeting
  `ball 0 ρ` having diameter at most `ε ^ a`, once the margin satisfies `ε ^ a ≤ d`
  (`annulusTopCellSizeGood_of_ball_diam`, ActualAnnulusBarrierComponents).
* Hence on `E ε`, every ladder with margin `d ≥ ε ^ a` has quenched survival `(1 - p) ^ (n + 1)`, outside a null set,
  so the survival failure probability is at most `P (E ε)ᶜ`.

## Residual premises (the fields of `AnnulusBarrierResidualLedger`)

1. Probability-rate, cells: `UniformCellSizeUpperStep 𝒮` (Steps/Sec3/UniformCellSize.lean:14). It is open: the
   cell-diameter producer is not in the repository (predecessor residual R1).
2. Probability-rate, annuli: `GMSAnnulusDisconnectionStmt 𝒮` (Proposed/GwynneMillerSheffield.lean:26), the explicit
   literature input arXiv:1807.07511v3, Lemma 3.11, (3.35), p. 31. It gives the failure bound `C ε ^ α`.
3. Measurable version, per mesh: `AnnulusGoodMeasurableVersionStep S ρ β p` (AnnulusEnvelopeProof.lean:74), the
   argument of steps2-r3:395-426. Its pieces: the cell part is discharged by `uniform_envSigma_cellSize_of_step`
   (Proofs/Sec3/ConvergenceHarmonicFunctions/UniformCellSizeMeasurable.lean:14), given item 1; the walk-probability part
   is `measurable_srwLaw_walkDisconnectsBeforeHit`
   (Proofs/Sec3/ConvergenceHarmonicFunctions/DisconnectionKernelMeasurability.lean:325). Open: the state coding that
   makes the good set a Borel condition on a Polish state, and the universal measurability of the good set, which is
   `PrestonAnalyticUniversallyMeasurableStmt` (Proposed/PrestonAnalytic2008.lean:43), an explicit literature Prop not
   yet used on this route. Mathlib has `AnalyticSet` (MeasureTheory/Constructions/Polish/Basic.lean) but no
   universal-measurability lemma there.
4. Scale quantifiers: (a) the annulus event is one event over all `z ∈ ball 0 ρ` and all `r ∈ [ε ^ β, ρ]`, as in
   item 2; its printed uniformity is to be confirmed against Lemma 3.11 (predecessor residual R3). (b) That
   uncountable intersection over real `(z, s)` must be measurable: this is the coanalytic step of item 3. No union over
   scales is taken. (c) The stage bottom `max ℓ (20 * ε ^ a)`, with the written margin `ℓ = 100 * ε ^ a + ε ^ β`
   (`ladderMargin`, steps2-r3:656), satisfies the two inequalities of the `lower` and `separation` fields for the cell
   margin `d = ε ^ a` (`ladder_bottom_separation`), so no separation premise is needed. The bottom lies in the range
   `s ≥ ℓ` of the written annulus iteration.
5. Not a residual: `p < 1`. The envelope uses `min p₀ (1 / 2)` (`cellAnnulus_parameters_of_estimates`).

## Not claimed

No numbered result, no distance-tail estimate (steps2-r3 eq:distance-tail), no mean, and no pointwise envelope for a
numbered theorem. `annulus_barrier_ladder_failure_of_ledger` is a conditional assembly under the ledger.

## Credit

The environment `S : MatedCRTEnv Ω` is built on Leonardo Bonanno's imported modules: the mating-of-trees coupling
`LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling` (Defs/Setting.lean:7, the `matingOfTrees` field of
`IsValid`) and the graph modules `LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph` and relatives
(Defs/Map.lean:32, the definition of `S.mult`). This file uses them only through those definitions.
-/

namespace MatedCRT

open MeasureTheory Set Metric
open scoped ENNReal

/-- Almost surely, `AnnulusGoodEvent` (the pointwise envelope input) implies the one-stage stay event
`AnnulusStayGood` (the barrier stage input), at every mesh and every `p ≥ 0`. -/
theorem annulusStayGood_of_annulusGoodEvent_ae {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ β p : ℝ} (hS : S.IsValid 𝒮 γ) (hp : 0 ≤ p) :
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ω ∈ AnnulusGoodEvent S ρ β p ε → AnnulusStayGood S ε ρ β p ω := by
  filter_upwards [hS.ae_annulus_stay_le_of_disconnection] with ω hω ε hε hgood
  unfold AnnulusStayGood
  intro z V r s d v hV hs1 hs2 hsub hv hd hnear hscale hcell
  unfold AnnulusGoodEvent at hgood
  rw [Set.mem_ofPred_eq] at hgood
  exact hω ε hε z V r s d p v hd hp hnear hscale hcell (hgood V hV s hs1 hs2 hsub v hv)

/-- On the envelope event `E` at mesh `ε`, where the cell condition and the pointwise annulus condition hold almost
surely, every ladder with margin `d ≥ ε ^ a` has quenched survival `(1 - p) ^ (n + 1)` outside a null set. Hence the
survival failure probability is at most `P Eᶜ`. -/
theorem ladder_survival_fails_le_compl {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {𝒮 : SpaceFillingSLEModel} {γ ρ a β p : ℝ} (hS : S.IsValid 𝒮 γ) (hp : 0 ≤ p)
    {ε : ℝ} (hε : 0 < ε) {E : Set Ω}
    (hE : ∀ᵐ ω ∂S.P, ω ∈ E →
      (∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty → diam (cell ε (S.η ω) i) ≤ ε ^ a) ∧
        ω ∈ AnnulusGoodEvent S ρ β p ε)
    {d r : ℝ} {V z : ℂ} {n : ℕ} (hd : ε ^ a ≤ d) (L : AnnulusLadder ε β ρ d r V z n) :
    S.P {ω | ¬ LadderSurvivalBound (S.mult ε ω) ε (S.η ω) V z r d L.s n (ENNReal.ofReal (1 - p))} ≤
      S.P Eᶜ := by
  have hstay := annulusStayGood_of_annulusGoodEvent_ae (ρ := ρ) (β := β) hS hp
  have hsurv : ∀ᵐ ω ∂S.P, ω ∈ E →
      LadderSurvivalBound (S.mult ε ω) ε (S.η ω) V z r d L.s n (ENNReal.ofReal (1 - p)) := by
    filter_upwards [hE, hstay, hS.isAreaParametrized] with ω hEω hstayω hcontω hmem
    obtain ⟨hcellω, hannω⟩ := hEω hmem
    obtain ⟨hηc, -⟩ := hcontω
    have htop : AnnulusTopCellSizeGood ε (S.η ω) d V z r (L.s 0) :=
      annulusTopCellSizeGood_of_ball_diam hηc hd L.outer_sub hcellω
    exact ladder_survival_of_stay_good hε L (hstayω ε hε hannω) htop
  have hle : ∀ᵐ ω ∂S.P,
      ω ∈ {ω | ¬ LadderSurvivalBound (S.mult ε ω) ε (S.η ω) V z r d L.s n (ENNReal.ofReal (1 - p))} → ω ∈ Eᶜ :=
    hsurv.mono fun ω hω hnot hmem => hnot (hω hmem)
  exact measure_mono_ae hle

/-- The residual ledger of the annulus barrier consumer. Each field is an exact Lean premise; none is a numbered
conclusion of the paper. -/
structure AnnulusBarrierResidualLedger (𝒮 : SpaceFillingSLEModel) (γ ρ : ℝ) : Prop where
  /-- Probability-rate premise for the cell diameters: the uniform cell-diameter bound with a polynomial rate
  (residual R1, open). -/
  cellRate : UniformCellSizeUpperStep 𝒮
  /-- Probability-rate premise for the annuli: the explicit GMS input, one event uniform over `z` and `r`
  (arXiv:1807.07511v3, Lemma 3.11, (3.35), p. 31). -/
  annulusRate : GMSAnnulusDisconnectionStmt 𝒮
  /-- Measurable-version premise, chosen separately at each mesh (steps2-r3:395-426). -/
  measurableVersion : ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ β p : ℝ, AnnulusGoodMeasurableVersionStep S ρ β p

/-- Exact-type consumer. Under the three ledger premises, the envelope exponents `β, p, κ` of
`cellAnnulusEnvelope_of_estimates_of_measurable_version` give, for every valid environment and every mesh `ε < δ`,
that every ladder with margin `d ≥ ε ^ a` fails its quenched survival bound `(1 - p) ^ (n + 1)` with probability at
most `C ε ^ κ`. This is a conditional assembly, not a numbered result. -/
theorem annulus_barrier_ladder_failure_of_ledger (𝒮 : SpaceFillingSLEModel) {γ ρ a : ℝ}
    (R : AnnulusBarrierResidualLedger 𝒮 γ ρ) (hγ : 0 < γ) (hγ2 : γ < 2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (ha : 0 < a) (ha' : a < 2 / (2 + γ) ^ 2) :
    ∃ β p κ : ℝ, 0 < β ∧ 0 < p ∧ p < 1 ∧ 0 < κ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
          ∀ (d r : ℝ) (V z : ℂ) (n : ℕ) (L : AnnulusLadder ε β ρ d r V z n), ε ^ a ≤ d →
            S.P {ω | ¬ LadderSurvivalBound (S.mult ε ω) ε (S.η ω) V z r d L.s n (ENNReal.ofReal (1 - p))} ≤
              ENNReal.ofReal (C * ε ^ κ) := by
  obtain ⟨β, p, κ, hβ, hp, hp1, hκ, henv⟩ :=
    cellAnnulusEnvelope_of_estimates_of_measurable_version 𝒮 R.cellRate R.annulusRate hγ hγ2 hρ hρ1 ha ha'
      R.measurableVersion
  refine ⟨β, p, κ, hβ, hp, hp1, hκ, ?_⟩
  intro Ω _ S hS
  obtain ⟨E, _, C, δ, hC, hδ, hE⟩ := henv Ω S hS
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro ε hε hεδ d r V z n L hd
  obtain ⟨hPE, hae⟩ := hE ε hε hεδ
  exact (ladder_survival_fails_le_compl (ρ := ρ) (β := β) (p := p) hS hp.le hε hae hd L).trans hPE

/-- The written margin of the distance tail, `ℓ = 100 * ε ^ a + ε ^ β` with cell margin `d = ε ^ a`
(steps2-r3:656, eq:distance-tail). -/
noncomputable def ladderMargin (ε a β : ℝ) : ℝ := 100 * ε ^ a + ε ^ β

/-- The written bound `ℓ ≤ 101 * ε ^ b` with `b = min a β`, for `0 < ε < 1` (steps2-r3:727). -/
theorem ladderMargin_le_101_pow_min {ε a β : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ladderMargin ε a β ≤ 101 * ε ^ min a β := by
  have ha : ε ^ a ≤ ε ^ min a β := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_left a β)
  have hb : ε ^ β ≤ ε ^ min a β := Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_right a β)
  unfold ladderMargin
  linarith

/-- The bottom stage `max (ladderMargin ε a β) (20 * ε ^ a)` satisfies the `lower` and `separation` fields of
`AnnulusLadder` for the cell margin `d = ε ^ a`, so the scale choice needs no premise. The bottom lies in the written
range `s ≥ ℓ`. -/
theorem ladder_bottom_separation {ε a β : ℝ} (hε : 0 < ε) :
    ε ^ β ≤ max (ladderMargin ε a β) (20 * ε ^ a) ∧
      5 * ε ^ a < max (ladderMargin ε a β) (20 * ε ^ a) / 2 := by
  have hpos : 0 < ε ^ a := Real.rpow_pos_of_pos hε a
  have hβ : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have hℓ : ladderMargin ε a β ≤ max (ladderMargin ε a β) (20 * ε ^ a) := le_max_left _ _
  have hℓβ : ε ^ β ≤ ladderMargin ε a β := by unfold ladderMargin; linarith
  have hℓ10 : 10 * ε ^ a < ladderMargin ε a β := by unfold ladderMargin; linarith
  exact ⟨hℓβ.trans hℓ, by linarith⟩

end MatedCRT
