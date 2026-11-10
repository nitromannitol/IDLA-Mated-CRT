import MatedCRT.FirstPass.S2b
import MatedCRT.FirstPass.S5j
import MatedCRT.Proofs.Sec1.EnvironmentScaling.IGCurveScaling

/-!
# The pole cell of Proposition 5.1 (fp-S5m, z8)

`StoppedPoleCellStep` (FirstPass/S5f/Steps.lean:39) asks that, for all small mesh sizes, almost surely the vertex of the
pole `0` is the vertex `0`: `a^ε_0 = 0`. This file proves it from the mating-of-trees coupling of the environment
(`S.IsValid`, Defs/Setting.lean), and assembles Proposition 5.1 with it.

Written source: `notes/fp-gaps/CHATGPT-z5-floor.md`, Step 3.2 (lines 132-154), with the cell computation of
`notes/fp-gaps/CHATGPT-li-pole-cell.md` §9. The clauses it uses are fields of the bundle `IsMatingOfTreesCoupling`
(`.lake/packages/lattice-probability/LatticeProb/Bonanno/MatedCRTHarmonic/Frozen/IsMatingOfTreesCoupling.lean`), reached
through `S.IsValid.matingOfTrees`:
* `igMap` (line 84): the affine covariance of the IG witness `Φ` at the identity map; with `spaceFilling` it gives
  `firstHit (ηL ω) 0 = 0` a.s. This is the lemma `igMap_witness_period` (Proofs/Sec1/EnvironmentScaling/IGCurveScaling.lean).
* `spaceFilling` (line 105): `ηL ω 0 = 0` and transience `Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ)` a.s.
* `areaParam` (line 111): `η ω = ηL ω ∘ φ` for an order isomorphism `φ : ℝ ≃o ℝ` with `φ 0 = 0` a.s.

Route. Transience makes the zero set `{t | ηL ω t = 0}` bounded below, so `firstHit (ηL ω) 0 = sInf` of it is attained:
`firstHit = 0` forbids zeros of `ηL ω` at negative times. Pulling back by `φ` (order iso fixing 0), `η ω` has no zero at
negative times. Hence the set `{k : ℤ | 0 ∈ cell ε (η ω) k}` contains `0` (`η ω 0 = 0`) and no negative integer
(the cell of index `k ≤ -1` is `η ω` on `[ε(k-1), εk] ⊂ (-∞,0)`), so its infimum is `0`.

Terminology: whole-plane space-filling SLE and its transience (Sheffield, Miller-Sheffield), imaginary geometry (Miller-Sheffield),
mating of trees (Duplantier-Sheffield-Miller), the cell of a vertex (the paper's Definition 1.2).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRT

/-- **Pole vertex (NEW, fp-S5m).** Almost surely, for every mesh size `ε > 0`, the smallest vertex whose cell contains the
pole `0` is the vertex `0`: `a^ε_0 = 0`. Proof: `firstHit (ηL ω) 0 = 0` (`igMap_witness_period`), transience and
`ηL ω 0 = 0` (`spaceFilling`), and the order isomorphism `φ` fixing `0` (`areaParam`). -/
theorem vertexOf_zero_ae (𝒮 : SpaceFillingSLEModel) {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    (hS : S.IsValid 𝒮 γ) : ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → vertexOf ε (S.η ω) 0 = 0 := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  obtain ⟨-, -, -, -, hfh, -⟩ := Sec1.igMap_witness_period hC
  filter_upwards [hC.spaceFilling, hC.areaParam, htie, hfh] with ω hsf hap hω hf
  obtain ⟨hsurj, hT, h0, -⟩ := hsf
  obtain ⟨⟨φ, hφ0, hφ⟩, -⟩ := hap
  -- the curve `S.η ω` is `ηL ω ∘ φ`
  have hη : ∀ t, S.η ω t = ηL ω (φ t) := fun t => by
    rw [← hω.1]
    exact hφ t
  have hzero0 : S.η ω 0 = 0 := by
    rw [hη 0, hφ0, h0]
  -- the zero set of `ηL ω` is bounded below (transience): it lies in a compact set
  have hbdd : BddBelow {t : ℝ | ηL ω t = 0} := by
    have hset : ({0} : Set ℂ)ᶜ ∈ cocompact ℂ := mem_cocompact.2 ⟨{0}, isCompact_singleton, subset_rfl⟩
    obtain ⟨K, hK, hKsub⟩ := mem_cocompact.1 (hT hset)
    refine hK.bddBelow.mono ?_
    intro t ht
    by_contra htK
    have : ηL ω t ∈ ({0} : Set ℂ)ᶜ := hKsub htK
    exact this ht
  -- no zero of `ηL ω` at negative times: `firstHit = 0` is the least zero
  have hneg_L : ∀ t : ℝ, t < 0 → ηL ω t ≠ 0 := by
    intro t ht hz
    have hle : sInf {s : ℝ | ηL ω s = 0} ≤ t := csInf_le hbdd (show t ∈ {s : ℝ | ηL ω s = 0} from hz)
    have hf' : sInf {s : ℝ | ηL ω s = 0} = 0 := hf
    linarith
  -- no zero of `S.η ω` at negative times (pull back by `φ`, an order isomorphism fixing `0`)
  have hneg : ∀ s : ℝ, s < 0 → S.η ω s ≠ 0 := by
    intro s hs hz
    rw [hη s] at hz
    have hφs : φ s < 0 := by
      have := φ.lt_iff_lt.2 hs
      rwa [hφ0] at this
    exact hneg_L (φ s) hφs hz
  intro ε hε
  unfold vertexOf
  have hlist : IsLeast {k : ℤ | (0 : ℂ) ∈ cell ε (S.η ω) k} 0 := by
    refine ⟨?_, ?_⟩
    · show (0 : ℂ) ∈ cell ε (S.η ω) 0
      refine ⟨0, ⟨?_, ?_⟩, hzero0⟩
      · push_cast
        nlinarith
      · push_cast
        nlinarith
    · intro k hk
      by_contra hlt
      have hk1 : k ≤ -1 := by omega
      obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := hk
      have hk1' : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
      have hεk : ε * (k : ℝ) ≤ ε * (-1) := mul_le_mul_of_nonneg_left hk1' hε.le
      exact hneg s (by linarith) hs
  exact hlist.csInf_eq

/-- **Step (2), the pole cell (fp-S5m).** `StoppedPoleCellStep 𝒮` holds: it is `vertexOf_zero_ae` for every mesh size. -/
theorem stoppedPoleCell_proved (𝒮 : SpaceFillingSLEModel) : StoppedPoleCellStep 𝒮 := by
  intro γ _ _ ρ _ _ Ω _ S hS
  have hae := vertexOf_zero_ae 𝒮 hS
  exact eventually_nhdsWithin_of_forall fun ε hε => hae.mono fun ω hω => hω ε hε

/-- **Proposition 5.1 (fp-S5m).** `firstPass_5_1_of_floorCell_pole` with the pole input discharged by
`stoppedPoleCell_proved`; the remaining hypotheses are those of `firstPass_5_1_of_floorCell_pole` (S5j.lean) minus `hpole`. -/
theorem firstPass_5_1_of_floorCell (𝒮 : SpaceFillingSLEModel)
    (h27 : VolumeGrowthStmt) (h28 : CellSizeEstimateStmt 𝒮)
    (hcan : ConeCanonicalHalfBallStep) (hcl : ConeHalfBallClosureInsideStep) (hE1 : ConeCircleLawUniqueStep)
    (hE2 : ConeReferenceExistsStep) (hscale : QuantumConeScalingInput) (h22 : LQGMeasurePropertiesStmt)
    (h24c : ConeHarmonicBallsUpToFixedTimeCorrectedStmt) (h218 : ExitTimeUpperBoundStmt 𝒮)
    (hfc : StoppedFloorCellStep 𝒮) (hU : FrozenUniversalMeasurabilityOfAnalytic)
    (hm : MepsScalingInput 𝒮) (h210 : DegreeMeasureConvergenceStmt 𝒮) (h214 : GreenKernelUpperBoundStmt 𝒮)
    (h211 : RandomWalkToLBMStmt 𝒮) (hrevuz : FrozenLBMGreenOccupationRescaled 𝒮)
    (hdet : FrozenTruncatedQuenchedLawsFixedTime 𝒮)
    (hexc : FrozenBrownianOutwardExcursionAtExit) (h35 : DiscreteDirichletProblemStmt 𝒮)
    (hH : FrozenDiscreteHolderContinuityCorrected 𝒮) (hcone : FrozenConeScalingLaw 𝒮)
    (hG : FrozenGreenDiscPole) (hG15 : GreenFunctionCrudeBoundStmt 𝒮) (hG16 : GreenKernelLowerBoundStmt 𝒮) :
    IDLALowerBoundStmt 𝒮 :=
  firstPass_5_1_of_floorCell_pole 𝒮 h27 h28 hcan hcl hE1 hE2 hscale h22 h24c h218 hfc (stoppedPoleCell_proved 𝒮) hU
    hm h210 h214 h211 hrevuz hdet hexc h35 hH hcone hG hG15 hG16

end MatedCRT
