import MatedCRT.Steps.Sec4.ObstacleSpecialization
import MatedCRT.External.SLE

/-!
# Section 4: proof of `MatedObstacleSettingStep` and Lemmas 4.3-4.5 from the inputs

* `cellVertices_finite_of_isBounded`: for a continuous proper curve, finitely many cells meet a bounded set; hence
  `V^ε(B_ρ) \ V^ε(∂B_ρ)` is finite and `𝒢^ε` is locally finite.
* `matedObstacleSettingStep_of`: `MatedObstacleSettingStep` from `EtaProperStep`, `ConsecutiveCellsAdjacentStep`,
  `GreenKernelLaplacianStep` and the connectivity of `V^ε(B_ρ) \ V^ε(∂B_ρ)` required by the field
  `IsObstacleSetting.connected` (ESCALATIONS E-c1-2: this connectivity can fail; the hypothesis disappears once the
  field is weakened).
-/

namespace MatedCRT

open MeasureTheory Set Metric Filter Topology

section Deterministic

variable {ε : ℝ} {η : ℝ → ℂ} {ρ : ℝ}

/-- For a continuous curve with `η(s) → ∞` as `|s| → ∞`, finitely many cells meet a bounded set. -/
theorem cellVertices_finite_of_isBounded (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {K : Set ℂ} (hK : Bornology.IsBounded K) : (cellVertices ε η K).Finite := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  have hc : IsCompact (η ⁻¹' closedBall 0 R) :=
    (isProperMap_iff_tendsto_cocompact.2 ⟨hη, hp⟩).isCompact_preimage (isCompact_closedBall 0 R)
  obtain ⟨T, hT⟩ := hc.isBounded.subset_closedBall 0
  refine (Set.finite_Icc (-⌈T / ε + 1⌉) ⌈T / ε + 1⌉).subset ?_
  intro k hk
  obtain ⟨z, ⟨s, hs, rfl⟩, hzK⟩ : ∃ z, z ∈ η '' Icc (ε * (k - 1)) (ε * k) ∧ z ∈ K := hk
  have hsT : |s| ≤ T := by simpa [Real.dist_eq] using hT (hR hzK)
  have h1 : ε * (k - 1) ≤ T := hs.1.trans ((le_abs_self s).trans hsT)
  have h2 : -T ≤ ε * k := ((neg_le_neg hsT).trans (neg_abs_le s)).trans hs.2
  have hk1 : (k : ℝ) ≤ T / ε + 1 := by
    have : (k : ℝ) - 1 ≤ T / ε := (le_div_iff₀ hε).2 (by rw [mul_comm]; exact h1)
    linarith
  have hk2 : -(T / ε + 1) ≤ (k : ℝ) := by
    have h3 : -T / ε ≤ (k : ℝ) := (div_le_iff₀ hε).2 (by rw [mul_comm]; exact h2)
    rw [neg_div] at h3
    linarith
  have hc1 := Int.le_ceil (T / ε + 1)
  constructor
  · have : ((-⌈T / ε + 1⌉ : ℤ) : ℝ) ≤ k := by push_cast; linarith
    exact_mod_cast this
  · exact_mod_cast hk1.trans hc1

/-- `𝒢^ε` is locally finite (continuous proper curve). -/
theorem cellMult_locallyFinite (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (a : ℤ) : {b | cellMult ε η a b ≠ 0}.Finite := by
  have hK : Bornology.IsBounded (cell ε η a) := (isCompact_Icc.image hη).isBounded
  refine (cellVertices_finite_of_isBounded hη hp hε hK).subset fun b hb => ?_
  obtain ⟨z, hza, hzb⟩ := cell_inter_nonempty_of_cellMult_ne_zero hb
  exact ⟨z, hzb, hza⟩

/-- A map `m` whose adjacent vertices have intersecting cells is locally finite (continuous proper curve). For the map
of Definition 1.1 the hypothesis is `AdjacentCellsMeetAeStep` (MatedCRT/Steps/Infra/MatingOfTrees.lean). -/
theorem locallyFinite_of_cells_meet {m : ℤ → ℤ → ℕ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hcell : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) (a : ℤ) : {b | m a b ≠ 0}.Finite := by
  have hK : Bornology.IsBounded (cell ε η a) := (isCompact_Icc.image hη).isBounded
  refine (cellVertices_finite_of_isBounded hη hp hε hK).subset fun b hb => ?_
  obtain ⟨z, hza, hzb⟩ := hcell a b hb
  exact ⟨z, hzb, hza⟩

/-- `V^ε(B_ρ) \ V^ε(∂B_ρ)` is finite (continuous proper curve). -/
theorem ballInterior_finite (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε) :
    (ballInterior ε η ρ).Finite :=
  (cellVertices_finite_of_isBounded hη hp hε isBounded_ball).subset ballInterior_subset_cellVertices_ball

end Deterministic

/-- `MatedObstacleSettingStep` from the inputs, given the connectivity `BallInteriorConnectedStep` required by
`IsObstacleSetting.connected` (ESCALATIONS E-c1-2). -/
theorem matedObstacleSettingStep_of {𝒮 : SpaceFillingSLEModel} (hp : EtaProperStep 𝒮)
    (hcons : ConsecutiveCellsAdjacentStep 𝒮) (hG : GreenKernelLaplacianStep) (hconn : BallInteriorConnectedStep 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) : MatedObstacleSettingStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS
  filter_upwards [hp γ hγ hγ2 Ω S hS, hcons γ hγ hγ2 Ω S hS, hS.isAreaParametrized,
    hconn γ hγ hγ2 ρ hρ hρ1 Ω S hS, hcell γ hγ hγ2 Ω S hS] with ω hpω hc hη hcω hmeet
  intro t ε ht hε h0
  have hlf := locallyFinite_of_cells_meet hη.1 hpω hε (hmeet ε hε)
  have hfin : (ballInterior ε (S.η ω) ρ).Finite := ballInterior_finite hη.1 hpω hε
  exact matedObstacle_isObstacleSetting ht hε (S.mult_symm ε ω) (S.mult_self ε ω) hlf hfin (hc ε hε) (hcω ε hε h0) h0
    (hG _ _ (S.mult_symm ε ω) hlf (hc ε hε) hfin 0 h0)

/-- `EtaProperStep` holds: under the mating-of-trees coupling of `MatedCRTEnv.IsValid`, a.s. `η(t) → ∞` as `|t| → ∞`
(`MatedCRTEnv.IsValid.ae_tendsto_cocompact`). -/
theorem etaProperStep_holds (𝒮 : SpaceFillingSLEModel) : EtaProperStep 𝒮 :=
  fun _ _ _ _ _ _ hS => hS.ae_tendsto_cocompact

/-- `ConsecutiveCellsAdjacentStep` holds: consecutive vertices are adjacent in the map of Definition 1.1, for every `ω`
(`MatedCRTEnv.mult_succ_ne_zero`; it replaces the former input `SpaceFillingSLEPathInput`). -/
theorem consecutiveCellsAdjacentStep_holds (𝒮 : SpaceFillingSLEModel) : ConsecutiveCellsAdjacentStep 𝒮 :=
  fun _ _ _ _ _ S _ => Filter.Eventually.of_forall fun ω _ hε k => S.mult_succ_ne_zero hε.le ω k

/-- **Lemma 4.3** (lemma:discrete-basic-properties, line 1679) from the steps `GreenKernelLaplacianStep`,
`NormExitTimeLaplacianStep` (deterministic), `BallInteriorConnectedStep` (E-c1-2) and `AdjacentCellsMeetAeStep`
(consequence of the mating-of-trees coupling, MatedCRT/Steps/Infra/MatingOfTrees.lean). -/
theorem discreteBasicProperties_of_inputs {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLaplacianStep) (hq : NormExitTimeLaplacianStep) (hconn : BallInteriorConnectedStep 𝒮)
    (hcell : AdjacentCellsMeetAeStep 𝒮) : DiscreteBasicPropertiesStmt 𝒮 :=
  discreteBasicProperties_of_steps
    (matedObstacleSettingStep_of (etaProperStep_holds 𝒮) (consecutiveCellsAdjacentStep_holds 𝒮) hG hconn hcell)
    (consecutiveCellsAdjacentStep_holds 𝒮) hq hcell

/-- **Lemma 4.4**, corrected (E-c1-1), from the steps. -/
theorem discreteLaplacianBoundCorrected_of_inputs {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLaplacianStep) (hconn : BallInteriorConnectedStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮) :
    DiscreteLaplacianBoundCorrectedStmt 𝒮 :=
  discreteLaplacianBoundCorrected_of_steps
    (matedObstacleSettingStep_of (etaProperStep_holds 𝒮) (consecutiveCellsAdjacentStep_holds 𝒮) hG hconn hcell) hcell

/-- **Lemma 4.5**, corrected (E-c1-1), from the steps. -/
theorem discreteConservationOfMassCorrected_of_inputs {𝒮 : SpaceFillingSLEModel}
    (hG : GreenKernelLaplacianStep) (hconn : BallInteriorConnectedStep 𝒮) (hcell : AdjacentCellsMeetAeStep 𝒮) :
    DiscreteConservationOfMassCorrectedStmt 𝒮 :=
  discreteConservationOfMassCorrected_of_steps
    (matedObstacleSettingStep_of (etaProperStep_holds 𝒮) (consecutiveCellsAdjacentStep_holds 𝒮) hG hconn hcell) hcell

end MatedCRT
