import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.QuantitativeGoodEvent
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.InteriorFromHolder
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.CellRadiusEvent
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.FirstPass.Frozen.S3S4

/-!
# Regularity good event and convergence from the corrected discrete Hölder estimate

Adapted copy of `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/HolderGoodEvent.lean`. The Hölder hypothesis is the corrected
form `FrozenDiscreteHolderContinuityCorrected 𝒮` (the body of `DiscreteHolderContinuityCorrectedStep 𝒮`,
`MatedCRT/Steps/Sec3/DiscretePotentialTightness.lean:71`). The printed `DiscreteHolderContinuityStmt`
(`MatedCRT/Draft/Section3.lean:71`, FALSE, docs/campaign/CORRECTED-FORMS.md row 3.2) is not used here.

The only change in the proof is the destructuring of the Hölder data. The printed form is
`∀ χ, ∃ ξ', 0 < ξ' ∧ ξ' < 1 ∧ ξ' ≤ χ ∧ ∀ C', ∃ C, ...`; the corrected form is
`∀ χ C', ... → ∃ ξ' C, 0 < ξ' ∧ ξ' < 1 ∧ 0 < C ∧ ...`. The clause `ξ' ≤ χ` was bound but never used by the printed proof, and
`CorrectedHarmonicRegularityGoodEventStep` asks only for `0 < ξ`. The constant C' is instantiated once, at `C₀ + 1`, as in the
printed proof. The dependence of ξ' on C' is covered by the same-walk argument.
-/

namespace MatedCRT

open Filter Topology Metric MeasureTheory Set Tightness _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Cell sizes, local finiteness and discrete Hölder regularity imply the
good-event estimate for projected harmonic extensions. -/
theorem correctedHarmonicRegularityGoodEvent_of_discreteHolderCorrected
    (𝒮 : SpaceFillingSLEModel) (h28 : CellSizeEstimateStmt 𝒮)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    CorrectedHarmonicRegularityGoodEventStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS r z hr hball ψ hψ e he
  obtain ⟨C₀, χ, hχ, hχ1, hret⟩ := holder_ballRetraction hr
    (show 0 ≤ r + 1 by linarith) z hψ
  obtain ⟨ξ, A, β, hξ, hξ1, hA, hβ, hβ1, hholder⟩ := h32 γ hγ hγ2 ρ hρ hρ1
  obtain ⟨ξ', C, hξ', hξ'1, hC, hreg⟩ :=
    hholder (χ : ℝ) ((C₀ : ℝ) + 1) (by exact_mod_cast hχ) (by exact_mod_cast hχ1) (by positivity)
  obtain ⟨Cψ, χψ, hχψ, hχψ1, hψholder⟩ := hψ
  obtain ⟨B, hB⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn
    (hψholder.continuousOn hχψ)
  have hψB : ∀ x ∈ closedBall z r, |ψ x| ≤ B := fun x hx => by
    simpa only [Real.norm_eq_abs] using hB x hx
  obtain ⟨a, ha, halim, hcell⟩ :=
    exists_vanishing_closedBall_cellRadius 𝒮 h28 hγ hγ2 hρ hρ1 hr hball S hS
  let E : ℝ → Set Ω := fun ε => {ω | ∀ (D : Set ℂ) (f : ℤ → ℝ),
    D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
    (∀ v ∈ interiorCellVertices ε (S.η ω) D, matedLaplacian (S.mult ε ω) f v = 0) →
    (∀ v ∈ interiorCellVertices ε (S.η ω) D, ∀ w ∈ cellVertices ε (S.η ω) D,
      |f v - f w| * infDist (vertexPoint ε (S.η ω) v) (frontier D) ^ ξ ≤
        A * (⨆ v' : cellVertices ε (S.η ω) D, |f v'|) *
          max (ε ^ β) ‖vertexPoint ε (S.η ω) v - vertexPoint ε (S.η ω) w‖ ^ ξ) ∧
    ((SimplyConnectedSpace D ∧ ∀ v ∈ cellVertices ε (S.η ω) (frontier D),
      ∀ w ∈ cellVertices ε (S.η ω) (frontier D),
        |f v - f w| ≤ ((C₀ : ℝ) + 1) *
          max ε ‖vertexPoint ε (S.η ω) v - vertexPoint ε (S.η ω) w‖ ^ (χ : ℝ)) →
    ∀ v ∈ cellVertices ε (S.η ω) D, ∀ w ∈ cellVertices ε (S.η ω) D,
      |f v - f w| ≤ max C (A * ⨆ v' : cellVertices ε (S.η ω) D, |f v'|) *
        max ε ‖vertexPoint ε (S.η ω) v - vertexPoint ε (S.η ω) w‖ ^ ξ')}
  let F : ℝ → Set Ω := fun ε => {ω | ∀ v ∈ cellVertices ε (S.η ω) (closedBall z r),
    ∀ p ∈ cell ε (S.η ω) v, dist (vertexPoint ε (S.η ω) v) p ≤ ε ^ a}
  let Q : Set Ω := {ω | Continuous (S.η ω) ∧
    Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) ∧ Function.Surjective (S.η ω) ∧
    ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ω)}
  have hQ : ∀ᵐ ω ∂S.P, ω ∈ Q := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      hS.ae_isLocallyFiniteMult hγ hγ2 (adjacentCellsMeetAeStep 𝒮)] with ω hη hp hlf
    exact ⟨hη.1, hp, hη.2.2.1, hlf⟩
  let G : ℝ → Set Ω := fun ε => (E ε ∩ F ε) ∩ Q
  have hprob : ProbTendsToOne S.P G := by
    exact IterativeBound.probTendsToOne_inter
      (IterativeBound.probTendsToOne_inter
        (IterativeBound.probTendsToOne_of_polyHighProb (hreg Ω S hS))
        (IterativeBound.probTendsToOne_of_polyHighProb hcell))
      (IterativeBound.probTendsToOne_of_ae hQ)
  refine ⟨(C₀ : ℝ), max C (A * B), (χ : ℝ), ξ', (fun ε => ε ^ a), G,
    C₀.coe_nonneg, (le_max_left _ _).trans' hC.le, ?_, hξ', halim, ?_, ?_⟩
  · exact_mod_cast hχ
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Real.rpow_nonneg hε.le _
  · have hprob' := ENNReal.tendsto_nhds_zero.1 hprob e he
    filter_upwards [hprob', halim.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with ε hεprob hεsmall hε
    refine ⟨hεprob, ?_, ?_, ?_, ?_⟩
    · intro ω hω
      exact ⟨hω.2.1, hω.2.2.1, hω.2.2.2.1⟩
    · intro ω hω
      exact hω.1.2
    · intro ω hω v hv w hw
      have hvR := boundary_vertexPoint_mem_larger_closedBall hr hεsmall.le hω.1.2 hv
      have hwR := boundary_vertexPoint_mem_larger_closedBall hr hεsmall.le hω.1.2 hw
      simpa only [dist_eq_norm] using projectedExitVertexValue_boundary_holder_mesh
        (S.mult ε ω) ε (S.η ω) r (r + 1) z ψ hret hv hw hvR hwR
    · intro ω hω v hv w hw
      have hh := projected_interior_holder_of_discrete_holder (S.mult ε ω) (hω.2.2.2.2 ε hε)
        (S.mult_succ_ne_zero hε.le ω) hε hω.2.1 hω.2.2.1 hr hεsmall.le ψ hA.le hψB
        (show (C₀ : ℝ) ≤ (C₀ : ℝ) + 1 by linarith) hret hω.1.2
        (fun hharm hbd => ((hω.1.1 _ _ hball isOpen_ball
          ((convex_ball z r).isConnected ⟨z, mem_ball_self hr⟩) hharm).2 hbd)) v hv w hw
      simpa only [dist_eq_norm] using hh

/-- Corrected harmonic convergence follows from the cited discrete Hölder
statement together with the walk convergence and cell-size inputs. -/
theorem correctedHarmonicConvergence_of_discreteHolderCorrected
    (𝒮 : SpaceFillingSLEModel) (h211 : RandomWalkToLBMStmt 𝒮)
    (hmeps : MepsScalingInput 𝒮) (hexc : BrownianOutwardExcursionAtExitStep)
    (hX : LBMPathFunctionalMeasurableStep 𝒮) (h28 : CellSizeEstimateStmt 𝒮)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) : CorrectedHarmonicConvergenceStmt 𝒮 :=
  correctedHarmonicConvergence_of_goodEvent 𝒮 h211 hmeps hexc hX h28
    (correctedHarmonicRegularityGoodEvent_of_discreteHolderCorrected 𝒮 h28 h32)


end MatedCRT
