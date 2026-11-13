import MatedCRT.FirstPass.S3i.LensStep
import MatedCRT.FirstPass.S3i.ExitAlmostSure
import MatedCRT.FirstPass.S3i.QuenchedBoundsCorrected
import MatedCRT.FirstPass.SLERef.Certified
import MatedCRT.FirstPass.S3i.FrozenFloored
import MatedCRT.FirstPass.LPBridge.BrownianOutwardExcursion

/-!
# Corrected Lemma 3.6 from the floored one-sided boundary estimate

This file proves the corrected Lemma 3.6 from the floored boundary estimate
`FrozenOneSidedBoundaryContinuityFloored 𝒮` (S3i/FrozenFloored.lean).

The annealed clause is proved by `annealed_3_6_of_quenchedLensStep`, from the quenched lens step.

NAMED HYPOTHESIS, NOT IN THE PAPER: `hLensFl : FrozenOneSidedBoundaryContinuityFloored 𝒮 → QuenchedLensStep 𝒮`
(the floored quenched lens step). The lens bound `lensProb_le_of_BE_fp36` (S3i/LensBE.lean:27–50) cannot be fed by the
floored form as typed, for two reasons:
(i) the floor exponent `β` of `FrozenOneSidedBoundaryContinuityFloored` is chosen after `ρ`, `Ω` and `S`, while the exponent
`b` of `QuenchedLensStep` (Proof.lean:240) is chosen before `∀ ρ Ω S`;
(ii) the lens bound needs the boundary-distance floor to be at most the lens scale: `lensProb_le_of_BE_fp36` applies the BE
at the radius `ε ^ (b / 2) / 16` to the vertex with `0 < infDist ≤ 6 * ε ^ b` (LensBE.lean:37–38), and the floored bound gives
the rate `ε ^ (ν * (β - b / 2))`, which is `ε ^ (ν * b / 2)` only when `β ≥ b`.
Since a valid floor exponent `β` remains valid when decreased, the existential does not supply `β ≥ b`.
PENDING TRUTH CHECK (see docs/campaign/FROZEN-PROVENANCE.md).
-/

open MeasureTheory

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The annealed same-walk clause of corrected Lemma 3.6 (`CorrectedHarmonicSameWalkAnnealedStmt`), from the quenched
lens step `hQLS` (`QuenchedLensStep`, S3i/Proof.lean:240). -/
theorem annealed_3_6_of_quenchedLensStep {𝒮 : SpaceFillingSLEModel} (h211 : RandomWalkToLBMStmt 𝒮)
    (h28 : CellSizeEstimateStmt 𝒮) (hm : MepsScalingInput 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) (hQLS : QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮 := by
  refine ⟨firstPass_3_6_convergence_corrected h211 h28 hm hexc h32, ?_⟩
  intro γ hγ0 hγ2
  obtain ⟨b, hb, hlens⟩ := hQLS γ hγ0 hγ2
  refine ⟨b, hb, fun ρ hρ0 hρ1 Ω _ S hS r z hr hball ψ H χ y hadm => ?_⟩
  obtain ⟨κ, ν, C, ε₀, hκ, hν, hC, hε₀, G, C₁, hC₁, hG⟩ :=
    hlens ρ hρ0 hρ1 Ω S hS r z hr hball ψ H χ y hadm
  obtain ⟨-, -, hψ, -⟩ := hadm
  refine ⟨κ, ν, C₁ + 2 * C, ε₀, hκ, hν, by linarith, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨hPG, hω⟩ := hG ε hε hεε₀
  have := hS.isProbabilityMeasure
  have hper : ∀ ω ∈ G ε,
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
        (Prod.mk ω ⁻¹' {p : Ω × (ℕ → ℤ) |
          (1 + (H : ℝ)) * ε ^ (b * (χ : ℝ) / 2) < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2})
        ≤ ENNReal.ofReal (2 * C * ε ^ (ν * b / 2)) := by
    intro ω hωG
    obtain ⟨hbad, hfar⟩ := hω ω hωG
    have hincl : Prod.mk ω ⁻¹' {p : Ω × (ℕ → ℤ) |
          (1 + (H : ℝ)) * ε ^ (b * (χ : ℝ) / 2) < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2}
        ⊆ {x | ¬ SameWalkGood S r z ε ω x} ∪
          {x | SameWalkGood S r z ε ω x ∧
            ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)} := by
      intro x hx
      by_cases hg : SameWalkGood S r z ε ω x
      · right
        refine ⟨hg, ?_⟩
        by_contra hnf
        have hnear : dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)
            ≤ ε ^ (b / 2) / 2 := not_lt.1 hnf
        have hd := sameWalk_disc_le_of_near_fp36 hr hψ (Real.rpow_nonneg hε.le _) hg (sameWalkExitPoint_mem_closedBall_fp36 hg) hnear
        have e : (ε ^ (b / 2)) ^ (χ : ℝ) = ε ^ (b * (χ : ℝ) / 2) := by
          rw [← Real.rpow_mul hε.le]
          ring_nf
        rw [e] at hd
        have hX : 0 ≤ ε ^ (b * (χ : ℝ) / 2) := Real.rpow_nonneg hε.le _
        have hx' : (1 + (H : ℝ)) * ε ^ (b * (χ : ℝ) / 2) < sameWalkExitDiscrepancy S r z ψ ε ω x := hx
        nlinarith [NNReal.coe_nonneg H]
      · left
        exact hg
    have hsum : ENNReal.ofReal (C * ε ^ (ν * b / 2)) + ENNReal.ofReal (C * ε ^ (ν * b / 2))
        = ENNReal.ofReal (2 * C * ε ^ (ν * b / 2)) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hC (Real.rpow_nonneg hε.le _))
        (mul_nonneg hC (Real.rpow_nonneg hε.le _))]
      congr 1
      ring
    exact (measure_mono hincl).trans ((measure_union_le _ _).trans ((add_le_add hbad hfar).trans hsum.le))
  have hsplit := sectionwiseOuterProb_le_of_good_fp36 S.P (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (fun ω => isProbabilityMeasure_srwLaw _ _)
    {p : Ω × (ℕ → ℤ) | (1 + (H : ℝ)) * ε ^ (b * (χ : ℝ) / 2) < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2}
    (G ε) (ENNReal.ofReal (2 * C * ε ^ (ν * b / 2))) hper
  refine hsplit.trans ?_
  calc S.P (G ε)ᶜ + ENNReal.ofReal (2 * C * ε ^ (ν * b / 2))
      ≤ ENNReal.ofReal (C₁ * ε ^ κ) + ENNReal.ofReal (2 * C * ε ^ (ν * b / 2)) := add_le_add hPG le_rfl
    _ = ENNReal.ofReal (C₁ * ε ^ κ + 2 * C * ε ^ (ν * b / 2)) :=
        (ENNReal.ofReal_add (mul_nonneg hC₁ (Real.rpow_nonneg hε.le _))
          (mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg hε.le _))).symm
    _ ≤ ENNReal.ofReal ((C₁ + 2 * C) * (ε ^ κ + ε ^ (ν * b / 2))) :=
        ENNReal.ofReal_le_ofReal (by
          nlinarith [mul_nonneg hC₁ (Real.rpow_nonneg hε.le (ν * b / 2)),
            mul_nonneg hC (Real.rpow_nonneg hε.le κ), Real.rpow_nonneg hε.le κ,
            Real.rpow_nonneg hε.le (ν * b / 2)])


end FirstPass36

/-- Corrected Lemma 3.6, rate conjunct (the fixed-start annealed same-walk clause, tex lines 1431-1441), from the floored
one-sided boundary estimate `hBE` (`FrozenOneSidedBoundaryContinuityFloored`) and the named hypothesis `hLensFl`
(the quenched lens step from the floored BE; NOT in the paper, see the header). -/
theorem closed_3_6_rate_floored {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFloored 𝒮 → MatedCRT.FirstPass36.QuenchedLensStep 𝒮) :
    MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  (MatedCRT.FirstPass36.annealed_3_6_of_quenchedLensStep hC.randomWalkToLBM hC.cellSizeEstimate hC.mepsScaling hexc
    hC.frozenDiscreteHolderContinuityCorrected (hLensFl hBE)).2

/-- Corrected Lemma 3.6, both clauses: the convergence clause `CorrectedHarmonicConvergenceStmt` and the annealed
same-walk clause, from the floored one-sided boundary estimate `hBE` and the named hypothesis `hLensFl` (see
`closed_3_6_rate_floored`). -/
theorem closed_3_6_full_floored {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮) (hexc : FrozenBrownianOutwardExcursionAtExit)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFloored 𝒮 → MatedCRT.FirstPass36.QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  MatedCRT.FirstPass36.annealed_3_6_of_quenchedLensStep hC.randomWalkToLBM hC.cellSizeEstimate hC.mepsScaling hexc
    hC.frozenDiscreteHolderContinuityCorrected (hLensFl hBE)

/-- Wrapper of `closed_3_6_rate_floored`: the Brownian exit binder `hexc` is discharged by
`MatedCRT.frozenBrownianOutwardExcursionAtExit_holds` (LPBridge/BrownianOutwardExcursion.lean:113). -/
theorem closed_3_6_rate_floored_bm {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFloored 𝒮 → MatedCRT.FirstPass36.QuenchedLensStep 𝒮) :
    MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  closed_3_6_rate_floored (𝒮 := 𝒮) (ν := ν) (hC := hC) (hexc := frozenBrownianOutwardExcursionAtExit_holds)
    (hBE := hBE) (hLensFl := hLensFl)

/-- Wrapper of `closed_3_6_full_floored`: the Brownian exit binder `hexc` is discharged by
`MatedCRT.frozenBrownianOutwardExcursionAtExit_holds`. -/
theorem closed_3_6_full_floored_bm {𝒮 : SpaceFillingSLEModel} (ν : ℝ → Measure SLEPathCode)
    (hC : CertifiedReferenceModel ν 𝒮)
    (hBE : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFloored 𝒮)
    (hLensFl : MatedCRT.FirstPass36.FrozenOneSidedBoundaryContinuityFloored 𝒮 → MatedCRT.FirstPass36.QuenchedLensStep 𝒮) :
    CorrectedHarmonicConvergenceStmt 𝒮 ∧ MatedCRT.FirstPass36.CorrectedHarmonicSameWalkAnnealedStmt 𝒮 :=
  closed_3_6_full_floored (𝒮 := 𝒮) (ν := ν) (hC := hC) (hexc := frozenBrownianOutwardExcursionAtExit_holds)
    (hBE := hBE) (hLensFl := hLensFl)

end MatedCRT

#print axioms MatedCRT.FirstPass36.annealed_3_6_of_quenchedLensStep
#print axioms MatedCRT.closed_3_6_rate_floored
#print axioms MatedCRT.closed_3_6_full_floored
#print axioms MatedCRT.closed_3_6_rate_floored_bm
#print axioms MatedCRT.closed_3_6_full_floored_bm
