import MatedCRT.FirstPass.S2f
import MatedCRT.FirstPass.S2g.GoodSetMoments
import MatedCRT.Proofs.Sec4.Prop42Closure.ConeWholePlaneSteps

/-!
# First-pass frozen inputs of the good-set step (fp-S2g, q1)

EXTERNAL facts of classical potential theory used by the deterministic certificate lemmas of
`FirstPass/S2g/GoodSet.lean` (the good set of `ConeClosureGoodMeasureLawStep`). They are about the Green function of a
disc and the minimum principle, not about the paper's clusters or harmonic balls.
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric HarmonicBalls

/-- FIRST-PASS FROZEN. Minimum principle for weakly superharmonic functions (EXTERNAL: classical potential theory).
Let `U ⊆ ℂ` be bounded and open, and let `f` be continuous on `closure U` with `Δf ≤ 0` in `U` in the distributional
sense (`LaplacianLE f 0 U`, HarmonicBalls.Defs.Laplacian). If `f ≥ 0` on the frontier of `U`, then `f ≥ 0` on `U`.
Source: standard; locator pending (Armitage and Gardiner, *Classical Potential Theory*, Springer 2001: a continuous
distributionally superharmonic function is superharmonic, by mollification, and the usual minimum principle applies;
no boundary smoothness or connectedness is needed).
Truth check TRUE (ChatGPT, 02:54 UTC; notes/fp-gaps/CHATGPT-idla-frozen-batch.md, table row): Doob (1984) Ch. II §5 p. 20, Minimum Theorem (c), with mollification and the smooth criterion in Ch. II §8 p. 23.
Used by: `certificate_le_supersolution` (FirstPass/S2g/GoodSet.lean). -/
def FrozenSuperharmonicMinimumPrinciple : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℝ), IsOpen U → Bornology.IsBounded U → ContinuousOn f (closure U) →
    LaplacianLE f 0 U → (∀ x ∈ frontier U, 0 ≤ f x) → ∀ x ∈ U, 0 ≤ f x

/-- FIRST-PASS FROZEN. Green function of a disc with pole at the centre (EXTERNAL: classical potential theory). For
`R > 0`, `x ↦ G_{B_R}(0, x)` is continuous on `closedBall 0 R \ {0}` and tends to `+∞` at the pole, since the Newton
kernel `-(2π)⁻¹ log ‖x‖` dominates and the harmonic correction is locally bounded (explicitly `G = (2π)⁻¹ log (R/‖x‖)`).
Source: standard; locator pending (Armitage and Gardiner, *Classical Potential Theory*, Green function of a ball).
HB `continuousOn_greenFunction_ball_of_stmt` gives the continuity part conditionally on `GreenFunctionBallStmt`.
Truth check TRUE (ChatGPT, 02:54 UTC; notes/fp-gaps/CHATGPT-idla-frozen-batch.md, table row): Doob (1984) Ch. II §1 p. 14 equation (1.1), divided by 2π; HB arXiv:2208.11795v3 p. 10 Proposition 2.3.
Used by: `isOpen_certCluster` (FirstPass/S2g/GoodSet.lean). -/
def FrozenGreenDiscPole : Prop :=
  ∀ R : ℝ, 0 < R → ContinuousOn (greenFunction (ball 0 R) 0) (closedBall 0 R \ {0}) ∧
    Tendsto (greenFunction (ball 0 R) 0) (𝓝[≠] 0) atTop

/-- FIRST-PASS FROZEN. Centre formula of the disc Green function (EXTERNAL: classical potential theory). For `R > 0` and
`0 < ‖x‖ < R`, `G_{B_R}(0, x) = (2π)⁻¹ log (R / ‖x‖)` with the normalization `ΔG = -δ` (the explicit Green function of
`B_R` at its centre). Source: HB `greenBall` (HarmonicBalls/Defs/Green.lean:79) at `x = 0`, Armitage and Gardiner,
*Classical Potential Theory*, §4.1; standard; locator pending. Truth check TRUE (ChatGPT, 02:54 UTC; notes/fp-gaps/CHATGPT-idla-frozen-batch.md, table row): Doob (1984) Ch. II §1 p. 14 equation (1.1), with normalization divided by 2π; HB arXiv:2208.11795v3 p. 10 Proposition 2.3 states ΔG = −δ.
Used by: `allDisksCandidate` (FirstPass/S2g/AllDisks.lean). -/
def FrozenGreenBallCentre : Prop :=
  ∀ R : ℝ, 0 < R → ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < R →
    greenFunction (ball (0 : ℂ) R) 0 x = (2 * Real.pi)⁻¹ * Real.log (R / ‖x‖)

/-- FIRST-PASS FROZEN (TRUTH CHECK TRUE). Initial compact confinement of the whole-plane clusters (EXTERNAL: a result
of the harmonic-balls paper, not of IDLA). For `0 < γ < 2`, a whole-plane GFF `(hC, hcirc)` on `(Ω, P)` and its LQG
measure `μ` of `h - γ log|·|` (`IsLQGMeasureOfField P γ γ hcirc μ`), almost surely some time `s > 0` has the regularized
cluster of the obstacle problem in `B_{3/4}` centred at `0` inside `B_{1/2}`. Source: Bou-Rabee and Gwynne, *Harmonic balls
in Liouville quantum gravity*, arXiv:2208.11795v3, Propositions 5.1-5.2, printed pp. 16-17 (initial compact confinement and
shrinking of the closed raw clusters to the centre). Terminology: Armstrong-Kuusi-Mourrat harmonic balls, Duplantier-Sheffield
LQG measure. Truth check TRUE (ChatGPT, 00:50 UTC; notes/fp-gaps/CHATGPT-q1-frozen-truth.md section 1). Provenance: a
corollary of HB Propositions 5.1-5.2 (printed pp. 16-17) together with Lemmas 3.3 and 3.5 (printed p. 13) and regularization
(5.5) (printed p. 17), specialized to alpha_0 = gamma < Q; nested compactness gives a unit-disk raw cluster whose closure lies
in B_{1/2}, and compatibility identifies it with the B_{3/4} raw cluster. The conclusion concerns a local obstacle problem
driven by a whole-plane log-GFF measure, not a confinement of the clusters themselves.
Used by: `SourceHalfBallPathwiseStep` (FirstPass/S2g/GoodSetReduction.lean). -/
def FrozenHBInitialConfinement : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ γ hcirc μ → ∀ᵐ ω ∂P, ∃ s : ℝ, 0 < s ∧
      HarmonicBalls.regularizedCluster (μ ω) (3 / 4) 0 s ⊆ ball (0 : ℂ) (1 / 2)

/-- FIRST-PASS FROZEN. Truth check TRUE (ChatGPT, 00:50 UTC; notes/fp-gaps/CHATGPT-q1-frozen-truth.md §2: equivalent to
`FrozenConeLogLocalCodeLaw` after a standard-Borel realization and a measurable GMC version). Derivable from
`FrozenConeLogLocalCodeLaw` plus the measurable DS11 construction (phase 2). Kept as the frozen interface (operator decision
01:40 UTC). Standard Borel strengthening of `FrozenConeLogLocalCodeLaw`
(FirstPass/Frozen/S2h.lean:29): the source whole-plane LQG model of the local law of a quantum cone may be taken on a
standard Borel space `Ω'`, with a measurable measure map `μ' : Ω' → Measure ℂ`; the laws of the moment vectors
`momentVec φs (μ ω)` (FirstPass/S2g/GoodSetMoments.lean) agree for every countable family of continuous compactly
supported functions with support in `B_1`. Source: Duplantier-Sheffield, Invent. Math. 2011 (arXiv:0808.1560), Section 3
(GMC locality, the LQG measure is a measurable function of the circle averages); IDLA arXiv:2211.04891, eq. (2.4), (2.8),
Fact 2.2(II), p. 12 (cone restriction identity). Terminology: quantum cone (Duplantier-Miller-Sheffield), Kechris standard
Borel spaces. The standard Borel clause and the measurability of `μ'` are the content of this interface. The original
carrier `Ω` is not required to be standard Borel.
Used by: `coneHalfBallGood_of_source` (FirstPass/S2g/GoodSetReduction.lean, via `CandidateConeLogLocalCodeLawStd`). -/
def FrozenConeLogLocalCodeLawStd : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsConeField γ P hC hcirc μ →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω') (P' : Measure Ω')
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
      IsProbabilityMeasure P' ∧ Measurable μ' ∧ IsWholePlaneGFF P' hC' hcirc' ∧
      IsLQGMeasureOfField P' γ γ hcirc' μ' ∧
      ∀ φs : ℕ → ℂ → ℝ, (∀ k, Continuous (φs k) ∧ HasCompactSupport (φs k) ∧ tsupport (φs k) ⊆ ball (0 : ℂ) 1) →
        P.map (fun ω => momentVec φs (μ ω)) = P'.map (fun ω' => momentVec φs (μ' ω'))

-- The whole-plane field law (fact (2) for the fields, `h|_{B_1} =_d (h^ℂ - γ log|·|)|_{B_1}`, Bou-Rabee and Gwynne,
-- arXiv:2211.04891, eq. (2.4)) is REUSED, not copied: it is `FPConeWholePlaneFieldLaw` (`FirstPass/Frozen/S4S5b.lean:40`),
-- which is `ConeWholePlaneFieldLawStep` (`Proofs/Sec4/Prop42Closure/ConeWholePlaneSteps.lean:66`). Truth check TRUE
-- (2026-11-10): equality in law of the measurable observation-process laws applies across arbitrary carriers; it does not
-- assert a coupling on the same carrier. Measurability is not an issue: both
-- fields are measurable (`IsQuantumCone.measurable_pairing`, `measurable_circle`, `Defs/QuantumCone.lean:84-86`, and
-- `IsWholePlaneGFF.measurable_pairing`, `measurable_circle`, HarmonicBalls `Defs/GFF.lean:96, 98`). Used by `firstPass_2_4_canonical`, `firstPass_6_1_corrected`,
-- `firstPass_2_5_canonical`, `firstPass_2_6_corrected` (`S2g/Corrected24.lean`, `S2g/Assembly2456.lean`).

end MatedCRT
