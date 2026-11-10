import MatedCRT.Proposed.BerestyckiGwynne
import MatedCRT.Draft.Section2
import HarmonicBalls.Draft.Section1
import HarmonicBalls.Draft.Section2
import HarmonicBalls.Draft.Section5
import HarmonicBalls.Draft.Section6
import HarmonicBalls.Draft.Section8

/-!
# First-pass frozen cited inputs of Proposition 5.1 (fp-S5-uitems-and-cited-freeze, z2)

Operator decision 2026-11-10 07:42 UTC (`tasks/li.md`, items 35b and G5/G6): the cited literature results used by
the IDLA lower bound `IDLALowerBoundStmt` (Proposition 5.1) are FIRST-PASS FROZEN (EXTERNAL) inputs, each with its
locator, until a truth check. The frozen Props below are definitionally the Draft or Proposed statements; a frozen
name is used only as a hypothesis type, never as a proved fact.

Rules of this file. (i) A per-model statement keeps the model `𝒮` as a parameter (`FrozenX 𝒮 := XStmt 𝒮`); no
frozen Prop quantifies over all `SpaceFillingSLEModel`s. (ii) Nothing here is proved. (iii) Items that are about this
paper's own objects, rather than a cited result, are not frozen here (see the report).

Sources: the Harmonic-Balls paper (arXiv:2208.11795; numbering as in the HB Draft docstrings) and the Berestycki–Gwynne
paper (arXiv:2003.10320, BG20).
-/

open MeasureTheory Set Metric
open _root_.HarmonicBalls

namespace MatedCRT

/-- **FIRST-PASS FROZEN (EXTERNAL, cited); PENDING TRUTH CHECK.** Berestycki–Gwynne, *Random walks on mated-CRT planar
maps and Liouville Brownian motion*, arXiv:2003.10320v2, Lemma A.1, equation (A.1), p. 66 (locator as in
`MatedCRT/Proposed/BerestyckiGwynne.lean`). Uniform ball-mass estimates for the quantum cone.
Used by: `volumeGrowthStmt_of_berestyckiGwynne` (`MatedCRT/Proofs/Sec3/ConeBallMass.lean:17`), which gives
`VolumeGrowthStmt` (the hypothesis `h27` of `firstPass_5_1`, `MatedCRT/FirstPass/S5q.lean`, and of `closed_5_1`). -/
def FrozenBerestyckiGwynneConeBallMass : Prop :=
  BerestyckiGwynneConeBallMassStmt

/-- **FIRST-PASS FROZEN; DERIVED CONSEQUENCE, not verbatim BG20.** Lemma 2.15 of the IDLA paper
(`lemma:greens-function-log-bound`, source line 857; arXiv:2211.04891). The IDLA form kills the walk on the interior
vertices `V^ε(B_ρ) \ V^ε(∂B_ρ)`. It is a derived consequence of `FrozenBG20GreenCrudeCanonical 𝒮`
(`MatedCRT/FirstPass/Frozen/S5BG56.lean:29`, Berestycki–Gwynne, arXiv:2003.10320, Lemma 5.6, equation (5.20), which kills
on all of `V^ε(B_ρ)`), by domain monotonicity through `MatedCRT.greenFunctionCrudeBound_of_canonical`
(`MatedCRT/FirstPass/S5u.lean:61`). Truth: TRUE (operator 09:10; `notes/fp-gaps/CHATGPT-idla-new-frozen-GMS331-BG56.md`).
For each `ζ ∈ (0,1)`, with polynomially high probability as `ε → 0`,
`sup_{a,b ∈ V^ε(B_ρ)} G^ε_{B_ρ}(a,b) ≤ ε^{-ζ}`. Statement: `MatedCRT/Draft/Section2.lean:201`.
Used by: `hG15` of `firstPass_5_1` (`MatedCRT/FirstPass/S5q.lean:114`) and of `closed_5_1`
(`MatedCRT/FirstPass/Closure/Prop51.lean`). -/
def FrozenGreenFunctionCrudeBound (𝒮 : SpaceFillingSLEModel) : Prop :=
  GreenFunctionCrudeBoundStmt 𝒮

/-- **FIRST-PASS FROZEN (EXTERNAL, cited); PENDING TRUTH CHECK.** Harmonic-Balls paper, arXiv:2208.11795, the input
"I2" of its Appendix A (`eq:volume-growth`, source line 3527): for `μ_h`-almost every realization, for all `R > 0`,
`β⁺`, `β⁻` in the ranges of [C1], there is `r₀ > 0` with `r^{β⁻} ≤ μ_h(B_r(z)) ≤ r^{β⁺}` for `r < r₀`, `z ∈ B_R`.
CAVEAT (recorded, not resolved here): the HB Draft docstring (`HarmonicBalls/Draft/Section2.lean:115-121`) says this
is a consequence, not a literature input, and the ChatGPT Pro audit of the 5.1 bundle (`notes/fp-gaps/CHATGPT-idla-5-1-audit-PRO.md`, l.118-132) lists it as unproved (U item `hI2`).
It is frozen per operator decision 07:42 UTC (G5/G6) and must be re-checked for source status.
Statement: `HarmonicBalls/Draft/Section2.lean:122`.
Used by: `hI2` of `firstPass_5_1` (`S5q.lean:119`), of `closed_5_1` (`Prop51.lean:63`), of
`coneHalfBallClosureInsideStep_fp` (`MatedCRT/FirstPass/S5r/ClosureInside.lean:25`) and of
`firstPass_strictObstacleGap` (`MatedCRT/FirstPass/S4S5b.lean:27`). -/
def FrozenLQGVolumeGrowthAllScales : Prop :=
  LQGVolumeGrowthAllScalesStmt.{0}

/-- **FIRST-PASS FROZEN (EXTERNAL, cited); PENDING TRUTH CHECK.** Harmonic-Balls paper, arXiv:2208.11795, Lemma 6.11
(`lemma:very-good-annuli-satisfy-harnack-type-estimate`, source line 1567). Statement: `HarmonicBalls/Draft/Section6.lean:415`.
Used by: `h611` of `firstPass_5_1` (`S5q.lean:118`) and `firstPass_strictObstacleGap` (`S4S5b.lean:25`). -/
def FrozenVeryGoodAnnulusHarnackType : Prop :=
  VeryGoodAnnulusHarnackTypeStmt.{0}

/-- **FIRST-PASS FROZEN (EXTERNAL, cited); PENDING TRUTH CHECK.** Harmonic-Balls paper, arXiv:2208.11795, Lemma 8.2
(`lemma:mu_h-doubling-and-harnack`, source line 2151). Statement: `HarmonicBalls/Draft/Section8.lean:74`.
Used by: `h82` of `firstPass_5_1` (`S5q.lean:119`) and `firstPass_strictObstacleGap` (`S4S5b.lean:27`). -/
def FrozenTypicalPointManyGoodScales : Prop :=
  TypicalPointManyGoodScalesStmt.{0}

/-- **FIRST-PASS FROZEN (EXTERNAL, cited); PENDING TRUTH CHECK.** Harmonic-Balls paper, arXiv:2208.11795, Proposition 5.3
(`prop:boundary-measure`, source line 836), read as in the HB docstring (`closure Λ ⊆ B_1`). Statement:
`HarmonicBalls/Draft/Section5.lean:155`.
Used by: `hBdry` of `firstPass_5_1` (`S5q.lean:128`), in the canonical half-ball step. -/
def FrozenClusterBoundaryMeasureZero : Prop :=
  ClusterBoundaryMeasureZeroStmt.{0}

/-- **FIRST-PASS FROZEN (EXTERNAL, cited); PENDING TRUTH CHECK.** Harmonic-Balls paper, arXiv:2208.11795, Theorem 5.5
(`theorem:full-theorem-minus-uniqueness`, source line 863). Statement: `HarmonicBalls/Draft/Section5.lean:192`.
Used by: `hEx` of `firstPass_5_1` (`S5q.lean:128`), in the canonical half-ball step and in the closure step
(`coneHalfBallClosureInsideStep_fp`, `S5r/ClosureInside.lean:31`). -/
def FrozenExistenceHarmonicBalls : Prop :=
  ExistenceHarmonicBallsStmt.{0}

/-- **FIRST-PASS FROZEN (EXTERNAL, cited); PENDING TRUTH CHECK.** Harmonic-Balls paper, arXiv:2208.11795, Proposition 5.6
(`prop:uniqueness`, source line 872). Statement: `HarmonicBalls/Draft/Section5.lean:206`.
Used by: `hProp56` of `firstPass_5_1` (`S5q.lean:129`), in the canonical half-ball step. -/
def FrozenUniquenessHarmonicBalls : Prop :=
  UniquenessHarmonicBallsStmt.{0}

/-- **FIRST-PASS FROZEN (EXTERNAL, cited); PENDING TRUTH CHECK.** Harmonic-Balls paper, arXiv:2208.11795, Proposition 1.3
(`prop:locally-determined`, source line 179; the closed harmonic ball is a local set, Schramm–Sheffield 2013 Lemma 3.9).
Statement: `HarmonicBalls/Draft/Section1.lean:151`.
Used by: `hloc` of `firstPass_5_1` (`S5q.lean:132`) and of the closure step (`S5r/ClosureInside.lean:31`). -/
def FrozenHarmonicBallLocalSet : Prop :=
  HarmonicBallLocalSetStmt.{0}

/-- **FIRST-PASS FROZEN (EXTERNAL, cited); PENDING TRUTH CHECK.** Harmonic-Balls paper, arXiv:2208.11795, Lemma 5.8
(`lemma:strong-compatibility`, source line 1019), for a deterministic bounded open `U`. Statement:
`HarmonicBalls/Draft/Section5.lean:246`.
Used by: `hSC` of `firstPass_5_1` (`S5q.lean:133`) and of the closure step (`S5r/ClosureInside.lean:31`). -/
def FrozenClusterStrongCompatibility : Prop :=
  ClusterStrongCompatibilityStmt.{0}

end MatedCRT
