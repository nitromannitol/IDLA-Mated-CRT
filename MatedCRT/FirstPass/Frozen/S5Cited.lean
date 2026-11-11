import MatedCRT.Proposed.BerestyckiGwynne
import MatedCRT.Draft.Section2
import HarmonicBalls.Draft.Section1
import HarmonicBalls.Draft.Section2
import HarmonicBalls.Draft.Section5
import HarmonicBalls.Draft.Section6
import HarmonicBalls.Draft.Section8

/-!
# Frozen cited inputs of Proposition 5.1

The cited literature results used by the IDLA lower bound (Proposition 5.1) are frozen literature inputs, each with its locator, until truth-checked. The frozen Props below are definitionally the Draft or Proposed statements; a frozen name is used only as a hypothesis type, never as a proved fact.

Truth status: every entry audited for this paper is TRUE (see the entry docstrings); `FrozenLQGVolumeGrowthAllScales` is a derived consequence. The Harmonic-Balls entries are external inputs to this paper; their proofs are results of the Harmonic-Balls paper, not of this paper. `FrozenBerestyckiGwynneConeBallMass` is not in that audit and is pending truth-checking.

Rules of this file. (i) A per-model statement keeps the model `𝒮` as a parameter (`FrozenX 𝒮 := XStmt 𝒮`); no frozen Prop quantifies over all `SpaceFillingSLEModel`s. (ii) Nothing here is proved. (iii) Items that are about this paper's own objects, rather than a cited result, are not frozen here.

Sources: the Harmonic-Balls paper (arXiv:2208.11795; numbering as in the HB Draft docstrings) and the Berestycki-Gwynne paper (arXiv:2003.10320, BG20).
-/

open MeasureTheory Set Metric
open _root_.HarmonicBalls

namespace MatedCRT

/-- Literature input. Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, arXiv:2003.10320v2, Lemma A.1, equation (A.1), p. 66 (locator as in `MatedCRT/Proposed/BerestyckiGwynne.lean`). Uniform ball-mass estimates for the quantum cone.
Truth-checked: pending. -/
def FrozenBerestyckiGwynneConeBallMass : Prop :=
  BerestyckiGwynneConeBallMassStmt

/-- Derived consequence, not a verbatim BG20 statement. Lemma 2.15 of the IDLA paper (`lemma:greens-function-log-bound`, source line 857; arXiv:2211.04891). The IDLA form kills the walk on the interior vertices `V^ε(B_ρ) \ V^ε(∂B_ρ)`. It is a derived consequence of `FrozenBG20GreenCrudeCanonical 𝒮` (Berestycki-Gwynne, arXiv:2003.10320, Lemma 5.6, equation (5.20), which kills on all of `V^ε(B_ρ)`), by domain monotonicity through `MatedCRT.greenFunctionCrudeBound_of_canonical` (`MatedCRT/FirstPass/S5u.lean:61`).
Truth-checked: TRUE. For each `ζ ∈ (0,1)`, with polynomially high probability as `ε → 0`, `sup_{a,b ∈ V^ε(B_ρ)} G^ε_{B_ρ}(a,b) ≤ ε^{-ζ}`. Statement: `MatedCRT/Draft/Section2.lean:201`. -/
def FrozenGreenFunctionCrudeBound (𝒮 : SpaceFillingSLEModel) : Prop :=
  GreenFunctionCrudeBoundStmt 𝒮

/-- Literature input (Harmonic-Balls paper, arXiv:2208.11795), the input "I2" of its Appendix A (`eq:volume-growth`, source line 3527): for `μ_h`-almost every realization, for all `R > 0`, `β⁺`, `β⁻` in the ranges of [C1], there is `r₀ > 0` with `r^{β⁻} ≤ μ_h(B_r(z)) ≤ r^{β⁺}` for `r < r₀`, `z ∈ B_R`.
Derived consequence, not a separate cited theorem. The HB Draft docstring (`HarmonicBalls/Draft/Section2.lean:115-121`) records it as a consequence. One event for all radii and exponents follows by countable reduction and slack; the corrected exponent ranges include `γ(Q−α₀)`.
Truth-checked: TRUE. Statement: `HarmonicBalls/Draft/Section2.lean:122`. -/
def FrozenLQGVolumeGrowthAllScales : Prop :=
  LQGVolumeGrowthAllScalesStmt.{0}

/-- Literature input (Harmonic-Balls paper, arXiv:2208.11795), Lemma 6.11 (`lemma:very-good-annuli-satisfy-harnack-type-estimate`, source line 1567). Statement: `HarmonicBalls/Draft/Section6.lean:415`.
Truth-checked: TRUE. -/
def FrozenVeryGoodAnnulusHarnackType : Prop :=
  VeryGoodAnnulusHarnackTypeStmt.{0}

/-- Literature input (Harmonic-Balls paper, arXiv:2208.11795), Lemma 8.2 (`lemma:mu_h-doubling-and-harnack`, source line 2151). Statement: `HarmonicBalls/Draft/Section8.lean:74`.
Truth-checked: TRUE. -/
def FrozenTypicalPointManyGoodScales : Prop :=
  TypicalPointManyGoodScalesStmt.{0}

/-- Literature input (Harmonic-Balls paper, arXiv:2208.11795), Proposition 5.3 (`prop:boundary-measure`, source line 836), read as in the HB docstring (`closure Λ ⊆ B_1`). Statement: `HarmonicBalls/Draft/Section5.lean:155`.
Truth-checked: TRUE. -/
def FrozenClusterBoundaryMeasureZero : Prop :=
  ClusterBoundaryMeasureZeroStmt.{0}

/-- Literature input (Harmonic-Balls paper, arXiv:2208.11795), Theorem 5.5 (`theorem:full-theorem-minus-uniqueness`, source line 863). Statement: `HarmonicBalls/Draft/Section5.lean:192`.
Truth-checked: TRUE. -/
def FrozenExistenceHarmonicBalls : Prop :=
  ExistenceHarmonicBallsStmt.{0}

/-- Literature input (Harmonic-Balls paper, arXiv:2208.11795), Proposition 5.6 (`prop:uniqueness`, source line 872; the enlarged harmonic test class, equality only on positive times). Statement: `HarmonicBalls/Draft/Section5.lean:206`.
Truth-checked: TRUE. -/
def FrozenUniquenessHarmonicBalls : Prop :=
  UniquenessHarmonicBallsStmt.{0}

/-- Literature input (Harmonic-Balls paper, arXiv:2208.11795), Proposition 1.3 (`prop:locally-determined`, source line 179; the closed harmonic ball is a local set, Schramm-Sheffield 2013 Lemma 3.9). Statement: `HarmonicBalls/Draft/Section1.lean:151`.
Truth-checked: TRUE. -/
def FrozenHarmonicBallLocalSet : Prop :=
  HarmonicBallLocalSetStmt.{0}

/-- Literature input (Harmonic-Balls paper, arXiv:2208.11795), Lemma 5.8 (`lemma:strong-compatibility`, source line 1019), for a deterministic bounded open `U`. The corrected paper's Lemma 5.8 is stated for Green-regular domains only; the statement for arbitrary bounded open `U` follows from the regular-exhaustion argument (HB repository, `Proofs/Sec5/ExhaustionClusterCompatibility.lean`) and its assembly (`Proofs/Sec5/StrongCompatibilityAssembly.lean`). Statement: `HarmonicBalls/Draft/Section5.lean:246`.
Truth-checked: TRUE. -/
def FrozenClusterStrongCompatibility : Prop :=
  ClusterStrongCompatibilityStmt.{0}

end MatedCRT
