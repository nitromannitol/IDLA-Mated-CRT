import MatedCRT.Defs.QuantumCone
import MatedCRT.Defs.RandomWalk
import HarmonicBalls.Defs.LBM
import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Draft.Section1
import HarmonicBalls.Draft.Section5
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# The random setting: quantum cone, space-filling SLE, the embedded mated-CRT map and LBM
(Sections 1.1.4, 2.1-2.7, lines 165-205, 402-740)

Uses Leonardo Bonanno's mated-CRT bundle, as ported to Lattice-Probability (`LatticeProb.Bonanno.*`, adapted from
Leonardo Bonanno's lean-formalizations, MatedCRTHarmonic, commit 31e7483): `MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling`
(module `LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling`), with `coneField`, `coneRadial` (modules
`...Frozen.MatedCRTConeField`, `...Frozen.MatedCRTConeRadial`), `Field` and `Path2`, and Leo's test functions
`LQGMetric.TestC` (module `LatticeProb.Bonanno.LQGMetric.Statement.Field`).

## The map: Definition 1.1 (operator decision (L1), inbox 2026-11-03 16:20 UTC)

The paper defines the mated-CRT map by Definition 1.1, from the boundary-length Brownian pair `(L, R)`. So the
environment carries this pair, `bm`, and the edge multiplicity of the map with cell size `ε` is
`MatedCRTEnv.mult S ε ω = bmEdgeCount ε L R` with `(L_t, R_t) = bm ω t`. It agrees with Leo's edge count of
`MatedCRTHarmonic.MatedCRT.graph`. The SLE/LQG description (Definition 1.2, `cellMult`) is the same graph a.s. by
DMS14 Theorem 1.9 / Lemma 8.8 (line 207); this equivalence is not used by any statement, and it is an optional DMS input
(INPUT-REQUESTS IR-A2). The embedding of Definition 1.2 is used through the cells `η([a - ε, a])` and the positions
`η(a)`, which only involve `η`.

## Whole-plane space-filling SLE: the mating-of-trees coupling

`MatedCRTEnv.IsValid` requires Leo's mating-of-trees coupling (`IsMatingOfTreesCoupling`, 24 fields: REUSE-LEO.md 1.5)
for the curve `η`, the pair `bm` and a `γ`-quantum cone whose pairings with test functions are those of our field. It
gives, among others: `η` is a reparametrization of a whole-plane space-filling SLE_{16/γ²} `ηL` (a measurable
function of an independent imaginary-geometry field, `igMap`) which is surjective and transient (`spaceFilling`),
parametrized by the LQG area (`areaParam`); `bm` is a correlated two-sided Brownian motion (`boundaryLawBM`, DMS14
Theorem 1.9 and GHMS Theorem 1.1) and the boundary-length pair of `(h, η)` (`boundaryLength`); DMS14 Lemmas 8.8, 8.9,
8.13, 8.14 (`merge`, `onlyMerge`, `visitBound`); GHM15 Prop 3.4 (`segmentsContainBalls`), GHS Lemma A.4 (`coverage`),
GMS-T Props 4.4, 4.6 (`cellMoments`). These fields are literature statements taken as hypotheses (their sources are
quoted in the bundle).

Documented weak spots of the bundle (Leo's disclosures, REUSE-LEO.md 1.3, 1.5): the case `γ = √2` (`κ' = 8`) of
`boundaryLawBM` rests on a step of DMS14 which the cited proof leaves unresolved; `onlyMerge` and `visitBound` rest on
the sketched DMS14 Lemma 8.13; `igMap` is stated in whole-plane form (coordinate change, locality) for a fixed witness;
a 24-field bundle could be inconsistent where an abstract predicate cannot; cells adjacent in Definition 1.1 are only
known (from `merge`) to intersect, not to share a boundary arc; the bundle contains no Liouville Brownian motion.

## The abstract SLE model (E-A1), kept for the remaining inputs

Every statement also takes a `SpaceFillingSLEModel` `𝒮`, whose predicate `𝒮.IsSLE P 𝓕 κ η` stands for: *under `P`, the
random curve `η`, viewed modulo increasing reparametrization, is a whole-plane space-filling SLE_κ from `∞` to `∞`,
independent of the σ-algebra `𝓕`*. It is kept because the SLE inputs which the bundle does not provide in our form
(MatedCRT/External/SLE.lean: scale invariance with a random factor, invariance under reparametrization, independence of
a smaller σ-algebra) are stated over it. See ESCALATIONS, entry "space-filling SLE".

## Whole-plane space-filling SLE (the model)

Whole-plane space-filling SLE_κ from `∞` to `∞` (Miller-Sheffield, Imaginary geometry IV, Sections 1.2.3 and 4.3;
lines 606-621) is not defined in Lean. Every statement takes as a parameter a `SpaceFillingSLEModel` `𝒮`, whose
predicate `𝒮.IsSLE P 𝓕 κ η` stands for: *under `P`, the random curve `η`, viewed modulo increasing reparametrization,
is a whole-plane space-filling SLE_κ from `∞` to `∞`, independent of the σ-algebra `𝓕`*. Statements are proved for
every model, from the literature inputs (the cited results, stated for the same model) as hypotheses; they are about
SLE for the model whose predicate is the true one. See ESCALATIONS, entry "space-filling SLE".

## The environment

`MatedCRTEnv Ω` bundles the random objects of the paper on a sample space `Ω`: the law `P`, the field `h` of the
quantum cone (pairings `hC`, circle averages `hcirc`), its LQG measure `μ = μ_h`, the curve `η`, and the LQG clock
`clock` of Liouville Brownian motion. `MatedCRTEnv.IsValid 𝒮 γ` says that these are: a probability; the circle
average embedding of the `γ`-quantum cone (Definition 2.1); its `γ`-LQG measure (eq:measure-lim, line 470); a
whole-plane space-filling SLE_{16/γ²} independent of `h` (line 192); parametrized so that `η(0) = 0` and
`μ_h(η([a,b])) = b - a` (line 193); and, for every starting point, the LQG clock of planar Brownian motion for `h`
(Section 2.7, line 712; `HarmonicBalls.IsLQGClock`), which is a time change clock.

The mated-CRT map with cell size `ε` is the multigraph `bmEdgeCount ε L R` on `ℤ` of the pair `(L, R) = bm ω`
(Definition 1.1); simple random walk on it is `srwLaw`. Leo's walk `LFMultigraph.walkLaw` (an edge-end walk) and
`exitGreen` are related to `srwLaw` and `greenFn` by bridges (REUSE-LEO.md 1.2), written in Lattice-Probability.

## Liouville Brownian motion and the scaling constants

`m₀` (eq:mo, line 727) is the median of the (annealed) exit time of LBM started at `0` from `B_{1/2}`; the rescaled
LBM is `X^z_t = B^z_{φ⁻¹(t m₀)}` (eq:rescaled-lbm, line 723). `m_ε` (eq:meps, line 731) is the median of the
(annealed) number of steps before the embedded walk `η(X^{0,ε})` exits `B_{1/2}`.

## Harmonic balls of the quantum cone (Theorem 2.3)

`IsConeHarmonicBallFamily μ Λ`: each `Λ_t`, `t > 0`, is a harmonic ball for `μ` centred at `0` (Definition 1.3,
`HarmonicBalls.IsHarmonicBall`) and the family satisfies (a)-(b) (`HarmonicBalls.SatisfiesHarmonicBallConditions`)
and (c) (`SatisfiesObstacleCharacterization`) of Theorem 2.3. "The" family of Theorem 2.3 is any family satisfying
these conditions, a.s. unique by Theorem 2.3.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

/-- A model of the law of whole-plane space-filling SLE (see the module docstring): `IsSLE P 𝓕 κ η` stands for
"under `P`, the curve `η` viewed modulo increasing reparametrization is a whole-plane space-filling SLE_κ from `∞` to
`∞`, independent of `𝓕`". -/
structure SpaceFillingSLEModel where
  /-- The predicate "`η` is a whole-plane space-filling SLE_κ independent of `𝓕`". -/
  IsSLE : ∀ {Ω : Type} [MeasurableSpace Ω], Measure Ω → MeasurableSpace Ω → ℝ → (Ω → ℝ → ℂ) → Prop

/-- The random objects of the paper on the sample space `Ω` (see the module docstring). -/
structure MatedCRTEnv (Ω : Type) [MeasurableSpace Ω] where
  /-- The probability measure. -/
  P : Measure Ω
  /-- The pairings `(h, φ)` of the quantum cone field. -/
  hC : Ω → (ℂ → ℝ) → ℝ
  /-- The circle averages `h_r(z)` of the quantum cone field. -/
  hcirc : Ω → ℝ → ℂ → ℝ
  /-- The `γ`-LQG measure `μ_h`. -/
  μ : Ω → Measure ℂ
  /-- The space-filling curve `η`, parametrized by `μ_h`-area. -/
  η : Ω → ℝ → ℂ
  /-- The LQG clock `φ` of planar Brownian motion (Liouville Brownian motion is `B_{φ⁻¹(t)}`). -/
  clock : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ
  /-- The boundary-length pair `t ↦ (L_t, R_t)` of `(h, η)`, a continuous path `ℝ → ℝ × ℝ` (Leo's
  `MatedCRTHarmonic.MatedCRT.Path2`): the two-dimensional Brownian motion of Definition 1.1 (line 170) which
  defines the mated-CRT map. -/
  bm : Ω → C(ℝ, ℝ × ℝ)

/-- `η` is a space-filling curve parametrized by `μ`-area with `η(0) = 0` (line 193): continuous, onto `ℂ`, with
`μ(η([a,b])) = b - a` for all `a < b`. -/
def IsAreaParametrized (μ : Measure ℂ) (η : ℝ → ℂ) : Prop :=
  Continuous η ∧ η 0 = 0 ∧ Function.Surjective η ∧
    ∀ a b : ℝ, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a)

/-- The σ-algebra `σ(h)` generated by the pairings of the field with test functions
(`HarmonicBalls.fieldSigmaAlgebra` with no log singularity, on all of `ℂ`). -/
@[instance_reducible]
noncomputable def MatedCRTEnv.fieldSigma {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) : MeasurableSpace Ω :=
  fieldSigmaAlgebra 0 S.hC univ

/-- The σ-algebra `σ(h, η)` generated by the field and the curve. -/
@[instance_reducible]
noncomputable def MatedCRTEnv.envSigma {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) : MeasurableSpace Ω :=
  S.fieldSigma ⊔ ⨆ s : ℝ, MeasurableSpace.comap (fun ω => S.η ω s) inferInstance

/-- The environment is the one of the paper for `γ` and the space-filling SLE model `𝒮` (module docstring). -/
structure MatedCRTEnv.IsValid {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (𝒮 : SpaceFillingSLEModel)
    (γ : ℝ) : Prop where
  /-- `P` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure S.P
  /-- `h` is the circle average embedding of the `γ`-quantum cone (Definition 2.1). -/
  isQuantumCone : IsQuantumCone γ S.P S.hC S.hcirc
  /-- `μ = μ_h` is the `γ`-LQG measure of `h` (eq:measure-lim, line 470). -/
  isLQGMeasure : IsLQGMeasure S.P γ S.hcirc S.μ
  /-- `η` (modulo parametrization) is a whole-plane space-filling SLE_{16/γ²} independent of `h` (line 192). -/
  isSLE : 𝒮.IsSLE S.P S.fieldSigma (16 / γ ^ 2) S.η
  /-- `η(0) = 0` and `μ_h(η([a,b])) = b - a` (line 193). -/
  isAreaParametrized : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω)
  /-- `clock` is, for every starting point, the LQG clock of planar Brownian motion for `h`, and a.s. (in the
  Brownian path) a time change clock. -/
  isLQGClock : ∀ᵐ ω ∂S.P, ∀ z : ℂ, IsLQGClock planarBrownianMotion γ (S.hcirc ω) z (S.clock ω) ∧
    ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (S.clock ω b)
  /-- **The mating-of-trees coupling** (operator decision (L1); Leo's `IsMatingOfTreesCoupling`, REUSE-LEO.md 1.5;
  module docstring): there are a whole-plane GFF `X` and Brownian motions `B, B'` (the `γ`-quantum cone
  `coneField X (coneRadial γ γ B B')`, DMS14 Definition 4.10), the data `X₀, B₀, B₀'` of the `0`-quantum cone, the
  imaginary-geometry field `hIG₀ + U`, the whole-plane space-filling SLE_{16/γ²} `ηL` and its reparametrizations
  `η'`, `η₀` by LQG area, forming a mating-of-trees coupling with boundary-length pair `bm`, such that a.s. the curve
  `η'` is `η` and the pairings of the cone field with test functions are those of `h`. -/
  matingOfTrees : ∃ (X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η' η₀ : Ω → C(ℝ, ℂ)),
    MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ S.P X X₀ hIG₀ B B' B₀ B₀' U ηL η' η₀ S.bm ∧
      ∀ᵐ ω ∂S.P, ⇑(η' ω) = S.η ω ∧ ∀ φ : LQGMetric.TestC,
        S.hC ω ⇑φ = MatedCRTHarmonic.MatedCRT.coneField (X ω)
          (MatedCRTHarmonic.MatedCRT.coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)) φ

/-- The `γ`-mated-CRT map with cell size `ε` of the environment, as an edge multiplicity on `ℤ`: Definition 1.1 for
the boundary-length pair `(L_t, R_t) = bm ω t` (`bmEdgeCount`; operator decision (L1)). Under the mating-of-trees
coupling it is a.s. the SLE/LQG description `cellMult ε (S.η ω)` of Definition 1.2 (DMS14 Theorem 1.9 / Lemma 8.8,
line 207; optional input, INPUT-REQUESTS IR-A2). -/
noncomputable def MatedCRTEnv.mult {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) (ω : Ω) :
    ℤ → ℤ → ℕ :=
  bmEdgeCount ε (fun t => (S.bm ω t).1) (fun t => (S.bm ω t).2)

/-- `m₀`: the median of the annealed exit time of Liouville Brownian motion started at `0` from `B_{1/2}`
(eq:mo, line 727). -/
noncomputable def MatedCRTEnv.m₀ {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) : ℝ :=
  medianOf fun s => ∫⁻ ω, planarBrownianMotion 0
    {b | lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ≤ ENNReal.ofReal s} ∂S.P

/-- `c₀ = 2/m₀`: the constant in the limits of Lemmas 3.3-3.5, 3.7, Theorem 4.1 and Lemma 4.8 for the Green's function
`G` normalized by `ΔG = -δ` (HB's `greenFunction`). CORRECTION [C1] (ESCALATIONS E-A3, review-C): the printed constant
`m₀` is false (e.g. for `γ² ≤ 0.8`); the Brownian occupation density is `2G` and the walk at step `m_ε t` approximates
`X_t = LBM_{m₀ t}`, which gives `2/m₀` (line 1172). Not to be confused with the annulus constant `𝐜₀` of Section 6. -/
noncomputable def MatedCRTEnv.c₀ {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) : ℝ :=
  2 / S.m₀

/-- The joint law of the environment and the independent IDLA walkers. For a valid environment the conditional
walker law is measurable, so the first branch applies. The zero measure is only a totalization for invalid settings. -/
noncomputable def MatedCRTEnv.idlaJointMeasure {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ε : ℝ) : Measure (Ω × (ℕ → ℕ → ℤ)) := by
  classical
  exact if h : Measurable (fun ω => walkerSequenceLaw (S.mult ε ω) 0) then
    S.P ⊗ₘ (⟨fun ω => walkerSequenceLaw (S.mult ε ω) 0, h⟩ : Kernel Ω (ℕ → ℕ → ℤ))
  else 0

/-- The *annealed outer probability* of an event `E ⊆ Ω × (ℕ → ℕ → ℤ)` of the environment and the IDLA walkers of the
map with cell size `ε`, which given `(h, η)` are independent simple random walks on `𝒢^ε` started at the origin
(`walkerSequenceLaw (S.mult ε ω) 0`): `annealedOuterProb` (MatedCRT/Defs/Notation.lean). -/
noncomputable def MatedCRTEnv.idlaProb {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ)
    (E : Set (Ω × (ℕ → ℕ → ℤ))) : ℝ≥0∞ :=
  annealedOuterProb S.P (fun ω => walkerSequenceLaw (S.mult ε ω) 0) E

/-- The number of steps before the embedded walk `η(x n)` leaves `U`. -/
noncomputable def embeddedExitTime (ε : ℝ) (η : ℝ → ℂ) (U : Set ℂ) (x : ℕ → ℤ) : ℕ∞ :=
  vExitTime {k | vertexPoint ε η k ∈ U} x

/-- `m_ε`: the median of the annealed exit time of the embedded walk `η(X^{0,ε})` from `B_{1/2}`, the walk being
started from `a^ε_0` (eq:meps, line 731). -/
noncomputable def MatedCRTEnv.mε {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ε : ℝ) : ℝ :=
  medianOf fun s => ∫⁻ ω, srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0)
    {x | (embeddedExitTime ε (S.η ω) (ball 0 (1 / 2)) x : ℝ≥0∞) ≤ ENNReal.ofReal s} ∂S.P

/-- The path of the rescaled Liouville Brownian motion `X_t = B_{φ⁻¹(t m₀)}` (eq:rescaled-lbm, line 723) driven by the
planar Brownian path `b`, for the clock `F` and the constant `m₀`. -/
noncomputable def rescaledLBMPath (F : ContinuousPath ℂ → ℝ≥0 → ℝ) (m₀ : ℝ) (b : ContinuousPath ℂ) (t : ℝ≥0) : ℂ :=
  liouvilleBrownianPath F b (m₀.toNNReal * t)

/-- The embedded walk `t ↦ η(x_{mε t})`, extended from `mε⁻¹ ℕ` to `[0, ∞)` by linear interpolation
(line 734, Section 3.3, line 1099). -/
noncomputable def interpolatedWalk (ε : ℝ) (η : ℝ → ℂ) (mε : ℝ) (x : ℕ → ℤ) (t : ℝ≥0) : ℂ :=
  let s : ℝ := mε * t
  let n : ℕ := ⌊s⌋₊
  let θ : ℝ := s - n
  ((1 - θ : ℝ) : ℂ) * vertexPoint ε η (x n) + (θ : ℂ) * vertexPoint ε η (x (n + 1))

/-- The first time `inf {t ≥ 0 : f t ∉ U}` a path leaves `U` (HB's `pathExitTime`) and its position there
(junk `f 0` if it never leaves). -/
noncomputable def pathExitPosition (U : Set ℂ) (f : ℝ≥0 → ℂ) : ℂ :=
  f ((pathExitTime U f).untopD 0)

/-- Condition (c) of Theorem 2.3 (lines 518-526): if `Λ_t ⊆ B_r` then for all `ρ > r`,
`Λ_t = int(cl {x ∈ B_ρ : w̄^{B_ρ}_t(x) > -t G_{B_ρ}(0,x)})` (`HarmonicBalls.cluster`, with the pole `0` included),
and `w̄^{B_ρ}_t` (`HarmonicBalls.leastSupersolution μ ρ 0 t`, eq:least-super-solution, line 501) is continuous on
`cl(B_ρ)`, has Laplacian `μ|_{Λ_t}` on `B_ρ` and vanishes on `∂B_ρ`. -/
def SatisfiesObstacleCharacterization (μ : Measure ℂ) (Λ : ℝ → Set ℂ) : Prop :=
  ∀ t r : ℝ, 0 < t → 0 < r → Λ t ⊆ ball 0 r → ∀ ρ : ℝ, r < ρ →
    Λ t = interior (closure (cluster μ ρ 0 t)) ∧
    ContinuousOn (leastSupersolution μ ρ 0 t) (closedBall 0 ρ) ∧
    HasLaplacian (leastSupersolution μ ρ 0 t) (μ.restrict (Λ t)) 0 (ball 0 ρ) ∧
    ∀ x ∈ sphere (0 : ℂ) ρ, leastSupersolution μ ρ 0 t x = 0

/-- `{Λ_t}_{t > 0}` is a family of harmonic balls for `μ` centred at `0` satisfying (a), (b), (c) of Theorem 2.3
(lines 509-527). -/
def IsConeHarmonicBallFamily (μ : Measure ℂ) (Λ : ℝ → Set ℂ) : Prop :=
  (∀ t : ℝ, 0 < t → IsHarmonicBall μ (Λ t) 0) ∧ SatisfiesHarmonicBallConditions μ Λ 0 ∧
    SatisfiesObstacleCharacterization μ Λ

/-- The time `T = sup {t > 0 : Λ_t ⊆ B_{ρ/3}}` (eq:cluster-stopping-time, line 1589). -/
noncomputable def clusterExitTime (Λ : ℝ → Set ℂ) (ρ : ℝ) : ℝ :=
  sSup {t : ℝ | 0 < t ∧ Λ t ⊆ ball 0 (ρ / 3)}

/-- `𝓜(D) = sup_{z ∈ D} ∫_D (log (1/|z - w|) + 1) dμ_h(w)` (eq:largest-exit-time-rv, line 884), in `[0, ∞]`
(the integrand is taken in `[0, ∞]` via its positive part, which is the integrand itself for `D ⊆ B_1`). -/
noncomputable def largestExitTimeRV (μ : Measure ℂ) (D : Set ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ D, ∫⁻ w in D, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ

/-- Condition (c) of Theorem 2.3 for a family indexed by `t ∈ (0, T)` (Lemma 2.4, line 535). -/
def SatisfiesObstacleCharacterizationOn (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (T : ℝ) : Prop :=
  ∀ t r : ℝ, t ∈ Ioo 0 T → 0 < r → Λ t ⊆ ball 0 r → ∀ ρ : ℝ, r < ρ →
    Λ t = interior (closure (cluster μ ρ 0 t)) ∧
    ContinuousOn (leastSupersolution μ ρ 0 t) (closedBall 0 ρ) ∧
    HasLaplacian (leastSupersolution μ ρ 0 t) (μ.restrict (Λ t)) 0 (ball 0 ρ) ∧
    ∀ x ∈ sphere (0 : ℂ) ρ, leastSupersolution μ ρ 0 t x = 0

/-- `{Λ_t}_{0 < t < T}` is a family of harmonic balls for `μ` centred at `0` satisfying the properties of Theorem 2.3
with `t` restricted to `(0, T)` (Lemma 2.4, line 535; `HarmonicBalls.SatisfiesHarmonicBallConditionsOn`). -/
def IsConeHarmonicBallFamilyOn (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (T : ℝ) : Prop :=
  (∀ t ∈ Ioo 0 T, IsHarmonicBall μ (Λ t) 0) ∧ SatisfiesHarmonicBallConditionsOn μ Λ 0 T ∧
    SatisfiesObstacleCharacterizationOn μ Λ T

/-- `T = sup {t > 0 : Λ_t ⊆ B_{1/2}}` for a family indexed by `(0, T)` (Lemma 2.4, line 536): every `Λ_t`, `t < T`, lies
in `B_{1/2}`, and for every `r < 1/2` some `Λ_t`, `t < T`, is not contained in `B_r` (so the family is not stopped
before it reaches `∂B_{1/2}`). -/
def IsStoppedAtHalfBall (Λ : ℝ → Set ℂ) (T : ℝ) : Prop :=
  (∀ t ∈ Ioo 0 T, Λ t ⊆ ball 0 (1 / 2)) ∧ ∀ r : ℝ, r < 1 / 2 → ∃ t ∈ Ioo 0 T, ¬ Λ t ⊆ ball 0 r

/-- A family of sets `{Λ_t}_{0 < t < T}` as a `Prop`-valued process `(t, x) ↦ (0 < t < T ∧ x ∈ Λ_t)` on `ℝ × ℂ`; its
law (product σ-algebra) is the law of the random family (Lemmas 2.5, 2.6). -/
def familyProcess (Λ : ℝ → Set ℂ) (T : ℝ) : ℝ × ℂ → Prop :=
  fun p => p.1 ∈ Ioo 0 T ∧ p.2 ∈ Λ p.1

/-- The rescaled family `t ↦ R⁻¹ Λ_{b t} = {x : R x ∈ Λ_{b t}}` (Lemma 2.5, line 551). -/
def rescaledFamily (Λ : ℝ → Set ℂ) (R b : ℝ) : ℝ → Set ℂ :=
  fun t => {x | (R : ℂ) * x ∈ Λ (b * t)}

/-- The field of the quantum cone and its LQG measure, without the curve: `P` is a probability, `(hC, hcirc)` is the
circle average embedding of the `γ`-quantum cone (Definition 2.1) and `μ = μ_h` its `γ`-LQG measure. The results of
Section 2 which do not involve `η` (Fact 2.2, Theorem 2.3, Lemmas 2.4-2.7, 2.17) are stated for such data. -/
def IsConeField {Ω : Type} [MeasurableSpace Ω] (γ : ℝ) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  IsProbabilityMeasure P ∧ IsQuantumCone γ P hC hcirc ∧ IsLQGMeasure P γ hcirc μ

/-- A family `{Λ_t}_{t > 0}` as a `Prop`-valued process `(t, x) ↦ (t > 0 ∧ x ∈ Λ_t)` on `ℝ × ℂ` (Lemma 2.6). -/
def globalFamilyProcess (Λ : ℝ → Set ℂ) : ℝ × ℂ → Prop :=
  fun p => 0 < p.1 ∧ p.2 ∈ Λ p.1

/-- The measure `μ^ε_h` whose restriction to each cell `H^ε_a` is `deg^ε(a) μ_h|_{H^ε_a}` (Lemma 2.10, line 699), for
the map with edge multiplicity `m` (`MatedCRTEnv.mult S ε ω`) and the cells of `η`. -/
noncomputable def degreeWeightedMeasure (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (μ : Measure ℂ) : Measure ℂ :=
  Measure.sum fun k : ℤ => ((matedDeg m k : ℕ) : ℝ≥0∞) • μ.restrict (cell ε η k)

/-- The good annulus event `E_r(z) = E_r(z; C)` (eq:good-annulus-event, line 2314, as corrected) for the measure
`μ = μ_h` and the constant `c₀ = 𝐜₀ ∈ (0, 1/5)` of eq:choice-of-constant-annulus:
`sup_{v ∈ 𝔸_{r,2r}(z)} ∫_{𝔸_{r,2r}(z)} (log (r/|u - v|) + 1) dμ(u) ≤ C min_{w ∈ 𝔸_{r,2r}(z)} μ(B_{c₀ r}(w))`
(the minimum is an infimum; the integrand is taken through its positive part in `[0, ∞]`, which only enlarges the
left side: the event is contained in the event with the signed integrand).
CORRECTION [C5] (provisional; ESCALATIONS E-A10, review-C "NEW"): the printed integrand `log (1/|u - v|) + 1` is not
scale invariant and makes the event a.s. empty for `r < e^{1-C}/4` (`|u - v| < 4r` on the annulus while
`B_{c₀ r}(w₀) ⊆ 𝔸_{r,2r}(z)`), so Lemmas 6.4-6.5 are false as printed; the scale-invariant `log (r/|u - v|) + 1` makes
the step "the probability of `E_r(z)` does not depend on `r` or `z`" (line 2367) true. -/
def IsGoodAnnulusEvent (μ : Measure ℂ) (c₀ C r : ℝ) (z : ℂ) : Prop :=
  (⨆ v ∈ annulus z r (2 * r), ∫⁻ u in annulus z r (2 * r), ENNReal.ofReal (Real.log (r / ‖u - v‖) + 1) ∂μ) ≤
    ENNReal.ofReal C * ⨅ w ∈ annulus z r (2 * r), μ (ball w (c₀ * r))

/-- The σ-algebra generated by `h|_U` viewed modulo additive constant: by the pairings `(h, φ)` with test functions `φ`
supported in `U` with `∫ φ = 0` (Lemma 6.6, line 2372). -/
@[instance_reducible]
noncomputable def modConstSigma {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) : MeasurableSpace Ω :=
  ⨆ (φ : ℂ → ℝ) (_ : IsTestFunction U φ ∧ ∫ x, φ x = 0), MeasurableSpace.comap (fun ω => hC ω φ) inferInstance

end MatedCRT
