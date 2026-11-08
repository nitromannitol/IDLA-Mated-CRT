# Written-proof requests at lead takeover (2026-11-08 08:23 UTC)

Status: historical exact-type requests with per-target updates below. Six now have **WRITTEN-PROOF-AVAILABLE / LEAN-PENDING** after the operator16:25 ruling; three original targets and three newer scaling requests remain **WRITTEN-PROOF-NEEDED**. These are exact open proof obligations carried as named Step Props under the operator's standing rule. They are not proved results or approved literature inputs. The operator routes them to a separate prover and independent audit; active workers continue with explicit hypotheses. No statement or definition is changed by this ledger.

The code blocks copy the entire current `def` command, including binders, from the indicated source. Names are fully qualified in headings; code uses the original namespace and open declarations of its source file. The declarations are pinned to the takeover commits (z1: 15e8866/f69cf7b; z5: d63273a; m1: 2afd11a), except the pre-existing S3 interface. Compile checks are recorded under `/home/nitro/paper-fleets/mcrt/lead/checks/20261108-takeover`.

The three rescaled-environment requests remain in [EnvironmentScaling.md](EnvironmentScaling.md). The operator supplied independently audited written proofs at09:45; see [ENV-STEPS-ROUTING-20261108.md](ENV-STEPS-ROUTING-20261108.md) for their WRITTEN-PROOF-AVAILABLE / LEAN-PENDING status and the repaired stopped-clock quantifiers. [GAPS-SEC3.md](GAPS-SEC3.md) and fleet `ESCALATIONS.md` retain the prior evidence. The requested `docs/campaign/STATUS.md` is absent; the existing fleet `STATUS.md` and [REDUCTIONS.md](REDUCTIONS.md) remain the status/reduction ledgers.

Operator update read 2026-11-08 14:24 UTC (inbox entry labelled 14:40): the nine remaining requests WPN-36 x3, WPN-42-locality and WPN-51 x5 were sent to a separate prover at14:20, one target at a time. They remain **WRITTEN-PROOF-NEEDED**, carried as named Step hypotheses until each independently audited proof returns. Active workers are not assigned their proofs. m6 and z2 are now paused; historical ownership references below do not authorize new work for them.


## Independently audited return, operator 2026-11-08 16:25

Pinned source: fleet `notes/wpn-steps2/steps2.tex`, sha256
`8ec75074beeb628d998a25dcc2a7a86b2a0b59a832899f7c78dd42a9ede27793`;
independent audit `notes/wpn-steps2/AUDIT-steps2.md`. Overall verdict GAPS
is per-target: four exact declarations are correct, two false declarations
have sufficient audited repairs, and rates/pole/layer remain unreturned.
These are written proofs, not new Lean closure or approved literature axioms.

| Request | Written status and exact source section | Lean routing |
| --- | --- | --- |
| WPN-36-uniform-cell | AVAILABLE, exact declaration correct, lines33-250 | m5 uniform-cell, first geometric/quantitative component |
| WPN-36-pointwise-event | AVAILABLE REPAIR, original pointwise Step false, lines252-438; replace its inclusion by a.e. implication at each mesh and choose admissible parameters from the actual estimates | m5 successor, repaired Step and existing a.e. tail/mean consumers |
| WPN-36-pointwise-rates | WRITTEN-PROOF-NEEDED, lines440-649: G1 missing Brownian minimum uniqueness/strict adjacency and G2 early interpolation exit case | no proof task; keep named Step |
| WPN-42-locality | AVAILABLE, exact declaration correct, lines651-794 | z5 local-measure functional; same map for both models |
| WPN-51-origin | AVAILABLE, exact declaration correct, lines796-1009 | z5 successor, obstacle code and completion measurability |
| WPN-51-pole | WRITTEN-PROOF-NEEDED, lines1011-1507 excluded from successful audit | no proof task; keep named Step |
| WPN-51-geometry | AVAILABLE, exact declaration correct, lines1509-1658 | z1 stopped geometry, regular-open compact core first |
| WPN-51-margin | AVAILABLE REPAIR, raw exact measurability false, lines1660-1858; use an envSigma-measurable version agreeing a.s. on the stopping event | z1 successor; repair cinf/cpos/Good consumer as authorized |
| WPN-51-layer | WRITTEN-PROOF-NEEDED, lines1860 onward inherit G1 | no proof task; keep named Step |

The operator explicitly authorizes the two internal Step restatements and
consumer adjustments. Frozen Draft statements remain untouched. The code
blocks below preserve the historical declarations whose problems were sent
for written proofs; the two false forms are not proof tasks or justified
hypotheses for an unconditional conclusion. Remaining newer requests
WPN-42-scaled-representatives, WPN-42-insertion-coordinate-extension and
WPN-ENV-dilated-circle-common-event are unchanged.

## WPN-51-origin: `MatedCRT.ConeOriginNullMeasurableStep`

**WRITTEN-PROOF-AVAILABLE / LEAN-PENDING (16:25).** Exact declaration audited CORRECT, steps2:796-1009; routed to z5. Historical request: Section 5 stopped lower bound, E-c1-5(b). The continuity-from-above consequence is proved; the exact null-measurability interface has no supplied written proof. Worker z1 report, 15e8866.

Exact declaration: `MatedCRT/Proofs/Sec5/StoppedExterior.lean:374`.

```lean
def ConeOriginNullMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → NullMeasurableSet {ω | ¬ ball (0 : ℂ) s ⊆ Λ ω t} S.P
```

## WPN-51-pole: `MatedCRT.StoppedInterior.StoppedSurplusPoleStep`

**WRITTEN-PROOF-NEEDED.** Section 5 stopped lower bound, E-c1-5(c). The annulus convergence does not treat the discrete surplus near the pole. Worker z1 report, f69cf7b.

Exact declaration: `MatedCRT/Proofs/Sec5/StoppedInterior.lean:136`.

```lean
def StoppedSurplusPoleStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t : ℝ, 0 < δ → δ < ρ → 0 < t →
    ∃ s : ℝ, 0 < s ∧ ∃ c : Ω → ℝ, Measurable[S.envSigma] c ∧ (∀ ω, 0 < c ω) ∧
      TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
        ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
          δ < infDist (vertexPoint ε (S.η ω) a)
            (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
          ‖vertexPoint ε (S.η ω) a‖ < s →
          c ω / ε ≤ matedLeastSupersolution (S.mult ε ω) ε (S.η ω) ρ t a +
            t / ε * greenKernel (S.mult ε ω) (ballInterior ε (S.η ω) ρ) 0 a}
```

## WPN-51-geometry: `MatedCRT.StoppedInterior.StoppedInteriorGeometryStep`

**WRITTEN-PROOF-AVAILABLE / LEAN-PENDING (16:25).** Exact declaration audited CORRECT, steps2:1509-1658; routed to z1. Historical request: Section 5 stopped lower bound, E-c1-5(d). The exact discrete-interior to continuum-interior assertion has no supplied written proof; the heuristic in the Lean docstring is not a completed argument. Worker z1 report, f69cf7b.

Exact declaration: `MatedCRT/Proofs/Sec5/StoppedInterior.lean:155`.

```lean
def StoppedInteriorGeometryStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ t r : ℝ, 0 < δ → 0 < t → 0 < r →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        δ < infDist (vertexPoint ε (S.η ω) a)
          (frontier (fillCells ε (S.η ω) (cellVertices ε (S.η ω) (Λ ω t)))) →
        ∀ x ∈ cell ε (S.η ω) a, δ / 2 ≤ infDist x (Λ ω t)ᶜ ∧ dist x (vertexPoint ε (S.η ω) a) < r}
```

## WPN-51-margin: `MatedCRT.StoppedInterior.StoppedInteriorMeasurableStep`

**WRITTEN-PROOF-AVAILABLE REPAIR / LEAN-PENDING (16:25).** Original raw declaration false; measurable-version repair audited, steps2:1660-1858; operator-authorized consumer repair routed to z1. Historical request: Section 5 stopped lower bound, E-c1-5(e). Measurability in envSigma of this random compact-set infimum remains open. Worker z1 report, f69cf7b.

Exact declaration: `MatedCRT/Proofs/Sec5/StoppedInterior.lean:171`.

```lean
def StoppedInteriorMeasurableStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ s t : ℝ, 0 < δ → 0 < s → 0 < t →
    Measurable[S.envSigma] fun ω => ⨅ x : {x : ℂ | x ∈ Λ ω t ∧ s ≤ ‖x‖ ∧ δ ≤ infDist x (Λ ω t)ᶜ},
      (HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t (x : ℂ) +
        t * HarmonicBalls.greenFunction (ball 0 ρ) 0 (x : ℂ))
```

## WPN-51-layer: `MatedCRT.StoppedLayerPotentialStep`

**WRITTEN-PROOF-NEEDED.** Section 5 stopped lower bound, E-c1-5, S3. Lemma 3.4 is pointwise in the base vertex; this uniform layer-potential estimate and the random test-function measurability are not supplied by it. The exact type below, including its finite sum and kernel convention, is the request. Worker z1 report.

Exact declaration: `MatedCRT/Proofs/Sec5/StoppedSurplusSteps.lean:68`.

```lean
def StoppedLayerPotentialStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ κ : ℝ, 0 < κ →
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} fun ε => {ω |
      ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t),
        ∑ᶠ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
          greenKernel (S.mult ε ω) (cellVertices ε (S.η ω) (Λ ω t)) a b ≤ κ / ε}
```

## WPN-42-locality: `MatedCRT.LQGMeasureLocalityFunctionalStep`

**WRITTEN-PROOF-AVAILABLE / LEAN-PENDING (16:25).** Exact declaration audited CORRECT, steps2:651-794; routed to z5. Historical request: Proposition 4.2 restricted-law transfer, input (A), operator ruling 2026-11-08 06:45. The IDLA Fact 2.2(ii) at corrected TeX 478-480 motivates locality. A single measurable functional serving both models is stronger than separate existence of field-measurable versions. No written derivation of this exact interface is supplied. Retain as a named Step, never as an admitted literature statement.

Exact declaration: `MatedCRT/Proofs/Sec4/Prop42Closure/LQGMeasureFunctional.lean:42`.

```lean
def LQGMeasureLocalityFunctionalStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ U : Set ℂ, IsOpen U → U ⊆ ball (0 : ℂ) 1 →
    ∃ Λ : ((TestB1 → ℝ) × (CircleB1 → ℝ)) → ℝ≥0∞, Measurable Λ ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
          (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
          IsConeField γ P hC hcirc μ → ∀ᵐ ω ∂P, μ ω U = Λ (coneFieldOnB1 hC hcirc ω)) ∧
      (∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
          (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ' : Ω' → Measure ℂ),
          IsProbabilityMeasure P' → IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureOfField P' γ γ hcirc' μ' →
            ∀ᵐ ω' ∂P', μ' ω' U = Λ (wholePlaneFieldOnB1 γ hC' hcirc' ω'))
```

## WPN-34-clock: `MatedCRT.DirichletStoppedClockConvergenceStep`

**UPDATE 2026-11-08 09:45 UTC: WRITTEN-PROOF-AVAILABLE / REPAIRED CONSTRUCTOR LEAN-PENDING.**
Operator-supplied `notes/env-steps/env-steps.tex` is independently audited
CORRECT. Proposition false (1071-1095) refutes discharging the predicate for
arbitrary supplied `G` (`G = 1` fails at time zero); the conditional consumer
itself is not refuted. Proposition correctstopped (1106-1252) constructs a
jointly measurable continuous-path-valued `G` for `0 ≤ γ < 2`, bounded simply
connected field domain and the remaining consumer hypotheses. It supplies the
exact existing source predicate and identifies `G` with stopped `F` in the
stated iterated-a.e. order. The exact elaboration-checked constructor type and
routing to z2 are in [the routing note](ENV-STEPS-ROUTING-20261108.md).
The original predicate below remains unchanged; its arbitrary-parameter
universal discharge is not a valid replacement goal. Occupation and the cone
start-at-zero Green lemma remain separate.

Historical request as originally recorded:

**WRITTEN-PROOF-NEEDED.** Previously flagged by the operator. This is the former hsource in DirichletClockTransfer.lean:86-90, now named at commit 2afd11a. Corrected paper occupation discussion 1168-1172 does not state this exact all-time a.s. convergence and continuity. See GAPS-SEC3.md and the audited occupation proof for related supported bridges; do not equate path convergence with this statement.

Exact declaration: `MatedCRT/Steps/Sec3/DirichletStoppedClock.lean:15`.

```lean
def DirichletStoppedClockConvergenceStep {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (x : ℂ) (G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ) : Prop :=
  ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
    let K : ℕ → ℝ≥0 → ℝ := fun n =>
      killedGMCClockApprox U γ (hcirc q.1) (dyadicScale n) q.2
    (∀ t : ℝ≥0, Tendsto (fun n => K n t) atTop (𝓝 (G q.1 q.2 t))) ∧
    Continuous (G q.1 q.2)
```

## WPN-36-uniform-cell: `MatedCRT.UniformCellSizeUpperStep`

**WRITTEN-PROOF-AVAILABLE / LEAN-PENDING (16:25).** Exact declaration audited CORRECT, steps2:33-250; routed to m5. Historical request: Lemma 2.8, corrected TeX 669-674, cites BG20 Lemma 2.4; polynomial probability is defined at 387-388. The paper does not explicitly quantify over representations or state exponent dependence on them. This request is the exact representation-uniform exponent bridge, not a claim that the source asserts representation dependence. Worker m1 r3, 2afd11a.

Exact declaration: `MatedCRT/Steps/Sec3/UniformCellSize.lean:14`.

```lean
def UniformCellSizeUpperStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ 2 →
  ∃ κ : ℝ, 0 < κ ∧ ∀ (Ω : Type) [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      S.P {ω | ¬ ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
        diam (cell ε (S.η ω) i) ≤ ε ^ a} ≤ ENNReal.ofReal (C * ε ^ κ)
```

## WPN-36-pointwise-event: `MatedCRT.PointwiseCellAnnulusEnvelopeStep`

**WRITTEN-PROOF-AVAILABLE REPAIR / LEAN-PENDING (16:25).** Original pointwise declaration false; per-mesh a.e. repair audited, steps2:252-438; authorized Step/consumer repair routed to m5. Historical request: Corrected same-walk rate: a pointwise envSigma-measurable geometric envelope with a polynomial exceptional bound. An outer-probability bound and versions agreeing a.e. at each mesh do not by themselves give this interface. Worker m1 r3, 2afd11a.

Exact declaration: `MatedCRT/Steps/Sec3/PointwiseAnnulusEnvelope.lean:16`.

```lean
def PointwiseCellAnnulusEnvelopeStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ a β p κ : ℝ) : Prop :=
  ∃ E : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (E ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ) ∧
      ∀ ω ∈ E ε,
        (∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty →
          diam (cell ε (S.η ω) i) ≤ ε ^ a) ∧
        (∀ z ∈ ball (0 : ℂ) ρ, ∀ s : ℝ, ε ^ β ≤ s → s ≤ ρ →
          ball z (2 * s) ⊆ ball 0 ρ → ∀ j ∈ cellVertices ε (S.η ω) (ball z s),
          ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) j
            {path | ∀ y ∈ cellVertices ε (S.η ω) (sphere z (s / 2)),
              walkDisconnectsBeforeHit (S.mult ε ω)
                (cellVertices ε (S.η ω) (sphere z (2 * s))) y path})
```

## WPN-36-pointwise-rates: `MatedCRT.PointwiseSameWalkRatesStep`

**WRITTEN-PROOF-NEEDED.** Corrected same-walk rate: the existing mean and tail estimates hold a.e. on the chosen event. They do not establish these estimates for every member of that event, simultaneously in the displayed parameters. Worker m1 r3, 2afd11a.

Exact declaration: `MatedCRT/Steps/Sec3/PointwiseSameWalkRates.lean:13`.

```lean
def PointwiseSameWalkRatesStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (E : ℝ → Set Ω) (ρ a β ν : ℝ) : Prop :=
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0), 0 < χ → χ ≤ 1 →
    HolderOnWith H χ ψ (closedBall z r) →
  ∀ q : ℝ, 0 < q → q < min a β * (χ : ℝ) →
  ∀ y ∈ ball z r, ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ ω ∈ E ε,
      ∀ v ∈ interiorCellVertices ε (S.η ω) (ball z r),
        (srwLaw (S.mult ε ω) v)
          {x | (1 + (H : ℝ)) * ε ^ q < sameWalkExitDiscrepancy S r z ψ ε ω x} ≤
            ENNReal.ofReal (C * ε ^ (ν * (min a β - q / χ))) ∧
        (∫ x, sameWalkExitDiscrepancy S r z ψ ε ω x ∂srwLaw (S.mult ε ω) v) ≤
          C * (H : ℝ) *
            (if (χ : ℝ) < ν then ε ^ (min a β * χ)
             else if (χ : ℝ) = ν then ε ^ (min a β * ν) * (1 + |Real.log ε|)
             else ε ^ (min a β * ν))
```

## Consumption boundary: uniform same-walk assembly

This interface collects the uniform joint choice of exponents, event and rate estimates; it is not an independent replacement for the preceding written-proof requests. `correctedHarmonicSameWalkRate_of_assembly` proves the frozen rate only conditional on it. Its component `AnnealedSameWalkRateStep` is defined immediately above it in the same source file. No closure of Lemma 3.6 is claimed from this wrapper.

```lean
def UniformSameWalkAssemblyStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ν : ℝ, 0 < ν ∧
  ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ (2 : ℕ) → ∃ κ : ℝ, 0 < κ ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ E : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
    (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (E ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ)) ∧
    AnnealedSameWalkRateStep S ρ a β ν κ ∧ PointwiseSameWalkRatesStep S E ρ a β ν
```

## Written arguments already available

`TruncatedDetFixedTimeStep` is implementation debt with a written route in [PROOF-REPAIRS-G.md](PROOF-REPAIRS-G.md), G4, item 1. It is **not** a new request for a written proof. z2 is assigned the deterministic killed-occupation/path-continuity substep, with BrownianOutwardExcursionAtExitStep still explicit until y2 resumes. The audited IR-m2-1 occupation proof is in fleet `audits/occ-astra`; its coefficient for the unscaled clock is 2.

The deterministic earlier-rational-time compact cover and the stopped-to-global obstacle comparison are written in [GAPS-SEC2567A.md](GAPS-SEC2567A.md), E-c1-5; z1 is assigned only these conditional consequences. Strict growth is not proved by this route. The plateau-scaling argument is written in fleet `notes/prop42-proof/prop42-proof.tex:230-268`; z5 is assigned its deterministic part, then its law-transfer bridge with cited inputs explicit. m6 retains the current strict-obstacle-gap task.

## WPN-42-scaled-representatives: `MatedCRT.ScaledBoundedRepresentativesStep`

**WRITTEN-PROOF-NEEDED** (lead 2026-11-08 15:29 UTC; z5 report, commit dee04d9).
This new request is additional to the nine sent to the prover at14:20. Its truth
for arbitrary measures has not been established. Do not assign its proof to an
active Lean worker or silently restrict its quantifiers.

Exact declaration: `MatedCRT/Proofs/Sec4/Prop42Closure/ScaledRegularizedFamily.lean:43`,
namespace `MatedCRT`, with `open MeasureTheory HarmonicBalls`:

```lean
def ScaledBoundedRepresentativesStep : Prop :=
  ∀ (μ : Measure ℂ) (Λ : Set ℂ) (a c : ℝ), 0 < a → 0 < c → IsSubharmonicBall μ Λ 0 →
    HasBoundedSubharmonicRepresentatives (scaledMeasure μ a c) ((fun x : ℂ => (a : ℂ) * x) ⁻¹' Λ) 0
```

The referenced predicate is defined in the read-only companion at
`HarmonicBalls/Audit/GreenSubharmonicTestClass.lean:48`:

```lean
def HasBoundedSubharmonicRepresentatives (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ) : Prop :=
  ∀ f ∈ subharmonicBallTestClass Λ z, ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
    f z = g z ∧ f =ᵐ[μ.restrict Λ] g
```

Evidence: audited fleet `notes/prop42-proof/prop42-proof.tex:252-256` says to
scale the mean-value property, mass and family conditions. The current frozen
test class (`HarmonicBalls/Draft/Section4.lean:65`) permits unbounded witness
domains. Available `HarmonicBalls.Section6.greenFunction_dilation` requires a
bounded domain (`Proofs/Sec6/GreenDilation.lean:164`); the companion audit
explicitly leaves bounded representatives open at1-6. HB Lemma5.7's cluster
identity (corrected source905-938) does not supply this test-class replacement.
`Proofs/Potential/BoundedSubharmonicRepresentatives.lean:140,160,246` supplies a
pointwise criterion and conditional special cases, not the stated assertion.
This is a missing written bridge at the current definitions; no counterexample
to the paper theorem is asserted. An audited proof or operator-approved statement
repair is needed before the full all-measure Step can be discharged.

Lead checked committed snapshots at936f3b8 with strict lc and a clean hole scan.
z5 proves mass/conditions, regularized-cluster dilation and bounded-test transfer;
`scaledRegularizedFamilyStep_of_representatives` still assumes this Step. Hence
`ScaledRegularizedFamilyStep`, the plateau-scaling conclusion and Proposition4.2
are not closed. The Step is not a literature input eligible for External promotion.

## WPN-42-insertion-coordinate-extension: `MatedCRT.Proposed.DS11CoordinateRuleFixedAffine`

**WRITTEN-PROOF-NEEDED** (lead2026-11-08 15:33 UTC, z5 9e51e0c). This is an
open repository extension, despite its current Proposed location and name, not
a faithful printed DS11 hypothesis. Additional to the nine sent at14:20.
The exact current declaration is copied below (namespace `MatedCRT.Proposed`,
`open MeasureTheory HarmonicBalls`):

```lean
def DS11CoordinateRuleFixedAffine : Prop :=
  ∀ (γ α : ℝ), 0 < γ → γ < 2 → α < lqgQ γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsProbabilityMeasure P → IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α hcirc μ →
  ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ, ∀ᵐ ω ∂P,
    IsLQGLimit γ (fun ε z => fieldCircleAverage α (hcirc ω) (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖)
      ((μ ω).map fun x => (x - b) / a)
```

Source boundary: DS arXiv0808.1560v2 Proposition2.1 p13 treats a GFF on a domain;
Prop1.1 p4 constructs the zero-boundary measure along powers of two and extends
to deterministic continuous additions. Neither quoted statement directly gives
the whole-plane insertion at its singular point or the required arbitrary
non-dyadic dilation. The paper's fact:lqg-measure IV and audited prop42 proof245-256
invoke a general coordinate rule without supplying these extensions. Existing
IR-c4-3 already records the non-dyadic issue. Sheffield-Wang Thm1.4's exact scope
must be checked before it is used; cone localization remains m5's separate task.

`insertionLQGScalingLawStep_of_coordinateRule` proves K only conditional on this
entire extension. The source-ready bounded-domain theorem and any carrier bridge
are assigned to z5's queued source-scope slice; the unwritten extension itself
is not assigned for invention. Request an independently audited written proof
or a faithful source that actually covers this exact type before promoting it.
Do not combine this gap with the independent scaled-representative gap.

## WPN-ENV-dilated-circle-common-event: `ConeDilationCircleApproximationStep`

**WRITTEN-PROOF-NEEDED** (lead2026-11-08, m1 7df13f4). Exact sufficient
internal common-event interface in FieldCircleScaling.lean:45, namespace
MatedCRT.Sec1, with MeasureTheory/Filter/Set and LQGMetric.CircleAvg open:

```lean
def ConeDilationCircleApproximationStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsQuantumCone γ P hC hcirc →
      ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ n m : ℕ, ∀ k a d : ℤ, 0 < k →
        Tendsto (fun j => hC ω (affTest R 0
          (circBump j (FieldCircle.gridPt m a d) ((k : ℝ) / 2 ^ n)))) atTop
          (𝓝 (hcirc ω (R * ((k : ℝ) / 2 ^ n)) (R * FieldCircle.gridPt m a d)))
```

Written boundary: audited fleet env-steps.tex:325-330 asserts identification
of the rescaled distribution's continuous circles with the scaled supplied
circles; it does not write this uniform affine-mollifier approximation passage
at the current Lean definitions. ConePairing.lean:286 and Bonanno
CircleAvgAffine.lean:196 supply fixed-parameter results whose exceptional sets
may depend on radius/center/scale; they do not directly supply the event above.
The deterministic pairing identity, constant-shift recovery and conditional
consumer are proved by m1. Do not ask a worker to invent this passage.

This all-positive-scale interface is sufficient for the actual random-scale
RescaledConeDistributionCircleGridStep, and may be stronger than necessary.
The separate prover and independent audit should check its exact hypotheses
and strength; alternatively supply an audited proof of the existing exact grid
Step at Field.lean:1146. No assertion of falsity or necessity of this stronger
interface is made. Keep it named until the operator returns an audited proof.
