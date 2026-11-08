# Written-proof requests at lead takeover (2026-11-08 08:23 UTC)

Status: historical exact-type requests with dated updates below. All nine original requests have audited written outcomes (operator16:25/18:25/18:45); all three newer scaling requests now also have audited written outcomes (operator19:35, steps3 sha d34cf930). False originals retain their exact historical types and require the authorized repairs. Lean implementation remains pending. No further prover round will occur: any genuinely unwritten step remains a named Step with exact type, location, consumer and reason. Literature inputs remain explicit and source promotion is separate.

The historical code blocks copy the entire original `def` command, including binders, from the indicated source; operator-authorized repairs and current interfaces are recorded in the dated updates. Names are fully qualified in headings; code uses the original namespace and open declarations of its source file. The declarations are pinned to the takeover commits (z1: 15e8866/f69cf7b; z5: d63273a; m1: 2afd11a), except the pre-existing S3 interface. Compile checks are recorded under `/home/nitro/paper-fleets/mcrt/lead/checks/20261108-takeover`.

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
| WPN-36-uniform-cell | AVAILABLE, exact declaration correct, r3 Section1:36-254 | m5 deterministic cell/area and outer-union-bound components checked; uniform quantitative law remains |
| WPN-36-pointwise-event | AVAILABLE REPAIR, original pointwise Step false, r3 Section2:255-442 | m5 e197e53 a.e. Step and tail/mean consumers checked; actual Borel state/walk construction remains |
| WPN-36-pointwise-rates | AVAILABLE REPAIR, r3 Section3:443-766; per-mesh a.e. quenched implication, chosen annulus exponent | z1 c5305cb/ce894f6 a.e. successors/assembly, start-cell geometry and cell-target composition checked; uniform-cell/minimum/adjacency/early-exit producers remain; frozen Draft delta escalated |
| WPN-42-locality | AVAILABLE, exact declaration correct, r3 Section4:768-911 | z5 48b2c75 exact internal Step and e8620f7 consumers checked; no Prop4.2 closure |
| WPN-51-origin | AVAILABLE, exact declaration correct, r3 Section5:913-1126 | ebc8497 conditional code reduction and 77d5e80/ce347eb Borel supersolution matrix checked; countable tests and actual section identity remain |
| WPN-51-pole | AVAILABLE, exact standalone declaration CORRECT, operator18:45; r3 Section6:1128-3090, no added convergence antecedent | finite-domain comparison and canonical published-input staging split into bounded z5 tasks; shared Brownian minimum assigned to z1; full Lean proof pending |
| WPN-51-geometry | AVAILABLE, exact declaration correct, r3 Section7:3092-3241 | 62cfddb Borel obstruction and null-measurability/continuity-from-above checked; actual measurable compact K and uniform cell estimates remain |
| WPN-51-margin | AVAILABLE REPAIR, raw exact measurability false, r3 Section8:3243-3441; use envSigma-measurable version agreeing a.s. on stopping event | repaired cinf/cpos/Good consumer and dense continuous decoder checked; StoppedMarginCodeStep remains |
| WPN-51-layer | AVAILABLE, exact six-antecedent target, r3 Section9:3443-3819 | z5 2c5f819 finite Green domination and r/n/mesh outer-probability components checked; cutoff/core/Harnack/fixed-center producers and exact Step assembly remain |

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

**WRITTEN-PROOF-AVAILABLE / LEAN-PENDING (operator18:45).** r3 Section6:1128-3090, audit CORRECT, exact standalone declaration without an added convergence antecedent. Historical request: Section 5 stopped lower bound, E-c1-5(c). The annulus convergence does not treat the discrete surplus near the pole. Worker z1 report, f69cf7b.

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

**WRITTEN-PROOF-AVAILABLE / LEAN-PENDING (operator18:25).** steps2-r2:3368-3744 and its independent re-audit target9 are CORRECT; exact declaration retained. Historical request: Section 5 stopped lower bound, E-c1-5, S3. Lemma 3.4 is pointwise in the base vertex; this uniform layer-potential estimate and the random test-function measurability are not supplied by it. The exact type below, including its finite sum and kernel convention, is the request. Worker z1 report.

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

**WRITTEN-PROOF-AVAILABLE REPAIR / LEAN-PENDING (operator18:25).** steps2-r2:443-766 and its independent re-audit target3 are CORRECT. The original pointwise type below is false; use the per-mesh a.e. successor with the chosen geometric event/exponents. See [the exact proposed delta](SAMEWALK-RATE-AE-REPAIR-20261108.md); frozen Draft remains unchanged. Historical request: Corrected same-walk rate: the existing mean and tail estimates hold a.e. on the chosen event. They do not establish these estimates for every member of that event, simultaneously in the displayed parameters. Worker m1 r3, 2afd11a.

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

**WRITTEN-PROOF-AVAILABLE REPAIR / LEAN-PENDING (operator19:35).** steps3 Section1:33-403 refutes the original and proves the bounded-Lambda replacement, sufficient for both consumers; queued m5. Historical request follows.

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

**WRITTEN-PROOF-AVAILABLE / LEAN-PENDING (operator19:35).** steps3 Section2:405-712 proves the exact insertion extension; queued z1 internal component and relocation out of Proposed. Historical request follows.

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

**WRITTEN-PROOF-AVAILABLE REPRESENTED REPAIR / LEAN-PENDING (operator19:35).** steps3 Section3:714-1057 refutes the raw Step and proves RescaledConeDistributionCircleGridStep exactly; queued m1. Historical request follows.

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


## Checked implementation update, 2026-11-08 17:17 UTC

At pinned e197e53, the authorized PointwiseCellAnnulusEnvelopeStep a.e.
repair and both tail/mean consumers pass strict lc, together with
AnnulusEnvelopeProof's state-law sandwich, intersection tail, parameter
selection and conditional assembly. This does not yet construct the full
envelope. The exact remaining interface (namespace MatedCRT, MeasureTheory
and Set open) from AnnulusEnvelopeProof.lean:74 is:

```lean
def AnnulusGoodMeasurableVersionStep {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) (ρ β p : ℝ) : Prop :=
  ∀ ε : ℝ, ∃ E : Set Ω, MeasurableSet[S.envSigma] E ∧
    ∀ᵐ ω ∂S.P, (ω ∈ E ↔ ω ∈ AnnulusGoodEvent S ρ β p ε)
```

This is **WRITTEN-PROOF-AVAILABLE / IMPLEMENTATION-PENDING**, steps2:395-426:
countable state coding, jointly Borel walk event/kernel and coanalytic/Preston
transfer. m5's fresh walk-event task and state-decoder successor are queued.
UniformCellSizeProof edbd4f0 supplies deterministic ball-mass-to-cell geometry,
area reparametrization and an outer-measure union bound. Representation-uniform
exponents and probability inputs remain; UniformCellSizeUpperStep is unproved.
The newly staged BG20 Lemma2.4 and Remark1.3 inputs retain canonical scope,
not arbitrary raw-model or representation-uniform laws.

z1 af34670 supplies regular-open compact-core, small-cell geometry, decreasing
obstructions and a conditional outer-probability passage; the full stopped
geometry Step still needs its measurable compact code, actual family clauses
and cell-size probability. These are written implementation work, not new
WPN. The margin repair task has promoted and its Preston transfer successor
is queued. The latter first corrects the omitted exact-measurability condition
in the Proposed Preston staging; compilation is not source approval. See
fleet ESCALATIONS E-PRESTON-EXACT-MEASURABILITY-STAGING. Original rates, pole,
layer and the three newer scaling WPN are unchanged. No numbered closure.


Late checked return17:18: z5 48b2c75 implements the exact existing
LQGMeasureLocalityFunctionalStep in LQGMeasureLocalityProof.lean:637. The
restricted-circle functional is selected before either environment; its
deterministic cutoff/approximation limit equals the measure of U for both
models, using their existing dyadic-limit/continuous-circle predicates.
Strict lc, three exported axiom probes and the hole scan pass; only standard
axioms occur. This is a checked internal Step implementation, not a
numbered-theorem closure or independent frozen-statement source audit.
Origin is next and an IG uniform-shift successor is staged with refill.


## Checked margin/origin coding update (2026-11-08 17:47 UTC)

Commits33b60f5/4c3f60e implement the authorized envSigma-measurable margin version, agreement almost surely on `{t < T}`, and the cinf/cpos/Good consumer repair. The Borel erosion minimum and its exact identity with the raw margin are proved on nonempty compact sets times continuous functions. `stoppedInteriorMeasurable_of_code` retains the following exact residual, copied from StoppedInterior.lean:193-205 in namespace MatedCRT.StoppedInterior. This is **WRITTEN-PROOF-AVAILABLE / LEAN-PENDING**, steps2:1747-1805, not a new written-proof request.

```lean
def StoppedMarginCodeStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ δ s t : ℝ, 0 < δ → 0 < s → 0 < t →
    ∃ (K : Ω → TopologicalSpace.NonemptyCompacts ℂ) (f : Ω → C(↥(marginDomain s (ρ / 2)), ℝ)),
      @Measurable Ω (TopologicalSpace.NonemptyCompacts ℂ × C(↥(marginDomain s (ρ / 2)), ℝ)) S.envSigma (borel _)
        (fun ω => (K ω, f ω)) ∧
      ∀ᵐ ω ∂S.P, t < clusterExitTime (Λ ω) ρ →
        (K ω : Set ℂ) = closure (Λ ω t) ∧
        ∀ x : ↥(marginDomain s (ρ / 2)), f ω x =
          HarmonicBalls.leastSupersolution (S.μ ω) ρ 0 t x.1 +
            t * HarmonicBalls.greenFunction (ball 0 ρ) 0 x.1
```

ebc8497 proves the circle-process Borel version, rational cluster inclusion code, universal-measurability pullback and conditional `ConeOriginNullMeasurableStep` reduction. It retains `PrestonAnalyticUniversallyMeasurableStmt` and this exact obstacle-code residual, copied from ConeOriginNullMeasurableProof.lean:464-470 in namespace MatedCRT.ConeOriginNull. The construction is written in steps2:838-955 and remains implementation work, not an unconditional Step proof.

```lean
def CodeSectionStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ c : Ω → PosCircleFns, Measurable c →
    (∀ᵐ ω ∂S.P, ∀ p : PosCircleIndex, c ω p = S.hcirc ω (p.1 : ℝ) p.2) →
    ∀ R : ℝ, 0 < R → ∀ t : ℝ, 0 < t →
      ∃ 𝒜 : Set (PosCircleFns × BallFns R), MeasurableSet 𝒜 ∧
        ∀ᵐ ω ∂S.P, ∀ w : BallFns R, (c ω, w) ∈ 𝒜 ↔ w ∈ superTraces (S.μ ω) R t
```

f4d04bc/3c0dcdf correct Proposed type B to countable generation, exact sigma-algebra comap equality and Borel range, with Preston Section2 p5, introduction p3/Section6 p35 and Theorem6.1(1) p35. The internal Polish analytic universal-measurability transfer is checked from the two explicit printed inputs, Cantor Theorem7.1 and Theorem6.1(1). The weak-definition defect is repaired; literature remains staged in Proposed pending operator source promotion. No External change or new WPN.

Receipts: fleet lead/checks/20261108-1740, eleven pinned source checks including both Assembly source consumers and four axiom probes, twelve standard-axiom exports; 74-source hole scan clean. Source checks do not claim an Assembly olean rebuild. z1 has margin continuous-decoder work queued, then the Borel geometry obstruction; z5 has IG uniform shift queued, then locality consumer integration. Numbered results remain open.

Late b834645 mass-code return: the Borel massLimit functional and its exact IsLQGLimit integral identity also pass strict source/axiom checks. This removes the scalar mass-limit measurability component, while the countable smooth test family, Borel supersolution relation and section identity remain in CodeSectionStmt. Final round receipts cover12 source snapshots,5 axiom probes/15 standard-axiom exports and74 hole-clean source hashes. No unconditional origin Step or numbered closure.


## Checked implementations and second audited release (lead round18:10)

33bdd99 proves the Borel dense-value decoder into the actual compact-domain continuous-function carrier, its recovery and a.e. recovery, including nonempty/empty margin-domain branches. This supplies the extension component of steps2:1784-1805; the Borel versions of actual surplus evaluations and random compact K still remain in StoppedMarginCodeStep. e02c3cd proves translation-mod-period invariance of uniform measure and joint independence with the entire other datum, plus its measurable functions. The normalized-GFF carrier/curve-law transfer remains in the mating proof. e8620f7 supplies the proved locality functional to the restricted-law, premature-contact-null and half-ball-closure consumers; their field/HB inputs remain explicit. No Prop4.2 or other numbered closure.

Pinned e8620f7 receipts in fleet lead/checks/20261108-1810:9 committed source checks,4 axiom probes/12 exports using only propext, Classical.choice and Quot.sound;79-source code-hole/axiom scan clean and19 paused-task hashes unchanged. This is implementation checking, not a new frozen-statement source approval.

The new inbox entry labelled18:25 releases targets3 and9 from notes/wpn-steps2/steps2-r2.tex, sha256 f52fd76aafd942d26dce5515140993cd0c55f392d965a9d9476d39aa2182a734, with AUDIT-steps2-r2.md targets3/9 CORRECT. Use r2:443-766 for the rate repair and r2:3368-3744 for the layer proof (the entry's3346 locator precedes its section header). Sections1,2,4,5,7,8 retain the earlier proof unchanged. The pole proof remains GAPS and is not assigned; newer scaling WPN remain. The release resolves the prior missing Brownian-minimum/strict-adjacency and early-exit written arguments; implementing them is now source-backed work, not a new WPN.

z1 has an a.e. rate-successor/assembly/outer-probability task queued after its current geometry task. Since the frozen corrected export remains pointwise in Draft/Section3HarmonicCorrected.lean:85, the worker stages exact repaired internal successors and preserves Draft; see E-SAMEWALK-RATE-AE-FROZEN-DELTA and the linked exact-type note. z5 has the layer-potential comparison and finite-center probability reduction queued after its current supersolution Borel matrix. Displaced compact-code and countable-test briefs are archived as bounded successors, not discarded. m1/m5 remain quota-stopped with their existing fresh queues supplied.


## Final audited return and checked components (lead round18:41)

The operator18:45 releases the pole target from `notes/wpn-steps2/steps2-r3.tex`, sha256 `88dfb1f9fb138cd038abe98d41650d7ef09834998833ebe13e3717a149582fae`, with `AUDIT-steps2-r3.md` CORRECT. This source supersedes both previous versions for **every target**. Section6 proves the exact standalone `StoppedInterior.StoppedSurplusPoleStep`: arbitrary valid model/sample space/raw family, deterministic s=rho, everywhere positive uncompleted-envSigma-measurable c, and all-positive-real-mesh outer-probability limit. It adds no convergence antecedent. The strict two-identification repair is r3:1264-1281; the canonical moment repair is2674-2753, using the printed normalized-mass moment paragraph preceding (4.25), not the malformed range or positive tail display. See [STOPPED-POLE-ROUTING-20261108.md](STOPPED-POLE-ROUTING-20261108.md) for bounded lemma and literature routes. All nine original requests now have written responses; this is not Lean closure.

c5305cb proves the exact internal per-mesh a.e. rate successors and conditional assembly, including the existing sectionwise outer-probability consumer and annealed transfer under `StartCellInteriorAe`. The rate producer, Brownian minimum/adjacency and early-exit implementations remain. The worker's suggestion that the cell-size event needs a new operator decision is unnecessary: the audited proof chooses the existential E from its cell-size/annulus envelope. Prove start-cell geometry for that actual chosen envelope and its a.s. proper curve, keeping the internal premise named until supplied; this does not change the frozen conclusion. The frozen pointwise-versus-a.e. delta remains separately escalated.

77d5e80/ce347eb supplies the measurable supersolution relation for an actual supplied countable test family, dense off-pole obstacle equivalence and the exact `superTraces` identity. `CountableC2FamilyStmt` and `LaplacianLESectionStmt` in SupersolutionBorelCode.lean:295-337 remain written implementation obligations, r3:1016-1043, together with simultaneous actual mass identities and local finiteness. They are not new WPN. 62cfddb supplies the Borel geometry obstruction, Preston pullback and continuity-from-above for a supplied measurable regular-closed compact K; constructing the actual random K is still required. 2c5f819 proves the finite normalized-Green domination and outer-probability reduction for the layer potential; it has not yet written all residual Step Props or assembled the exact six-antecedent target. No origin, geometry, layer or numbered closure follows from these components.

Receipts `lead/checks/20261108-1841`: nine pinned source-version checks and five axiom probes/18 exports pass, with only propext, Classical.choice and Quot.sound;84-source hole/axiom scan clean and19 paused-task hashes unchanged. Literature remains explicit and Proposed pending operator promotion. All four active next queues and bounded successors are supplied, with displaced compact/test briefs archived. m1/m5 quota stops remain respected. Operator18:45 confirms the three newer scaling WPN were sent to the prover at18:42 (mcrt c5305cb, hb d95497e); keep those hypotheses named and assign no worker to prove them.

Late ce894f6 is also checked: `startCellInteriorAe_of_cellSize` uses the actual IsValid area-parametrization and a.s. proper-curve facts, and `correctedHarmonicSameWalkRateAe_of_cellTarget` intersects events with polynomial exponent min(kappa,kappaCell). The exact uniform-cell residual is `CellSizeTargetAeStmt` at SameWalkAssemblyAe.lean:266; its exponent is fixed before the environment, whereas the existing `PolyHighProb` Draft allows an environment-dependent exponent. This is the already audited quantitative producer in r3 Section1:36-254, not missing written mathematics or a reason to stop the independent Brownian-minimum slice. Final receipts cover9 source-version checks,5 axiom probes/18 standard-axiom exports and84 hole-clean sources.


## Lead19:13: terminal written-proof policy and checked residual inventory

Operator18:55 ends future prover rounds after the three currently running requests. Formalize all audited written arguments already available. A genuinely WRITTEN-PROOF-NEEDED step with no audited return remains a named hypothesis, with exact type, file:line, consumer and reason here and in PROGRESS; do not ask workers to invent it. The three requests sent18:42 remain named pending independent audit. No new unwritten step was identified this round.

7e85827/ad84342 implement the three-regime layer-cake bounds for a distance variable and a Hölder discrepancy, with the factor H. They retain measurability, a.s. boundedness, scaled-tail and exponent hypotheses; the H>0 reduction does not discharge the H=0 branch of the full rate producer. 9bee835 proves stoppedLayerPotentialStep_of_layerSteps from four named residuals and MepsScalingInput. Strict checks and exported-axiom probes pass, but neither full rate nor layer producer is closed.

The four layer types below are **WRITTEN-PROOF-AVAILABLE / LEAN-PENDING**, not new WPN. Consumer: stoppedLayerPotentialStep_of_layerSteps at StoppedLayerPotentialReduction.lean:372, then StoppedLayerPotentialStep and stopped surplus/lower-bound reductions. Source is steps2-r3.tex, sha256 88dfb1f9fb138cd038abe98d41650d7ef09834998833ebe13e3717a149582fae, audited CORRECT. Core/cutoffs:3544-3661; logarithmic potential:3663-3690; Harnack:3710-3773; fixed-center/outer passage:3763-3819. Source correspondence of each producer's exact quantifiers still requires checking when it is implemented; successful conditional assembly is not that check. In particular retain the displayed everywhere-on-F versus a.e. distinctions and repair internally if the source requires versions rather than asserting a stronger producer.

Exact named residual `MatedCRT/Proofs/Sec5/StoppedLayerPotentialReduction.lean:173` (namespace MatedCRT):

```lean
def LayerCutoffCoreStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t →
  ∃ f : ℕ → Ω → ℂ → ℝ,
    (∀ n ω x, 0 ≤ f n ω x ∧ f n ω x ≤ 1) ∧
    (∀ n x, Measurable[S.envSigma] fun ω => f n ω x) ∧
    (∀ n ω, IsHolderContinuousOn (f n ω) (ball 0 ρ)) ∧
    (∀ ω ∈ {ω | t < clusterExitTime (Λ ω) ρ},
      ∀ᵐ x ∂(S.μ ω), Tendsto (fun n => f n ω x) atTop (𝓝 0)) ∧
    ∀ η : ℝ≥0∞, 0 < η → ∃ N : ℕ, ∀ n ≥ N, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
        {ω | ∃ b ∈ cellVertices ε (S.η ω) (Λ ω t) \ matedDiscreteCluster (S.mult ε ω) ε (S.η ω) ρ t,
          f n ω (vertexPoint ε (S.η ω) b) < 1 / 4}) < η
```

Exact named residual `MatedCRT/Proofs/Sec5/StoppedLayerPotentialReduction.lean:200` (namespace MatedCRT):

```lean
def LayerFiniteCenterHarnackStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r → r < ρ / 6 →
  ∃ (Y : Finset ℂ) (p : ℝ) (G : ℝ → Set Ω), 0 < p ∧ p ≤ 1 / 2 ∧ (∀ y ∈ Y, y ∈ ball (0 : ℂ) (ρ / 2)) ∧
    (∀ z ∈ closedBall (0 : ℂ) (2 * ρ / 5), ∃ y ∈ Y, dist z y < r / 4) ∧
    TendsToOneOn S.P {ω | t < clusterExitTime (Λ ω) ρ} G ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ω ∈ {ω | t < clusterExitTime (Λ ω) ρ} ∩ G ε,
        ∀ a ∈ cellVertices ε (S.η ω) (Λ ω t), ∃ y ∈ Y, dist (vertexPoint ε (S.η ω) a) y < r / 4 ∧
          a ∈ cellVertices ε (S.η ω) (ball y (3 * r)) ∧
          ∀ g : Ω → ℂ → ℝ, (∀ ω x, 0 ≤ g ω x ∧ g ω x ≤ 1) →
            ENNReal.ofReal (layerPotential S ρ ε g ω a) ≤
              ENNReal.ofReal ε *
                  expectedExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball y (3 * r))) a +
                ENNReal.ofReal p⁻¹ * ENNReal.ofReal (layerPotential S ρ ε g ω (vertexOf ε (S.η ω) y))
```

Exact named residual `MatedCRT/Proofs/Sec5/StoppedLayerPotentialReduction.lean:225` (namespace MatedCRT):

```lean
def LayerExitMassSmallStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ c : ℝ≥0∞, 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∀ s : ℝ, 0 < s →
  ∃ r : ℝ, 0 < r ∧ r < s ∧
    S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
      {ω | c < K * ⨆ z ∈ ball (0 : ℂ) ρ, largestExitTimeRV (S.μ ω) (ball z (4 * r))}) < η
```

Exact named residual `MatedCRT/Proofs/Sec5/StoppedLayerPotentialReduction.lean:243` (namespace MatedCRT):

```lean
def LayerFixedCenterStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  MepsScalingInput 𝒮 →
  DiscreteLaplacianBoundCorrectedStmt 𝒮 → MaximumPrincipleStmt 𝒮 →
  ConvergenceDivisibleStmt 𝒮 → UniformConvergenceGreenKernelStmt 𝒮 → ExitTimeUpperBoundStmt 𝒮 →
  IntegralConvergenceGreenFunctionStmt 𝒮 →
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t →
  ∀ f : ℕ → Ω → ℂ → ℝ, (∀ n ω x, 0 ≤ f n ω x ∧ f n ω x ≤ 1) →
    (∀ n x, Measurable[S.envSigma] fun ω => f n ω x) →
    (∀ n ω, IsHolderContinuousOn (f n ω) (ball 0 ρ)) →
    (∀ ω ∈ {ω | t < clusterExitTime (Λ ω) ρ},
      ∀ᵐ x ∂(S.μ ω), Tendsto (fun n => f n ω x) atTop (𝓝 0)) →
  ∀ Y : Finset ℂ, (∀ y ∈ Y, y ∈ ball (0 : ℂ) ρ) →
  ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ c : ℝ≥0∞, 0 < c → ∀ η : ℝ≥0∞, 0 < η →
  ∃ N : ℕ, ∀ n ≥ N, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    S.P ({ω | t < clusterExitTime (Λ ω) ρ} ∩
      {ω | c < K * ∑ y ∈ Y, ENNReal.ofReal (layerPotential S ρ ε (f n) ω (vertexOf ε (S.η ω) y))}) < η


/-! ### Part 4: assembly into `StoppedLayerPotentialStep` -/
```

Rate report G1/G2: uniform exponents are not supplied by a per-environment existential. Their exact existing types follow; consumer correctedHarmonicSameWalkRateAe_of_ae_geom / correctedHarmonicSameWalkRateAe_of_cellTarget. G1's producer is written in r3 Section1:36-254; G2's deterministic nu from the annulus probability is written at r3:692-714. Both are implementation obligations, not new WPN or approved frozen changes. Keep the constants fixed in the displayed order.

`MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SameWalkAssemblyAe.lean:266` (namespace MatedCRT):

```lean
def CellSizeTargetAeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ (2 : ℕ) →
  ∃ κ : ℝ, 0 < κ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ A : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (A ε)) ∧
    (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (A ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, (ω ∈ A ε ↔
      ∀ i : ℤ, (cell ε (S.η ω) i ∩ ball 0 ρ).Nonempty → diam (cell ε (S.η ω) i) ≤ ε ^ a)
```

`MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SameWalkAssemblyAe.lean:278` (namespace MatedCRT):

```lean
def UniformSameWalkAeCoreStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β : ℝ, 0 < β ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ν : ℝ, 0 < ν ∧
  ∀ a : ℝ, 0 < a → a < 2 / (2 + γ) ^ (2 : ℕ) → ∃ κ : ℝ, 0 < κ ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ E : ℝ → Set Ω, (∀ ε, MeasurableSet[S.envSigma] (E ε)) ∧
    (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      S.P (E ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ κ)) ∧ PointwiseSameWalkRatesAeStep S E ρ a β ν
```

G3 correction: the cells-meet premise is already implemented by adjacentCellsMeetAeStep in Proofs/MatingOfTrees/AdjacentCells.lean:17 and freshly passes strict lc and a standard-axiom probe. Its specialization or ae_isRegularMatedMap.cells_meet should supply the GMS premise. This does not itself assert the stronger separated-interval lemma. G4 a.s. finite exit and the exact discrepancy bound remain source-written work at r3:657-722; ae_vExitTime_ne_top_of_expectedExitTime_ne_top in OccupationGreen.lean:135 retains its finite-expectation premise. G5 and the layer literature inputs remain explicit Proposed hypotheses pending source promotion, including the separate GMS canonical-to-arbitrary-valid-model bridge. No External or frozen declaration changed.

Receipts: fleet lead/checks/20261108-1913. Ten pinned source versions (nine distinct files), four axiom probes/sixteen standard-axiom exports; no numbered closure.


Late checked bd29395: sameWalkExitDiscrepancy_le_of_finite_exit and its a.s. version supply the exact bound from start-in-disk and finite-interpolated-exit hypotheses. integral_discrepancy_le_regime supplies real-valued three-regime means, including H=0, from measurability, the a.s. bound and scaled tails. Those hypotheses remain; the actual finite-exit producer and full uniform event/rate assembly are not discharged. This refines the earlier G4 implementation boundary rather than introducing new WPN. Three new embedded axiom prints use only standard axioms. Final receipts:11 pinned source versions across9 files,4 additional axiom probes,19 distinct checked exports,85-source hole scan clean.


Late bounded cutoff da545b8/adb651f (lead19:25): the source-pole finite-domain comparison, capacity inequality and real-infimum admissible-family bound in StoppedPoleFiniteComparison.lean pass strict source checking with17 standard-axiom exports. The assumptions retain finite domain, symmetry, local finiteness, consecutive adjacency, boundary inequality and D inside A; the infimum's nonemptiness and lower bound are proved. This implements r3:1192-1257, including the source vertex, but does not discharge StoppedSurplusPoleStep, measurable positive c, reconstruction or its outer-probability limit. The new measure_discrepancy_tail_enlarge supplies the numerical large-scale tail extension with its displayed hypotheses; it does not supply the uniform annulus producer. Final receipts lead/checks/20261108-1913:17 strict lc calls,13 pinned source versions across10 files,37 distinct standard-axiom exports,86 hole-clean source hashes. New commits after this bounded cutoff await the next round. No numbered closure.


## Final audited returns and checked components (lead19:46 round)

Operator19:35 released the final three written-proof requests: fleet `notes/wpn-steps3/steps3.tex`, sha256 `d34cf930706e195c09ec2eb14c8999a6a1d64cc6b69938b6e227d2ddf9619d9d`, independent `AUDIT-steps3.md` VERDICT CORRECT for all three outcomes. This is written proof availability, not Lean closure. No further prover rounds will occur under operator18:55. The original representative and raw-circle Steps are false; only the specified bounded/represented repairs may be implemented. The insertion extension is internal mathematics, never a literature hypothesis presented as DS11.

The bounded repair adds `Bornology.IsBounded Λ` before `IsSubharmonicBall μ Λ 0` in the exact historical type. The only direct mathematical application at ScaledRegularizedFamily.lean:228-231 receives boundedness from the regularized-family field `h1.isBounded (c*t) (mul_pos hc ht)`; both PlateauScalingAssembly consumers retain their conclusions. No frozen or companion file is edited by the lead.

944485f BrownianMinimum.lean:190,291 proves separated-interval minima are a.s. unequal for arbitrary two-sided intervals, using a nondegenerate Gaussian gap independent of the joint countable left/right increment family. Strict source and axiom checks pass. The uniqueness paragraph at the end of r3:534-599 is not implemented in that slice; it remains written implementation work, not a new WPN. 7e08a81 SameWalkRatesAe now supplies adjacent-cells intersection a.s. for all positive meshes; G3 is discharged in its conditional rate bound. Uniform environment-independent cell/rate exponents, actual finite exit and rate/event producers remain open. Proposed cell-configuration staging 23094a3 elaborates but has no source-promotion approval.


## Checked compact code and canonical moment boundary (lead20:19 round)

Pinned6c2f4a4 includes z1's1d739b1/9345a37/c03d939 compact-code slice. Strict lc and four explicit axiom prints pass for `StoppedCompactCode.measurable_codeCompact` (:354), `codeCompact_eq_closure_of_membership` (:368), `ae_codeCompact_eq_closure` (:395) and the Hausdorff-hit event (:261). The compact-valued map is Borel for the Hausdorff/Vietoris topology; recovery assumes simultaneous rational membership versions and a.s. open/bounded/nonempty Lambda. These exact premises remain. r3:3146-3169 writes their countable indicator construction; it follows the internal insertion and analytic-margin tasks. The actual CodeSectionStmt remains an independent written implementation obligation. No geometry, margin or numbered result closes here.

Standing m5 DONE's six Step/tail/mean/assembly/audit/source files pass fresh strict lc. Current97eac20/504a196 GMS reconstruction staging and55c3bfd/6c2f4a4 canonical-moment staging also elaborate; this is not source approval. GMS1.16 now separates Brownian limit, recurrence and harmonic-center Props and uses outer integrals of bounded continuous tests without cylinder measurability. Law existence and the nonseparable-path outer-expectation reading remain explicit boundaries. GHMS/DMS missing carriers remain open; no theorem-shaped substitute for them is accepted.

### WRITTEN-PROOF-NEEDED WPN-51-canonical-inner-degree-measurability

Exact prospective Step below, elaborated in fleet `lead/checks/20261108-2019/CanonicalDegreeStepType.lean`. It is a named residual specification, not a landed theorem or new axiom. Declaration/carrier anchors: `MatedCRT/Proposed/StoppedPoleCanonicalMoments2026.lean:74` (canonical model), :113 (inner degree), :193 (printed degree bound). The new internal tail module is reserved for z5; the tail-to-moment consumer at r3:2733-2753 requires this measurability for Tonelli/layer cake. The eventual consumer is the canonical inner-degree moment producer in r3 Section6, then `StoppedInterior.StoppedSurplusPoleStep` at StoppedInterior.lean:136. No implemented tail-to-moment consumer currently discharges this premise.

```lean
namespace MatedCRT.StoppedCanonicalMoments
/-- Prospective named residual; no proof is claimed. -/
def CanonicalInnerDegreeMeasurabilityStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
      IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
        AEMeasurable (fun ω => (gmsInnerDegree (η ω)).toENNReal) P
end MatedCRT.StoppedCanonicalMoments

```

Reason open: `gmsInnerDegree` is an uncountable-interval supremum; r3:2690-2753 uses D as a random variable but does not write its measurable/analytic coding proof. z5's source review has not located that proof in GMS1705.11161v5 Definition4.5 pp32-33. The new specification keeps the staged model's source/representation bridge explicit; no automatic extension to arbitrary abstract IsValid models is claimed. Under operator18:55 there is no further prover request. Keep this Step named indefinitely unless an already-written applicable proof is located. The queued Chebyshev component proceeds with exact measurability premises; no worker may invent the missing producer.

The printed inequality(4.20) itself remains a faithful explicit cited Prop, `GMSInnerDegreeBoundStmt`; its background justification is not an additional prerequisite for this conditional work. r3:1789-1812 already writes a finite-consecutive-mesh null-overlap argument from area parametrization. That written component and the cited bound are distinct from this degree-coding residual. Do not label the printed cited inequality a new WPN. All previous twelve requests have audited written outcomes; this new source-boundary Step has none.

Round receipts: ten strict source/probe calls across nine pinned files,18 distinct standard-axiom exports; additional exact prospective Step type checked separately. Ninety-source code-hole scan clean;23 paused task/control hashes preserved. All4 next plus guarded following briefs ready; m1/m5 quota stops respected. No new12-round event, frozen edit, promotion or numbered closure.


## Lead20:50 round: q1 transfer, checked components and source hold

Operator20:50 transfers m1's current canonical-conditioned bridge to q1 (Haiku effort max). Preserve m1's credit, the operator-moved brief and m1.next; no duplicate canonical assignment goes back to m1. q1 owns the continuation and reports only in reports/q1.md. q1's independent local-integrability successor uses audited env-steps:243-252; the represented-circle grid remains reserved for m1. m1/m5 are quota-stopped until resets; q1/z1/z5 are live, five assigned workers total. The other paused workers' files remain untouched.

Checked ec2200c supplies the no-insertion-atom component conditional on the exact `MatedCRT.MeasurableDyadicDecoder γ α`. The exact old insertion Step is definitionally equal to `MatedCRT.InsertionCoordinateExtensionStep`, checked against its pre-move body with `rfl`. This does not prove that Step. Written decoder construction, local Dirichlet/harmonic decomposition, punctured all-scale convergence and complex-affine extension remain implementation work. The reported question is resolved: conditional INTERNAL work may explicitly retain the local-decomposition Step and the faithful Sheffield-Wang input. Include the harmonic regularity in that Step; the report's abbreviated existential type alone is insufficient. Audited steps3:609-621 writes its proof, so this is not a new WPN.

Refreshing the DS alias object exposed a real integration collision: both the new insertion module and legacy InsertionScalingLaw exported `MatedCRT.isLQGLimit_congr_pos` with different premise shapes. The lead makes the new module's helper private, preserving the legacy public helper and the exact Step. The earlier consumer check against the stale alias is superseded by the fresh-dependency checks in lead/checks/20261108-2050. This repair changes no source theorem, frozen statement or conditional premise.

Checked e6726ea supplies analytic strict-sublevel projections, Preston-conditional Borel infimum versions and the denseDecoder surplus assembly. Actual supersolution section/finite infimum/continuous surplus/state-map pullback producers remain explicit (report z1 R1-R6); Borel-on-state does not itself prove uncompleted envSigma measurability. Rational-membership versions remain the fresh bounded task.

Checked 9ec52ac/5d2ded7 supplies `StoppedCanonicalMoments.tail_moment_outer` and `gms_innerDegree_moment`. The latter requires four explicit Proposed Props (GMSLemma43Eq46Stmt, GMSMassBetaMomentStmt, GMSCoordinateChangeStmt, GMSInnerDegreeBoundStmt), the canonical zero-cone model and a SUPPLIED rescaled LQG-measure family μb with its IsLQGMeasure hypotheses. Its conclusion is finite outer p-moment for 1<=p<4/gamma^2, not degree measurability or the final pole Step. Measurable supersets of dyadic tail sets bypass the degree-measurability requirement for THIS outer-moment conclusion. **WRITTEN-PROOF-NEEDED WPN-51-canonical-inner-degree-measurability stays named and unproved; it is not a premise of this new outer-tail route.** Historical text above saying no implemented tail-to-moment route exists is superseded to that extent. No background/consumer source bridge is thereby discharged.

BG SOURCE HOLD: `BGLemma33Stmt` and `BGTheorem41Stmt` at Proposed/StoppedPoleCanonicalMoments2026.lean:223,230 abbreviate frozen arbitrary-IsValid Draft claims. This directly violates the20:25 canonical-scope direction and audited r3:2989-3028, which expressly avoids abstract ConvergenceDivisibleStmt. Their compilation is checked, but their identification as canonical published inputs is rejected pending correction. The IsValid docstring does not prove a canonical-law identification. z5's queued correction owns only its Proposed packet; the frozen Draft remains untouched. Outer-expectation reinterpretations also stay subject to exact source review/equivalence, never promotion by compilation. Printed(4.20) remains an explicit cited bound, with no new request to prove its background. All earlier twelve WPN have audited written outcomes; no further prover round is requested.


### WPN-51 consumer correction, lead21:28

WRITTEN-PROOF-NEEDED remains: the exact `CanonicalInnerDegreeMeasurabilityStep` above has no written coding proof. The landed conditional consumer is now `Proofs/Sec5/StoppedPoleInnerDegreeMoments.lean:476` (hMeas); the worker report's filename omitted `Pole`. Its use in the layer-cake proof is at145, with wrappers323/467. Neither the new outer-moment theorem489 nor a plain lower-lintegral finiteness corollary requires it: the lower lintegral is bounded by every measurable majorant and hence by the outer integral. Retain the Step for actual measurability/Tonelli identities and future random-variable consumers. No terminal-policy exception or new prover request is made.


## Lead22:00 updated consumers and WPN-52 ambient zero-boundary finiteness

WPN-51 remains WRITTEN-PROOF-NEEDED. After a7593ac the actual layer-cake use is StoppedPoleInnerDegreeMoments.lean:520, wrappers699/874. Plain lower-integral finiteness now has an implemented no-measurability route:731/740/907. Previous :145/:323/:476/:489 locators are historical.

b95d6fb proves conditional punctured disk/all-scale convergence, using LocalDirichletHarmonicDecompositionStep:663 and ZeroBoundaryLimitLocallyFiniteStep:679. The former has audited written proof steps3:609-621; its implementation remains. The stronger ambient-finiteness Step below is not written in steps3:603-625 and stays unproved under the terminal policy. **WRITTEN-PROOF-NEEDED WPN-52 (ambient zero-boundary finiteness as declared; potentially bypassable)**; exact type at InsertionCoordinate.lean:679-690:

```lean
def ZeroBoundaryLimitLocallyFiniteStep : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ α : ℝ),
    0 < γ → γ < 2 → α < lqgQ γ →
    ∀ (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
    ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → Metric.closedBall c ρ ⊆ ({0}ᶜ : Set ℂ) →
    ∀ (h0 : Ω → (ℂ → ℝ) → ℝ) (hcirc0 : Ω → ℝ → ℂ → ℝ) (H : Ω → ℂ → ℝ),
      IsDirichletGFF P (Metric.ball c ρ) h0 hcirc0 →
      (∀ᵐ ω ∂P, IsHarmonicOnDisk (Metric.ball c ρ) (H ω) ∧
        ∀ r z, 0 < r → Metric.closedBall z r ⊆ Metric.ball c ρ → hcirc ω r z = hcirc0 ω r z + H ω z) →
      ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (((μ ω).restrict (Metric.ball c ρ)).withDensity
        fun z => ENNReal.ofReal (Real.exp (-(γ * insertionRemainder α (H ω) z))))
```

Consumer: punctured_disk_allScales:755 (and punctured_allScales_of_steps:906). Boundary issue: this asks local finiteness on all of C for a measure supported in an open disk, hence finite mass near its boundary; continuity of the harmonic remainder only inside the disk does not supply that bound. No worker is assigned to prove this stronger Step and no further prover round is requested.

Primary Sheffield-Wang arXiv:1605.06171v2 pp2-3, Theorem1.1, states weak convergence in D. The staged compact-test consequence unnecessarily demands ambient IsLocallyFiniteMeasure of the supplied limit, whereas domain-local finiteness suffices. z1's queued source-scope/consumer repair replaces that demand with finiteness on compact subsets of D, using the written compact-supported multiplier argument and existing measure bounds; it must preserve the stronger Step as unproved and report exact remaining types. This bypass is not a proof of WPN-52. See E-SW-AMBIENT-FINITENESS and IR-SW-DOMAIN-COMPACT-CONSEQUENCE. Current decoder task is unchanged; affine work is archived/preserved afterwards.
