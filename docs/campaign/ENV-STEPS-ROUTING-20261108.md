# Audited environment and stopped-clock proof routing (2026-11-08)

Operator ruling: fleet `inbox.md`, 2026-11-08 09:45 UTC. The written proof is
`/home/nitro/paper-fleets/mcrt/notes/env-steps/env-steps.tex`, 1292 lines,
SHA256 `26dfc02c2f703d4c5658a2f619abb0e45457aad04d2f94dc0e7521f01aa03ae4`,
prepared against snapshot `e52ce6e`. Independent audit:
`notes/env-steps/AUDIT-env-steps.md`, verdict **CORRECT**, no suspected errors.
Line numbers below refer to that pinned TeX file.

These are **WRITTEN-PROOF-AVAILABLE / LEAN-PENDING** obligations. This changes
the status of the three historical environment requests and repairs the fourth
request's quantifiers. It is not a claim that any of the four Lean obligations
has been discharged. Literature remains faithful explicit hypotheses; Proposed
statements await the operator's source check before any External promotion.

## Existing environment targets

The exact existing declarations are in
`MatedCRT/Proofs/Sec1/EnvironmentScaling.lean`:

| Exact Lean target | Written proof and bounded route |
| --- | --- |
| `MatedCRT.RescaledConeFieldStep : SpaceFillingSLEModel → Prop` (line 113) | Proposition field, 299-335; countable distribution coding 176-207 and canonical-law lemma 210-296. m1 first proves a measurable representative for the uncompleted field sigma-algebra; its successor handles canonical/rescaled law. |
| `MatedCRT.RescaledConeClockStep : SpaceFillingSLEModel → Prop` (line 130) | Proposition clock, 449-487; all-start selection and universally measurable good fields, 380-446. z1 first proves selection/law-transfer components, then the exact all-start transport. |
| `MatedCRT.RescaledMatingOfTreesStep : SpaceFillingSLEModel → Prop` (line 139) | Proposition mating, 942-981; same-space lift 665-691, area scaling 693-765, main joint law 767-940. m5 first proves the same-space lift; its successor handles a bounded random-radius area-scaling bridge. The full main-law and 24-field transport remain pending. |

The first three targets retain their exact definitions. In particular the clock
quantifies over every Brownian start on one field event without assuming the
supplied rescaled circle version is measurable. The mating target constructs
all auxiliary variables on the original arbitrary sample space. The written
proof uses unused radial Gaussian randomness to sample a conditional law;
equality in distribution alone is insufficient for this same-space conclusion.
The three proofs would supply the corresponding hypotheses of
`coneEnvironmentScalingStep_of_inputs`; they are still explicit until proved.

## Stopped clocks: false arbitrary discharge and true constructor

The existing `MatedCRT.DirichletStoppedClockConvergenceStep` at
`MatedCRT/Steps/Sec3/DirichletStoppedClock.lean:15` is a predicate of a supplied
`G`. The other assumptions of
`berestycki_dirichlet_time_change_eq_lbm` do **not** imply it for arbitrary `G`:
Proposition false, lines 1071-1095, takes `G = 1`; every approximate killed
clock is zero at time zero. This refutes a universal discharge of the source
hypothesis, not the conditional transfer theorem itself. The example uses
`γ = 0`, `F(t) = t`, and concentric disks with a Dirichlet GFF; the time-zero
obstruction works at positive subcritical γ whenever the other assumptions
are instantiated.

Proposition correctstopped, 1106-1252, constructs a suitable `G` under
`0 ≤ γ < 2` and bounded simply connected `D`, retaining the consumer's other
hypotheses. It proves locally uniform convergence on a product-conull event
and identifies the result with stopped `F` on the stated iterated-conull event.
The raw supplied `F` need not be jointly measurable. Callers must obtain the
constructed `G` and its source proof before invoking the unchanged consumer.
Existing frozen and paused-worker files are untouched.

The following is the exact needed existential interface extracted from that
proposition, expressed using a jointly measurable continuous-path-valued map.
It is a **specification awaiting proof**, not a literature assertion or a new
production assumption. Its command elaborates with the repository's strict
`lc` settings (receipt `fleet/lead/checks/20261108-1002/`). `Gc` supplies the
existing predicate; the source's stronger locally uniform conclusion may be
proved as a separate theorem. The actual constructors/bridges are reserved for z2's
new files; z2 is currently paused by the operator. No global measurability assumption on `F` has been added.

```lean
def AuditedDirichletStoppedClockExistenceStep : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D U : Set ℂ) (h : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (x : ℂ) (γ : ℝ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ),
    IsOpen D → IsOpen U → Bornology.IsBounded D → SimplyConnectedSpace D →
    Bornology.IsBounded U → closure U ⊆ D → x ∈ U →
    IsDirichletGFF P D h hcirc → 0 ≤ γ → γ < 2 →
    (∀ᵐ ω ∂P,
      IsLQGClock planarBrownianMotion γ (hcirc ω) x (F ω) ∧
      ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω b)) →
    ∃ Gc : Ω × ContinuousPath ℂ → C(ℝ≥0, ℝ),
      Measurable Gc ∧
      DirichletStoppedClockConvergenceStep P U γ hcirc x
        (fun ω b t => Gc (ω, b) t) ∧
      ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), ∀ t : ℝ≥0,
        Gc (ω, b) t = F ω b
          (((t : ℝ≥0∞) ⊓ ContinuousPath.exitTime U b).toNNReal)
```

Imports and notation used to elaborate the specification:
`MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.DirichletClockTransfer`;
namespace `MatedCRT`; open `HarmonicBalls MarkovProcess MeasureTheory
ProbabilityTheory Filter Topology Set`; scoped `ENNReal NNReal`.

z2's first bounded task proves the time-zero obstruction and the dense-time
monotone-clock upgrade (1207-1224). Its successor stages the exact printed
clock result and builds the measurable limit on the Cauchy event (1227-1245).
Berestycki's path convergence theorem is not substituted for clock convergence.
The stopping convention's endpoint term at 1166-1186 is handled as written,
including the separate γ=0 argument. No outside-circle convention is imposed;
compact containment makes all sufficiently fine scales admissible.

## Cited inputs: precise staging ownership

Only source statements absent from the existing interfaces need staging. Reuse
Mathlib/project results first. Each statement must retain its printed carriers,
hypotheses and conclusion, with a source locator; repository-specific bridges
are proved from the audited argument. The assigned Proposed files are disjoint.

| Source and pinned locator | Owner / proposed file |
| --- | --- |
| Preston, arXiv:0809.3066v1, Theorem 6.1, printed p35/PDF36 | m1: `MatedCRT/Proposed/PrestonCoding2008.lean` |
| Preston, Theorem 7.1, printed p39/PDF40 | z1: `MatedCRT/Proposed/PrestonAnalytic2008.lean` |
| GRV, arXiv:1301.2876v4, Theorem 2.7 pp10-11 (retain its massive-field and regularization scope) | z1: `MatedCRT/Proposed/GarbanRhodesVargas2013.lean`; staged for source checking, not used as a cone-clock substitute |
| Preston, Theorem 12.1, printed p61/PDF62 | m5: `MatedCRT/Proposed/PrestonConditional2008.lean` |
| DMS, arXiv:1409.7055v4, Remark 4.4 pp74-75, Lemma 4.9/Definition 4.10 p79, Proposition 4.13(i) p80/proof81 | m1: `MatedCRT/Proposed/DuplantierMillerSheffieldCone2014.lean` |
| Sheffield-Wang, arXiv:1605.06171v2, Theorem 1.1 p3 | m5 successor: `MatedCRT/Proposed/SheffieldWang2016.lean` |
| Berestycki, arXiv:1301.3356v1, Section 2 p5 stopping, p6 explicit dyadic clock convergence, estimates pp6-9 | z2 successor: `MatedCRT/Proposed/BerestyckiClockProof2013.lean` |
| Duplantier-Sheffield, arXiv:0808.1560v2, Propositions 3.1-3.2 p17 | z2 successor: `MatedCRT/Proposed/DuplantierSheffieldCircle2008.lean` |

GRV arXiv:1301.2876v4 Theorem 2.7 pp10-11 concerns its massive field and
regularization. The clock proof instead transports the original valid cone's
all-start clock property; it makes no massive-to-cone regularizer substitution.
Sheffield-Wang is staged in its bounded zero-boundary setting; off-zero cone,
continuous-addition and random-radius consequences require the written bridges.
Preston 12.1 supplies conditional distributions, not an unsupported assertion
that an arbitrary sample space admits any prescribed resampling.

m6 retains the checked `m6-prop42-strict-gap-with-cameron-martin-r2` task,
parked by the latest operator budget ruling. z5 continues the plateau law
argument under explicit scaling and volume-growth inputs. The old m1 occupation, m5 assembly, z1 stopped/global inclusion,
and z2 truncated fixed-time briefs are archived in fleet
`lead/archive/20261108-1002/`, with their prior successors preserved. They remain
pending work. The new audit does not settle occupation estimates, the cone
start-at-zero Green lemma, independent strict growth, or unrelated gaps.

If an exact Lean-level bridge needs mathematics absent from these written
arguments, record its full type with the limiting source lines here or in the
appropriate GAPS file and in PROGRESS as WRITTEN-PROOF-NEEDED. Do not invent it.

## Checked implementation progress, 2026-11-08 12:46 UTC

Lead receipts: fleet `lead/checks/20261108-1241/`; eleven source files plus two
axiom probes pass strict `lc`. The three remote DONE files also pass fresh
checks. A scan of 40 relevant existing sources finds no proof holes or axiom
declarations (the sole raw match is a Proposed file's explanatory comment).
The ten inspected new theorem exports use only `propext`, `Classical.choice`
and `Quot.sound`. These are conditional implementation checks, not a closure
or independent source-fidelity verdict.

- m1: countable distribution reconstruction (`641da0b`), measurable variable
  dilation (`b58b586`), and recovery of centered positive circles (`31cb45f`)
  are implemented. `Field.lean` passes with full-circle recovery
  (`d1d1dd6`) as well. The rescaled pairing theorem still takes the existing
  `QuantumConeScalingInput`; canonical cone identification and the actual
  radial/lateral independence and lateral-law conjuncts of
  `RescaledConeFieldStep` remain open. Its queued slice assembles the exact
  field Step only after those law obligations are supplied by proved bridges
  and faithful distributional DMS input.
- m5: `exists_same_space_lift` (`2a46f41`) proves the generic same-space kernel
  realization given a measurable independent uniform variable, a prescribed
  projection law and standard Borel source/target carriers. It does not yet
  construct that variable from the cone. `ae_rescaled_measure_eq_of_allScale_off_origin`
  (`c032d3e`) proves random-radius area scaling given one all-positive-scale
  off-origin convergence event, continuous circles at the required scales,
  the rescaled dyadic LQG measure and zero mass at zero for both measures.
  The queued continuous-addition/countable-localization slice addresses the
  all-scale premise using the written disk-decomposition argument at715-730.
  Full mating law and 24-field transport remain open.
- m6: `harmonicBallStrictObstacleGapStep_of_restrictedLaw_and_pairingLaws`
  (`7001c44`) consumes whole-plane existence, restricted LQG law equality,
  mutual absolute continuity of actual smooth-shifted local pairing laws,
  and the listed HB/volume-growth statements. Coordinate-law transport is
  proved (`51c2725`), with its representation premise explicit. A subsequent
  whole-plane Dirichlet-coordinate representation (`bef75f3`) also passes
  lead lc and the axiom probe. The full faithful IG IV Proposition2.9 statement and its passage
  to those coordinates remain obligations; these are not silently replaced by
  the stronger pairing-law input. Independent strict growth is still open.

`Proposed/SheffieldWang2016.lean` now contains the candidate compact-test
consequence `SheffieldWangCircleAverageAllScaleStmt`, with arXiv1605.06171v2
Theorem1.1 p3 and domain/field p2 locators. The operator's source review is
requested in fleet INPUT-REQUESTS; this is not an External promotion.
The Preston statements need no new staging where Mathlib already supplies the
required coding, conditional-distribution and kernel-realization theorems.

## Current routing and checked progress, 2026-11-08 14:33 UTC

The newest inbox ruling (labelled 14:40 UTC) limits the active fleet to
**m1, m5, z1 and z5**. m6 and z2 are paused; their briefs are preserved.
m1/m5 remain on the environment proof and obey the operator's 96% quota stop.
The lead stopped its own pending z2 refill watcher; no worker control was
changed. All four active workers have next tasks and distinct staged successors.
No new 12-round event was found; m6's checked r2 is preserved while paused.

Five new source files pass fresh strict `lc` (receipt
`fleet/lead/checks/20261108-1425/`). All 40 previous source hashes are unchanged;
the 45-file hole/axiom scan has only three explanatory comment matches.
Twelve inspected theorem exports use only `propext`, `Classical.choice` and
`Quot.sound`. These are conditional implementation checks, with no new
numbered-result closure.

- z1 `aef42b6`: Borel-null-sandwich law transfer works without completeness of
  the sample space. The all-start clock interface proves universal
  measurability and law transfer **conditional on** the explicit Borel
  subsequence-selection, Borel relation and characterization Steps, the
  actual Borel/Polish circle-function structure, and the staged Preston
  analytic-set input. The common field event still quantifies over every
  Brownian start. Selection, measurable circle-process construction, law
  identification and final rescaled-clock transport remain Lean-pending
  parts of the written argument at380-487. z1 has the law-transfer task,
  with circle-process structure and Borel clock-limit work queued.
- z5 `488dcb0` and `b1f152d`: deterministic radius/plateau scaling identities and a conditional
  plateau-scale reduction are implemented, together with canonical measurable
  radius and plateau events from bounded-disk raw-cluster codes. The latter
  gives a.e. event identification and plateau probability transfer under
  identical measure laws. It does not prove the stronger predicate on all
  measures measurable. The queued assembly uses the canonical event instead.
  Remaining source-backed inputs are `InsertionLQGScalingLawStep`,
  `ScaledRegularizedFamilyStep`, and the existing explicit HB
  `HarmonicBalls.LQGVolumeGrowthAllScalesStmt`.

The all-integer-disk volume-growth premise in z5's report is already supplied
conditionally by HB `Steps/Sec3/Basic.lean:71`,
`ae_isLocallyFiniteMeasure_volumeGrowth`, from
`HarmonicBalls.LQGVolumeGrowthAllScalesStmt` (`Draft/Section2.lean:122`).
Apply this helper to both whole-plane GFF/LQG pairs furnished by the scaling-law
Step. This corrects the report's request for a new all-radius External input:
the existing HB statement is an explicitly unproved consequence, as its
source docstring says, and remains a named hypothesis. No new literature
approval or proof of it is asserted.

`Proposed/PrestonAnalytic2008.lean` is staged, with exact Prop
`MatedCRT.PrestonAnalyticUniversallyMeasurableStmt`. Its Section7 ambient-source
check remains assigned to z1 before an External promotion request. GRV's
massive-field/independent-scale carriers and normalization still need faithful
source preparation; no cone-clock substitution or unprepared carrier request
is made. Fresh z1/z5 reports and observed task promotion resolve their earlier
pickup question. z2's pickup request is superseded by its paused status.

The nine remaining WPN requests (WPN-36 x3, WPN-42-locality, WPN-51 x5) were
sent by the operator to a separate prover at14:20. All remain named hypotheses
pending individually returned independent audits; none is assigned to an
active worker here. Existing environment written proofs remain available.
