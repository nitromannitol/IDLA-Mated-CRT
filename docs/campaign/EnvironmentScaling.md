# Environment scaling proof obligations

The conditional reduction is `MatedCRT.coneEnvironmentScalingStep_of_inputs` in
`MatedCRT/Proofs/Sec1/EnvironmentScaling.lean`. Its three new hypotheses are
proof steps, not literature axioms. Their complete Lean types are their named
`Prop` declarations in that file. Paper line references below refer to
`paper/idla_mated_crt-corrected.tex`.

## Update: audited written proofs available (2026-11-08 09:45 UTC)

**WRITTEN-PROOF-AVAILABLE / LEAN-PENDING.** The operator supplied and
independently audited all three arguments below. See
[exact proof routing and source locators](ENV-STEPS-ROUTING-20261108.md).
The pinned proof is fleet `notes/env-steps/env-steps.tex`: field 299-335,
clock 449-487, mating 942-981, with supporting lemmas listed in that note.
m1 owns the field proof, z1 the all-start clock proof, and m5 the same-space
mating infrastructure. These Steps remain hypotheses until their Lean proofs
are checked. The stopped-clock gap has a separate existential repair; arbitrary
supplied `G` is not justified. No frozen declarations were changed.

## Historical requests (written-proof need superseded by the update)

The descriptions and earlier source observations below record the original
requests. The new pinned DMS source is arXiv:1409.7055v4, as audited.

1. `MatedCRT.RescaledConeFieldStep : SpaceFillingSLEModel → Prop`: for a valid
   environment and an a.s. equal measurable circle version, construct measurable
   rescaled pairings with the stated a.s. equality to `rescaledPairing`, radial
   and lateral independence, lateral law, and field-sigma inclusion. The paper
   uses the transformed field at lines 3617–3625 and its equality in law at
   lines 452–459. DMS14 Proposition 4.13(i), arXiv:1409.7055v5 p. 80, gives
   field equality in law; `QuantumConeScalingInput` records the circle-process
   part, but the repository's pairing, lateral and sigma bridges require proof.
2. `MatedCRT.RescaledConeClockStep : SpaceFillingSLEModel → Prop`: for the
   rescaled circle version, construct one clock satisfying `IsLQGClock` and
   `IsTimeChangeClock` simultaneously for every starting point, with the exact
   quantifier order in the declaration. The paper uses the cone and LBM at
   lines 705–712 and scaling at 3617–3625. GRV16 Theorem 2.7 and Berestycki
   2015 Theorem 1.4 do not state this full whole-plane, all-starting-points
   representation for the repository's clock definition.
3. `MatedCRT.RescaledMatingOfTreesStep : SpaceFillingSLEModel → Prop`: given
   the rescaled cone and its actual transformed pairings, construct the complete
   `IsMatingOfTreesCoupling` with rescaled boundary pair, curve and pairings, as
   quantified in the declaration. The paper uses the mated-CRT coupling in its
   setup and scaling at lines 3617–3625. DMS14 Theorem 1.9, pp. 26–27, gives
   the boundary Brownian motion and translation invariance, not the full
   repository-specific coupling representation; covariance beyond κ′ ≤ 8 also
   needs the corresponding extension.

The measurable circle modification and field-measurable version of the cone
scale radius are proved in Lean; neither is an additional step hypothesis.
`RescaledEnvironmentInput` is retained only as a legacy declaration: its exact
raw-circle measurability requirement has the null-set defect explained in its
docstring, and the new reduction does not use it.


## Operator19:35 final circle-recovery return

Operator19:35 released the final three written-proof requests: fleet `notes/wpn-steps3/steps3.tex`, sha256 `d34cf930706e195c09ec2eb14c8999a6a1d64cc6b69938b6e227d2ddf9619d9d`, independent `AUDIT-steps3.md` VERDICT CORRECT for all three outcomes. This is written proof availability, not Lean closure. No further prover rounds will occur under operator18:55. The original representative and raw-circle Steps are false; only the specified bounded/represented repairs may be implemented. The insertion extension is internal mathematics, never a literature hypothesis presented as DS11.

The raw ConeDilationCircleApproximationStep is refuted. Its represented replacement is exactly RescaledConeDistributionCircleGridStep, with the measurable simultaneous distribution representation already in that declaration. The current canonical m1 task is preserved and its successor implements this direct route; see [final audited routing](STEPS3-ROUTING-20261108.md). This does not close RescaledConeFieldStep, clock or mating.


## Lead21:28 checked canonical bridge and source boundary

At dc010c1, afc254e/3c9322f pass fresh strict source checks. `CanonicalConeIdentification.lean:977` constructs a measurable post-last-zero continuous-path version from coordinate measurability, a.s. continuity and the explicitly assumed real-time sublinear limit. The law consumers at1029/1048 additionally assume `Proposed.DMS14Remark44PostLastZeroLaw`; uniqueness reuses the existing conditioned-law theorem. This is conditional implementation progress, credited jointly to m1 and q1, not discharge of the canonical cone or represented-circle Steps.

Primary-source check: [DMS1409.7055v4](https://arxiv.org/pdf/1409.7055v4), Remark4.4 pp74-75, gives a hitting-level characterization and post-last-zero construction of the conditioned drifted process. It does not literally state our delta-weak-limit predicate. Audited env-steps.tex:217-242 writes the density/entrance-law bridge. The staged Prop packages that additional identification, so source promotion stays HELD (fleet E-DMS44-WEAK-LIMIT-ATTRIBUTION / IR-DMS44-WEAK-LIMIT-BRIDGE). This is written implementation, not a new missing-proof request.

Lemma4.9 and Definition4.10 p79 supply the radial/lateral orthogonal decomposition and cone construction, rather than the weak-limit identity. Primary PDF and page text are cached at `~/paper-fleets/mcrt/lead/sources/dms-1409.7055v4/`; no operator source upload is needed. Real-time Brownian sublinear growth remains explicit; its written Gaussian/reflection/Borel-Cantelli component is q1's next bounded task, after radial local integrability, with measurable radial integrals preserved afterwards. Coordinate measurability versus the HasLaw API's a.e. measurability still needs a measurable continuous-path version. No reference-circle or canonical distribution-law closure is claimed.


Late checked component679ffd9: `RadialLocalIntegrability.lean` proves the planar logarithmic majorant integrable on closed disks, local integrability by domination, and the radial sublinear specialization. Its a.s. wrapper explicitly assumes continuity and sublinear growth; it does not establish either Brownian premise or the whole-plane GFF radial representation. Angular restriction integrability and measurable radial integrals remain separate written components. All six exports pass lead strict lc/standard-axiom checking. q1 now implements real-time Brownian sublinearity; measurable radial integrals is queued, with the angular logarithm component preserved after it.


## Lead22:00 checked Brownian sublinear component and dependency compatibility

b2ab34b `BrownianSublinear.lean` proves the Borel-Cantelli/deterministic interpolation route to the real-time sublinear limit, conditional only on `MatedCRT.Sec1.GaussianBandStep B P` (file:43-46). This supplies the hsub premise of CanonicalConeIdentification:981 once the maximal bound is instantiated. Six main exports pass strict lead lc/standard-axiom checks. This is not an unconditional Brownian theorem or canonical cone closure.

The source-written maximal estimate already exists at lattice-probability pin3912597, BrownianMax:247. Its import is blocked by BrownianTail:120, where mgf_gaussianReal receives `.map_eq` instead of the current HasLaw argument. The lead confirmed both signatures. A project-local, provenance-preserving compatibility port of the existing Tail/Max proofs is queued for q1 after the radial/measurable/angular tasks; external checkouts and .lake remain untouched. This is an implementation blocker, not an unwritten mathematical step. DMS44 attribution, the canonical law realization, radial representation and represented-circle recovery remain explicit.


Late checked1aaf67f: MeasurableRadialIntegrals.lean proves annular Riemann-sum convergence/AEMeasurability and ball truncation by the logarithmic majorant. Six main exports pass strict lead checks. Ball radial-path corollary retains continuity and sublinear growth; no unconditional Gaussian maximal bound, angular restriction or canonical-law closure.


## Lead22:32 Brownian API repair and angular component checked

236349c/b7356ec port the already written Brownian tail/maximal proofs into project-local compatibility modules. The HasLaw argument and deprecated Set membership names are adapted to the pin; dependencies remain untouched. GaussianBandProof now proves GaussianBandStep and real-time sublinearity for Mathlib IsBrownianReal with a probability law and measurable coordinates. 4450a2e composes this with the measurable continuous post-last-zero constructor, removing the supplied hsub/GaussianBandStep premise for those Brownian inputs. Its law corollaries retain DMS14Remark44PostLastZeroLaw explicitly: the held weak-limit identification is not discharged or promoted.

bd548bc proves angular logarithmic integrability on circles through zero, using a pointwise angular bound and its null exceptional angles. Planar local integrability alone would not imply this. q1's queued fixed-circle measurability component uses env-steps:248-251 and the existing radial approximations. The represented-circle grid remains reserved for m1; full quantum-cone scaling, stopped clock and joint transport remain open. Strict source checks and main-export axiom checks pass; no numbered closure.


## Lead23:01 angular measurability checked

bbdeb71/c936c23 MeasurableAngularIntegrals.lean:143/203/227 proves fixed-circle integral/average AEMeasurability from measurable positive-radius coordinates and a.s. continuity. Circles through zero are included by radial truncation and removal of null angular exceptions. This is measurability of the totalized integral, not a finiteness claim. Separate exports at244/293/318 establish integrability on such circles under the logarithmic majorant, radial sublinearity or the stated Mathlib Brownian hypotheses. Eight main exports pass strict lc and standard-axiom checks.

Audited env-steps:128-135,248-251 supplies the written approximation route; the implementation uses measurable truncations rather than annular Riemann sums. The actual lateralEval specialization and simultaneous countable-coordinate pullback are queued. q1 currently implements the written entrance-kernel bridge env:217-242, preserving m1 credit. DMS14Remark44PostLastZeroLaw, lateral_law (Defs/QuantumCone.lean:96-98), canonical representation and represented-circle recovery are not discharged. The conditioned-law proof is written implementation work, not a new WPN.


## Lead23:33 entrance kernels checked; WRITTEN-PROOF-NEEDED WPN-53

20dc27f CanonicalEntranceKernels.lean supplies the explicit kernels, survival ODE uniqueness (conditional on the stated derivatives and boundary limits), entrance pointwise limit, chain nonnegativity/measurability and the conditional setwise finite-dimensional limit. Thirteen lead axiom probes pass with only standard axioms. The entrance calculation reuses m1's e7050b2; credit is preserved. Neither ODE uniqueness nor a kernel formula identifies the actual killed/conditioned process by itself.

**WRITTEN-PROOF-NEEDED WPN-53: residual entrance-law justification on this route.** Audited fleet env-steps.tex:220-232 writes the density, survival ODE and entrance formula. At234-237 it passes to the assumed weak limit and identifies its laws. It does not supply the chain-law disintegration argument, the uniform integrable bound used by the new DCT proof, the normalizing integral calculations, or the weak-limit/post-last-zero identification. These remain explicit; the older general description of the entire bridge as written implementation was too broad. In particular the stronger setwise convergence route is an implementation choice, not a necessary premise of every possible conditioned-law proof. No further prover round or worker invention is assigned under operator18:55.

Exact existing types, namespace `MatedCRT.Sec1`, CanonicalEntranceKernels.lean:299-304 and309-312:

```lean
def ConditionedDriftFDDPremise {Ω : Type*} [MeasurableSpace Ω] (d : ℝ)
    (X : ℝ → Ω → ℝ) (P : ℝ → Measure Ω) : Prop :=
  ∀ x : ℝ, 0 < x → ∀ (n : ℕ) (τ : Fin n → ℝ), StrictMono τ → (∀ i, 0 < τ i) →
    ∀ A : Set (Fin n → ℝ), MeasurableSet A →
      P x {ω | (fun i => X (τ i) ω) ∈ A} =
        ∫⁻ y in A ∩ positiveOrthant n, ENNReal.ofReal (conditionedChainDensity d n 0 x τ y)

def ConditionedDriftChainDomination (d : ℝ) (n : ℕ) (τ : Fin n → ℝ) : Prop :=
  ∃ bound : (Fin n → ℝ) → ℝ, Integrable bound (volume.restrict (positiveOrthant n)) ∧
    ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ y ∈ positiveOrthant n,
      |conditionedChainDensity d n 0 x τ y| ≤ bound y
```

Consumer `tendsto_fdd_setwise_entrance`:321-328 explicitly takes both Props and only yields convergence of real-valued finite-dimensional event probabilities. It is not a proof of path weak convergence, normalization or post-last-zero identification.

The report's remaining conservation/entrance-normalization steps are not consumed by that theorem; their exact proposed Step types, in the same namespace with MeasureTheory/Set notation, are:

```lean
def ConditionedDriftConservationStep : Prop :=
  ∀ d t x : ℝ, 0 < d → 0 < t → 0 < x →
    (∫ y in Set.Ioi (0 : ℝ), conditionedDriftDensity d t x y) = 1

def EntranceDriftNormalizationStep : Prop :=
  ∀ d t : ℝ, 0 < d → 0 < t →
    (∫ y in Set.Ioi (0 : ℝ), entranceDriftDensity d t y) = 1
```

The final held identification has the existing exact type below (namespace `MatedCRT.Proposed`, Proposed/DuplantierMillerSheffieldCone2014.lean:116). This is a conditional source-admission/bridge record; the cached DMS Remark4.4 supplies the post-last-zero construction, not literally the repository's delta-weak-limit predicate. Do not promote the combined attribution as a verbatim cited result.

```lean
def DMS14Remark44PostLastZeroLaw : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (F : Ω → MarkovProcess.ContinuousPath ℝ),
      IsBrownianReal B P → Measurable F →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        F ω t = dmsPostLastZeroPath (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (fun s => B s ω) t) →
      MatedCRT.IsBMConditionedPositive (MatedCRTHarmonic.MatedCRT.lqgQ γ - γ) (P.map F)

```

Consumers CanonicalConeIdentification.lean:1029/1048 and CanonicalBrownianPathAssembly remain conditional. Actual lateral-coordinate measurability/law work is independent and current/queued. The canonical field, represented-circle, clock and mating conclusions remain open.


## Lead2026-11-09 lateral circles: measurable arrays versus laws

0c49c79 LateralCircleMeasurability.lean passes strict source and main-export axiom checks. It identifies lateral circle coordinates with the angular-integral formula, supplies their a.e. measurability including circles through zero, and constructs measurable countable lateral arrays with simultaneous a.s. recovery and pullback. The through-zero integrability exports retain the explicit RadialLogMajorant premise (:40); map_lateralArray_eq_of_lateral_law retains the actual law identity, and lateralArray_law_of_isQuantumCone consumes IsQuantumCone.lateral_law. Measurability does not establish that law.

The report's R1/R2 are written implementation remaining, not new WRITTEN-PROOF-NEEDED requests: audited env-steps:243-255 explicitly gives Brownian Gaussian/reflection bounds plus Borel--Cantelli, the resulting logarithmic radial envelope, bounded-annulus continuity and logarithmic angular integrability. BrownianSublinear/RadialLocalIntegrability supply checked conditional and deterministic components. The actual cone radial-law/path transfer and pairing-integrability specialization remain to implement; none is silently discharged here. Canonical lateral-law assembly is current, observable assembly queued. WPN-53 entrance-chain identification/domination/normalization and the held DMS weak-limit bridge remain unproved as recorded above.


## Lead2026-11-09 01:12 canonical lateral joint law; WPN-54 continuity boundary

Checked a8b5d10/adf8373 CanonicalLateralLawAssembly.lean:47-189 identifies the actual countable lateral array and its canonical whole-plane/cone law, passes radial independence to that array and proves its joint law with the cone radial process. The nine exports have only standard axioms. The joint-law theorem at168 retains IsProbabilityMeasure P, the supplied IsQuantumCone radial_law/lateral_law/indep clauses, and a whole-plane witness; it does not derive those clauses or establish a canonical field representation. The array can contain any countable family of admissible tests and circles. Full-observable assembly is current; written radial-log-majorant and pairing-integrability specialization is queued.

WRITTEN-PROOF-NEEDED WPN-54: q1 report B1 and module docstring:26-30 identify a stronger continuous lateral-circle path target. Under the existing cone hypotheses its exact proposed producer type, namespace MatedCRT.Sec1, is:

```lean
def LateralCircleContinuityFromConeStep : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsQuantumCone γ P hC hcirc →
    ∀ᵐ ω ∂P, ContinuousOn
      (fun p : ℝ × ℂ => lateralCircleCoord hcirc p.1 p.2 ω)
      (Ioi 0 ×ˢ univ)
```

The proposition is type-checked in fleet lead/checks/20261109-0101/WPN54Type.lean; no proof is supplied. Source boundary: audited env-steps.tex:243-255 proves the radial logarithmic bound, local/angle integrability and countable determination, but does not write the needed uniform-continuity argument across circles through zero. Finiteness of individual angular integrals does not prove this continuity. Consumer: none in the checked countable-array/joint-law results; this is an optional stronger path-version target, not a new premise of those results or of current observable assembly. If a later consumer requires it, carry this named Step explicitly. Operator18:55 forbids a further prover round; no worker is assigned to invent this argument. WPN-51/52/53 and held literature admission remain open; no numbered closure.


## Lead2026-11-09 01:39 whole-observable transport checked

5418076 CanonicalObservableAssembly.lean:171 proves simultaneous a.s. recovery of every admissible test/circle observable from the actual radial paths and lateral family. The measurable coneTransport at101/131 induces finite-family laws at205 and the full product-sigma-algebra observable law at245; supplied whole-plane witnesses and IsQuantumCone clauses specialize these at279/298/316. The joint law is derived using radial/lateral independence, not assumed as its conclusion. Fourteen exports pass strict lead lc and standard-axiom checks.

These are laws of the existing admissible observables. They do not construct a distribution-valued field representation, recover represented circles, identify the reference conditioned path law, or establish the full RescaledConeFieldStep. The algebraic identity uses equality off the single spatial origin and null exceptional angles; it does not claim finiteness of the totalized integrals. WPN-54 continuous lateral-circle paths is still optional/unconsumed. q1 now implements the separately written radial logarithmic majorant and pairing-integrability specialization; a reference-path observable-law specialization is queued, retaining any held DMS14Remark44PostLastZeroLaw premise explicitly. WPN-53 and source admission remain HELD. No numbered closure.
