# FIRST PASS: inputs of the composed main theorems 1.4 and 1.6 (q4)

Task fp-IDLA-main-composition (wave 2). Bookkeeping only: no new mathematics, no new frozen Props.
Lean: `MatedCRT/FirstPass/Main.lean` (`firstPassMain_1_4`, `firstPassMain_1_6`), axiom audit
`MatedCRT/FirstPass/Main/Axioms.lean`. Both theorems print only `propext`, `Classical.choice`, `Quot.sound`
(lb log 165200-82765). Commit 35d1440.

Both theorems have the same hypothesis list: their reductions `convergenceOfIDLA_of_steps` and
`convergenceOfDivSandpile_of_steps` (`MatedCRT/Steps/Sec1/Convergence.lean:206`, `:235`) take the same four inputs.

## Composition route

- Theorem 1.4 (`ConvergenceOfIDLAStmt`, Draft/Section1.lean:47) and Theorem 1.6 (`ConvergenceOfDivSandpileStmt`, :58):
  `convergenceOfIDLA_of_steps` / `convergenceOfDivSandpile_of_steps` with
  - `h81` (Proposition 8.1, `IDLAConstrainedConvergenceStmt`) = `firstPass_8_1` (`FirstPass/S1S2S8SA.lean:65`) applied to
    Propositions 4.2, 5.1, 6.1 (open) and to `h71`;
  - `h71` (Proposition 7.1, `DivSandpileUpperBoundStmt`) = `firstPass_7_1` (`FirstPass/S5S6S7.lean:94`), needing
    `hcone` = Theorem 2.3 (`firstPass_2_3`, `FirstPass/S1S2S8SA.lean:75`), `hconv` = Theorem 4.1
    (`firstPass_4_1`, `FirstPass/S3S4.lean:109`), `hgreen` = Lemma 3.3 (`firstPass_3_3`, `FirstPass/S3S4.lean:61`);
  - `hEnv` (environment scaling) = the frozen input `FrozenConeEnvironmentScaling` (`FirstPass/Frozen/S3S4.lean:38`);
  - `harmonicBallFamilyScalingStep` (proved, `Proofs/Sec1/HarmonicBallScaling.lean:100`);
  - `coneScaleRadiusStep_of_input hscale` (proved from `QuantumConeScalingInput`, `Proofs/Sec1/ConeScaleRadius.lean:308`);
  - `hT` = `ScaledClusterExitTimeStep` (open NEW step, below).

## EXTERNAL hypotheses (general mathematics, cited Draft statements, frozen first-pass inputs)

| Hypothesis | Prop / statement | file:line | source locator |
|---|---|---|---|
| `hscale` | `QuantumConeScalingInput` | `MatedCRT/External/QuantumCone.lean:19` | DMS14 Prop 4.13(i); eq:quantum-cone-scaling (paper line 458) |
| `hm` | `MepsScalingInput 𝒮` | `MatedCRT/External/SLE.lean:63` | BG20 eq. (1.8); eq:meps-scaling (paper line 733) |
| `hdeg` | `DegreeBoundInput 𝒮` | `MatedCRT/External/SLE.lean:70` | GMS19 Lemma 2.6 as quoted in Lemma 7.4 proof; eq:degree-bound (paper line 3071) |
| `h22` | `LQGMeasurePropertiesStmt` (Fact 2.2) | `MatedCRT/Draft/Section2.lean:39` | cited: DS11 Prop 2.1, SW16 (paper lines 490-492) |
| `h27` | `VolumeGrowthStmt` (Lemma 2.7) | `MatedCRT/Draft/Section2.lean:121` | cited: BG20 Lemma A.1 (paper line 658) |
| `h28` | `CellSizeEstimateStmt 𝒮` (Lemma 2.8) | `MatedCRT/Draft/Section2.lean:131` | cited: BG20 Lemma 2.4 (paper line 669) |
| `h29` | `CountingMeasureConvergenceStmt 𝒮` (Lemma 2.9) | `MatedCRT/Draft/Section2.lean:143` | cited: BG20 Lemma A.4 (paper line 680) |
| `h210` | `DegreeMeasureConvergenceStmt 𝒮` (Lemma 2.10) | `MatedCRT/Draft/Section2.lean:157` | cited: BG20 Corollary A.6 (paper line 698) |
| `h214` | `GreenKernelUpperBoundStmt 𝒮` (Lemma 2.14) | `MatedCRT/Draft/Section2.lean:191` | cited: BG20 Lemma 5.4 (paper line 843) |
| `h216` | `GreenKernelLowerBoundStmt 𝒮` (Lemma 2.16) | `MatedCRT/Draft/Section2.lean:212` | cited: BG20 Lemma 4.4 (paper line 867) |
| `h218` | `ExitTimeUpperBoundStmt 𝒮` (Lemma 2.18) | `MatedCRT/Draft/Section2.lean:239` | cited: BG20 Proposition 5.1 (paper line 916) |
| `hH` | `FrozenDiscreteHolderContinuityCorrected 𝒮` | `MatedCRT/FirstPass/Frozen/S3S4.lean:20` | GMS19 Theorem 3.9, Lemma 3.2 corrected form (Steps/Sec3/DiscretePotentialTightness.lean:71) |
| `hEnv` | `FrozenConeEnvironmentScaling 𝒮` (= `ConeEnvironmentScalingStep 𝒮`) | `MatedCRT/FirstPass/Frozen/S3S4.lean:38`; def at `MatedCRT/Steps/Sec1/Convergence.lean:67` | DMS14 Prop 4.13(i); eq:eta-scale-invariant (paper line 619); Fact 2.2; Brownian scaling of mating of trees (paper lines 3286-3293). Judgment call of q2, flagged in its frozen file |
| `h0` | `FPWholePlaneLQGExistence` | `MatedCRT/FirstPass/Frozen/S5S6S7.lean:17` | frozen; whole-plane GFF and LQG measure exist |
| `h1` | `FPConeWholePlaneWeylComparison` | `MatedCRT/FirstPass/Frozen/S5S6S7.lean:23` | frozen; **inbox: must be restated at field level (q3); this hypothesis will change** |
| `h2` | `FPWholePlaneLQGCoordinateChange` | `MatedCRT/FirstPass/Frozen/S5S6S7.lean:29` | frozen; scale and translation invariance of the whole-plane LQG measure |
| `hV` | `FPWholePlaneUpperVolumeTail` | `MatedCRT/FirstPass/Frozen/S5S6S7.lean:34` | frozen; `μ(B_s(z)) ≤ s^β` for `z ∈ B_3` |
| `hR` | `FPConeMeanZeroRestriction` | `MatedCRT/FirstPass/Frozen/S5S6S7.lean:39` | frozen; mean-zero restriction of eq:gff on circles |

Not yet frozen: `hEnv` (the existing def is reused), `hscale`, `hm`, `hdeg` (existing External defs). The cited Draft
statements (`h22`, `h27`-`h218`) are hypotheses as cited results, not PROVED-FP.

## Open Draft hypotheses (results not yet PROVED-FP)

| Hypothesis | Result | file:line | Needed by |
|---|---|---|---|
| `h24` | `ConeHarmonicBallsUpToFixedTimeStmt` (Lemma 2.4) | `MatedCRT/Draft/Section2.lean:66` | `firstPass_2_3` (q1) |
| `h25` | `ConeScaleInvarianceUpToFixedTimeStmt` (Lemma 2.5) | `MatedCRT/Draft/Section2.lean:88` | `firstPass_2_3` (q1); `hT` |
| `h34` | `IntegralConvergenceGreenFunctionStmt` (Lemma 3.4) | `MatedCRT/Draft/Section3.lean:109` | `firstPass_4_1`, `firstPass_3_3` |
| `h35` | `DiscreteDirichletProblemStmt` (Lemma 3.5) | `MatedCRT/Draft/Section3.lean:132` | `firstPass_4_1` (q2) |
| `h42` | `DivSandpileLowerBoundStmt` (Proposition 4.2) | `MatedCRT/Draft/Section4.lean:50` | `firstPass_8_1` |
| `h51` | `IDLALowerBoundStmt` (Proposition 5.1) | `MatedCRT/Draft/Section5.lean:27` | `firstPass_8_1` |
| `h61` | `IDLAUpperBoundStmt` (Proposition 6.1) | `MatedCRT/Draft/Section6.lean:31` | `firstPass_8_1` |

## Open NEW step

| Hypothesis | Step | file:line | Status |
|---|---|---|---|
| `hT` | `ScaledClusterExitTimeStep` (eq:btb-converge-to-inf) | `MatedCRT/Steps/Sec1/Convergence.lean:92`; paper `subsec:proof-of-idla`, corrected tex lines 3615-3660 | OPEN, see the gaps below |

The printed argument: `T^b` has the law of `𝒯` (scale invariance; the paper cites Lemma 2.6), and `𝒯` is strictly
positive, so `b T^b → ∞` in probability. Its existing Lean reduction `scaledClusterExitTimeStep_of_steps`
(`MatedCRT/Proofs/Sec1/ScaledClusterExitTime.lean:257`) takes `h25`, `hmeas` and `hgrow`, and two of them are not
printed in the paper, so `hT` is kept as an explicit open hypothesis:

- `hmeas` = `ConeFamilyAEMeasurableStep` (`MatedCRT/Steps/Sec2/ConeHarmonicBalls.lean:31`). Its docstring says it is
  "implicit in the paper ... neither stated nor proved there". Under the FIRST PASS rule it is a gap, not an input.
- `hgrow` = `ConeHarmonicBallStrictGrowthStep` (`MatedCRT/Steps/Sec2/ConeHarmonicBallsUpToFixedTime.lean:109`). Its
  docstring says "Not stated in the paper". The inbox forbids assuming strict growth. Its use is in
  `exists_rat_familyProcess` and `scaledClusterExitTimeStep_of_steps`.
- The printed law statement uses Lemma 2.6 (`ConeScaleInvarianceStmt`, `Draft/Section2.lean:108`, `firstPass_2_6`
  in `FirstPass/S1S2S8SA.lean`). The Lean reduction uses Lemma 2.5 instead. A proof of `hT` from Lemma 2.6 would
  need `firstPass_2_6` and `FrozenConeHarmonicBallFunctional`.
- Positivity of `𝒯 = sup {t > 0 : Λ_t ⊂ B_{ρ/3}}` (eq:cluster-stopping-time, corrected tex line 1848) is
  asserted by the printed proof. Printed Lemma 2.4 gives `T > 0` for the `B_{1/2}` exit time, not `Λ_t ⊂ B_{ρ/3}`
  for small `t`. Whether the conditions of Theorem 2.3 give it is unchecked.

## Replacement rule

When a firstPass theorem lands, re-run the composition: replace the matching open hypothesis by its theorem. Open
items that will disappear: `h24` and `h25` (q1, `firstPass_2_4`/`_2_5`), `h34` and `h35` (q2), `h42`, `h51`, `h61`
(not yet assigned to a firstPass theorem in the committed files). `hT` needs a NEW proof or a decision by the operator.
