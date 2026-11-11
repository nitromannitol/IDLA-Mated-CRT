# IDLA count ledger (numbered results)

One row per paper-owned numbered result of "Internal DLA on mated-CRT maps": the 42 rows of
docs/campaign/INVENTORY.tsv whose kind starts with `paper-owned` (results 1.4 to 8.1, and A.1 to A.4). The 14 rows of
kind `cited` are not counted here. Two extra rows (B6) give the counted forms that replace `firstPassMain_1_4` and
`firstPassMain_1_6` (audit R1 B6; those two are not counted: Main.lean:46, :74).

## Columns

- **Counted declaration**: the Lean name of the declaration the row counts; file:line is its location.
- **Kind**: `COUNTED (proof)` if the body is a tactic proof or a multi-step term. `DERIVED (file)` if the body is a
  one-line application of another theorem, located in `file`; the proof of the row is there.
- **Binder classes**: each explicit or implicit binder is classed by the file that defines its Prop:
  External, Frozen, Proposed, HB (HarmonicBalls/Draft), HBdef (other HarmonicBalls), model core
  (CertifiedReferenceModel and CertifiedReferenceModelCore, SLERef/Certified.lean:54 and SLERef/S5qe; class `model core`, lead li 2026-11-11 08:20), data (SpaceFillingSLEModel, `ν`), Def (MatedCRT/Defs), Step (a paper step outside
  Frozen, External and Proposed), DRAFT (MatedCRT/Draft, a Draft statement of this paper), Proof? (defined in a
  non-Frozen FirstPass or Proofs file, to be examined), std (Mathlib types). A binder whose Prop is an alias (its
  definition is one identifier) takes the class of the target when the target is Proposed, External, HB or DRAFT.
- **Flagged binders**: binders of class DRAFT, Step or Proof?. Under the literature-binder rule these must be replaced
  by theorems, except `hND` (LQGMeasureNonDyadicDilationPart), kept by operator ruling (tasks/li.md:196; req 104a). A
  row with `none` has no flagged binder.

## Open items for the lead

- **3.1 (audit m3).** `closed_3_1` concludes `DiscretePotentialTightnessCorrectedStmt`, the weak form; it is not
  counted. The names `closed_3_1_faithful` and `closed_3_1_countable` do not exist. The counted candidates are
  `firstPass_3_1_faithful` (FirstPass/S3c.lean:125, samplewise form, `DiscretePotentialTightnessPointwiseStmt`) and
  `firstPass_3_1_countable` (FirstPass/S3c/CountableFamilies.lean:97, countable families). The Draft
  (Draft/Section3.lean:42) has no `IsOpen D`; both candidates assume `IsOpen D`. The row uses the samplewise form. The
  Lead decision (lead li 2026-11-11 08:20): "domain" in the corrected tex l.981-986 ("every connected domain D ⊂ B_ρ") means an open connected set (the standard convention of potential theory), so `IsOpen D` is the printed hypothesis, not an addition; the "not in the paper" flag is dropped. The choice of the samplewise form is not changed by this decision.
- **1.4 and 1.6 (audit B6).** Counted as `closed_1_4_full` and `closed_1_6_full` (Closure/Final14Full.lean), the same
  binders as `firstPassMain_1_4_full` and `firstPassMain_1_6_full` (FirstPass/Main.lean, section Counted). Their only
  flagged binder is `hND`.
- **5.1 (audit m1).** `closed_5_1` binds `hcell`; the wrapper `closed_5_1_cellRewire` (Closure/CellRewire.lean) applies
  `adjacentCellsMeetAeStep` instead. Both still bind paper-step inputs (`h22`, `h24c`, `h27`, `hG15`); see the flags.
- **2.13 (audit m1).** `closed_2_13` binds `hcell`; the wrapper `closed_2_13_cellRewire` (Closure/CellRewire.lean)
  has no `hcell`.
- **Candidates not named in tasks/li.md**: 2.4, 2.5, 2.6, 2.17, 4.1, 4.2, 5.3, 6.1, 6.5, 7.1, 8.1, A.2, A.3, A.4. The
  generator picked the declaration with the name stated in the row; the lead to confirm each.
- **Draft binders in counted forms.** Several rows bind `VolumeGrowthStmt` (2.7, DRAFT `h27`) or
  `ExitTimeUpperBoundStmt` (2.18, DRAFT `h218`) or other Draft statements of this paper. The flags show which.

## Lead decisions of 2026-11-11 08:20 and operator items

- Row 3.1: `IsOpen D` is the printed hypothesis (domain = open connected set); the "not in the paper" flag is dropped
  (lead li 2026-11-11 08:20).
- Binder class `model core` for `CertifiedReferenceModel` and `CertifiedReferenceModelCore` (SLERef/Certified.lean:54,
  SLERef/S5qe); as now (lead li 2026-11-11 08:20).
- hE1 `ConeCircleLawUniqueStep` and hE2 `ConeReferenceExistsStep`: keep class Frozen (FirstPass/Frozen/S2i.lean:16, :27).
- Blockers owned by other workers, not worked here: h35 in 4.1, 4.2, 4.6 (z12, H35CorrectedRewire.lean); hG15 and h215
  (5.1, 5.4), h22 in 5.1 and 5.4, hnj, hcan, hcl in 4.2 (z9, Clean51And54.lean, Steps42.lean).

**FOR OPERATOR.**

- Literature binders hLit, hBM, hCC, hμ are class `HB Proposed` with locators S2VG/Literature.lean:44, :25, :32 and
  S4S6c/LitConeLQG68.lean:26. They are not staged in MatedCRT/External; staging is for the operator.
- `hcone : FrozenConeEnvironmentScaling 𝒮` is documented FALSE (Frozen/S3S4.lean:25-27; Frozen/S4S6c.lean:7). The counted
  4.1 form `firstPass_4_1_ownBinders_counted` (H35CorrectedRewire.lean:53) and the 4.2 copy `firstPass_4_2_final_h35c`
  (H35CorrectedRewire.lean:64) bind it. The 4.1 cone-law form `firstPass_4_1_coneLaw_h35c` binds
  `FrozenConeScalingLaw` instead (Frozen/S4S6c.lean:18). The 4.2 row needs the same replacement; the operator decides.
- 4.6 copy (z12): operator decision needed, add `h28` (or `hC`) to `firstPass_4_6_corrected`'s copy.
- Import clash (resolved, lead operator note li 2026-11-11 08:44): the two-argument `MatedCRT.ratPoint` (CircleAverage.lean:23) is renamed `MatedCRT.rationalGridPoint`; the one-argument `ratPoint` (LawCode.lean:24) keeps its name. Pure rename, no statement change.
- The Frozen binders `hexc` (FrozenBrownianOutwardExcursionAtExit) and `hcone` (FrozenConeScalingLaw) are added to the
  5.3 and 4.1 rows as inputs of `closed_3_5` and of the cone-law route; the operator to confirm.

## Existence of the coupling

Status: **PENDING TRUTH CHECK**. Existence is not proved in this repository; it is a cited literature input. It concerns
the valid environments `MatedCRTEnv.IsValid 𝒮 γ` (MatedCRT/Defs/Setting.lean:141).

- **Literature inputs named.** `IsMatingOfTreesCoupling` (LatticeProb module
  `LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling`; Setting.lean:7, :14, :157-165) is the coupling
  conjunct of `IsValid`. `MatedCRTEnv.IsValid` (Setting.lean:141) has the fields `isQuantumCone`, `isLQGMeasure`,
  `isSLE` and the coupling. `HasReferenceEnvironments 𝒮` (MatedCRT/FirstPass/SLERef/Reference.lean:42) gives valid
  environments for every γ ∈ (0,2); it is a conjunct of `CertifiedReferenceModel ν 𝒮` (SLERef/Certified.lean:54, :64).
- **Corrected-tex invocations** (paper/idla_mated_crt-corrected.tex):
  - l.179-180: "mating-of-trees bijections" as the analogy for the mated-CRT map, citing [ghs-mating-survey].
  - l.189-191: "Let h be the random distribution on C corresponding to a γ-quantum cone ... Let η be a whole-plane
    space-filling SLE, independent of h, with parameter κ = 16/γ² ∈ (4,∞)."
  - l.427 (Definition [def:quantum-cone], circle-average embedding) and l.466-472 (μ_h, the γ-LQG area measure).
  - l.611-612 and l.624: whole-plane space-filling SLE η, "see [ghs-mating-survey, Section 3.6]".
  - The paper has no numbered theorem stating existence of the coupling; the pair (h, η) is given by l.189-191 and
    l.611-632. Truth check for the lead: whether the pairing is the cited mating-of-trees input or a paper-own claim.
- **Proved here.** The GFF conjunct: `MatedCRT.GFFExistence.exists_harmonicBalls_isWholePlaneGFF`
  (MatedCRT/FirstPass/LPBridge/GFFExistence.lean:22, commit cf7f8cd): ∃ Ω, a measurable space, a probability P, hC,
  hcirc with `HarmonicBalls.IsWholePlaneGFF P hC hcirc`.
- **Open conjuncts of `IsValid`** (reports/z8.md (c)): (i) the radial law of `isQuantumCone`, `∃ ν, IsBMConditionedPositive
  (lqgQ γ - γ) ν ∧ P.map (radialProcess ∘ hcirc) = quantumConeRadialLaw γ ν` (locator MQ-li-8; no External Prop yet);
  (ii) `isLQGMeasure : IsLQGMeasure S.P γ S.hcirc S.μ`, cited via `FPWholePlaneLQGExistence`
  (FirstPass/Frozen/S5S6S7.lean:13).
- **Effect on the ledger.** The Draft statements quantify over all `S : MatedCRTEnv Ω` with `S.IsValid 𝒮 γ`, so the
  counted implications do not use an existence statement. Existence matters only for non-vacuity of the statements.

## Own-binder wrappers

File `MatedCRT/FirstPass/Closure/OwnBinderRewire.lean` (new). Each wrapper takes the binders of its counted form minus
the Draft binder, which is supplied by a cited or counted theorem:

- `VolumeGrowthStmt` (h27; Lemma 2.7, cited, BG20 Lemma A.1) by `volumeGrowthStmt_of_berestyckiGwynne hBG`
  (Proofs/Sec3/ConeBallMass.lean:17), with the binder `hBG : FrozenBerestyckiGwynneConeBallMass` (class Frozen,
  FirstPass/Frozen/S5Cited.lean:28).
- `ExitTimeUpperBoundStmt 𝒮` (h218; Lemma 2.18, cited, BG20 Prop 5.1) by `CertifiedReferenceModel.exitTimeUpperBound hC`
  (FirstPass/SLERef/Certified.lean:135), with the binder `hC : CertifiedReferenceModel ν 𝒮` (class core; defined in
  SLERef/Certified.lean:54, not in MatedCRT/External: staging for the lead).
- h33 and h35c of 3.7 by the wrappers of 3.3 and 3.5.

Wrappers (the rows above are updated): `closed_2_19_ownBinders` (line 39), `closed_3_3_ownBinders` (line 45), `closed_3_4_ownBinders` (line 51), `closed_3_5_ownBinders` (line 57), `closed_4_7_ownBinders` (line 65), `closed_4_8_corrected_ownBinders` (line 71), `closed_5_2_ownBinders` (line 79), `firstPass_2_17_ownBinders` (line 85), `firstPass_3_1_ownBinders` (line 92), and `firstPass_3_7_ownBinders` (line 103) (row 3.1 kept on `firstPass_3_1_faithful`). Second batch: `closed_2_2_ownBinders` (line 116), `closed_6_10_ownBinders` (line 123), `firstPass_2_4_ownBinders` (line 133), `firstPass_2_5_ownBinders` (line 153), `firstPass_2_6_ownBinders` (line 174), `firstPass_3_6_ownBinders` (line 197, partial), `firstPass_4_1_ownBinders` (line 211, partial). No flagged binder remains in the first ten; the partial ones keep the flags shown in their rows.

**Expected versus available (rows not yet wrapped).** Each line gives the Draft type a binder needs, the counted
theorem that concludes it, and the reason it is not wrapped.

- h22 `LQGMeasurePropertiesStmt` (2.5, 2.6, 4.2, 5.1): available `closed_2_2_lit` (Closure/Final22.lean:37), binders
  `hscale : QuantumConeScalingInput` (External/QuantumCone.lean:16), `hBG` (Frozen), `hND` (kept). Leaf wrapped as `closed_2_2_ownBinders` (line 116), used by 2.5 and 2.6.
- h23 `ConeHarmonicBallsStmt` (4.2) and hcone (7.1): available `closed_2_3_lit` (2.3), binders via h22 and `hND` (kept).
- h28 `CellSizeEstimateStmt`, h210 `DegreeMeasureConvergenceStmt`, h211 `RandomWalkToLBMStmt`, h214
  `GreenKernelUpperBoundStmt`, h216 `GreenKernelLowerBoundStmt`, h29 `CountingMeasureConvergenceStmt`: available as
  `CertifiedReferenceModel.*` (SLERef/Certified.lean:100, :107, :123, :127, :131, :103) on `hC`. Used inline by 3.6 and 4.1; no separate leaf wrapper.
- h44 `DiscreteLaplacianBoundCorrectedStmt` (5.3): `closed_4_4` (Closure/Section4.lean:22), binder `𝒮` only.
  h213 `MaximumPrincipleStmt` (5.3): `closed_2_13_cellRewire` (CellRewire.lean:21), binder `𝒮` only.
  h610 `IterativeBoundStmt` (6.1): `closed_6_10` (Section6.lean:30), binders h0, h2, hV, hR (Frozen). Wrapped as `closed_6_10_ownBinders` (line 123).
- **h35 (4.1, 4.2, 4.6), owner z12** (lead li 2026-11-11 08:20) `DiscreteDirichletProblemStmt 𝒮` (Draft/Section3.lean:132).
  Available: `DiscreteDirichletProblemCorrectedStmt 𝒮` (closed_3_5). The uncorrected Prop is concluded only by
  `Assembly/Main.lean:156` from `MainHypotheses`. z12 copies (H35CorrectedRewire.lean): `firstPass_4_1_coneLaw_h35c` (:39),
  `firstPass_4_2_final_h35c` (:64), `firstPass_4_1_ownBinders_h35c`, `firstPass_4_1_ownBinders_counted`. Used by 5.3 (h41) above.
- **BLOCKED h24** `ConeHarmonicBallsUpToFixedTimeStmt` (4.2). Available: `ConeHarmonicBallsUpToFixedTimeCanonicalStmt` (2.4).
- **BLOCKED h24c** `ConeHarmonicBallsUpToFixedTimeCorrectedStmt` (5.1; FirstPass/S2b.lean:43). No counted theorem concludes it.
- **BLOCKED hG15, h215, owner z9** (lead li 2026-11-11 08:20) `GreenFunctionCrudeBoundStmt 𝒮` (Draft/Section2.lean:201; cited 2.15). Expected: this Prop. `firstPass_4_1_ownBinders` (line 211) has h35 as its only Draft binder.
  Available: none (the only occurrences in MatedCRT are binders, e.g. `firstPass_5_4`, S5S6S7.lean:42). Blocks 5.1 and 5.4.
- **hLs (5.3), discharged** `ConeScaleInvarianceCodedStmt` (FirstPass/S2g/LawCoded.lean:20) by `coneScaleInvarianceCoded_ownBinders`
  (HLsRewire53.lean:46) = `firstPass_2_6_coded_of_globalFamilyFactor` (S2g/LawCoded.lean:33) applied to
  `coneGlobalFamilyFactor_ownBinders` (HLsRewire53.lean:35) = `coneGlobalFamilyFactor_proved` (S2i/GlobalFactor.lean:519) with
  `hcan`, `hcl`, `closed_2_2_ownBinders` (h22, keeps `hND`), `volumeGrowthStmt_of_berestyckiGwynne` (h27). Lead li 2026-11-11 08:20.
- **h41 (5.3), discharged** by `firstPass_4_1_coneLaw_ownBinders` (HLsRewire53.lean:59) = `firstPass_4_1_coneLaw_h35c`
  (H35CorrectedRewire.lean:39) with the core reference model `hC` and `closed_3_5` (input `hexc`, Frozen); cone-law input `hcone`
  (`FrozenConeScalingLaw`, Frozen/S4S6c.lean:18). Not the counted 4.1 form (`hcone` FALSE there, see FOR OPERATOR).
- **BLOCKED h51, h61, h71, h42** (6.1, 8.1): h51 needs `closed_5_1` (blocked by h24c, hG15); h61 needs `firstPass_6_1`
  (blocked by h51); h71 needs `firstPass_7_1` (blocked by hconv); h42 needs `firstPass_4_2_final` (blocked by h35, h24),
  or `Phase2Rewire.lean:338` (not examined this round).
- hconv (7.1), h41 (5.3): `firstPass_4_1` (blocked by h35). h37 (4.6): `firstPass_3_7_ownBinders` (blocked by h35 in 4.6).
- hE1 `ConeCircleLawUniqueStep`, hE2 `ConeReferenceExistsStep` (bound by `firstPass_2_5_canonical_p2`, `firstPass_2_6_corrected_p2`,
  and by the 5.3 route): **resolved** (lead li 2026-11-11 08:20): keep the class Frozen, as the file defines them
  (FirstPass/Frozen/S2i.lean:16, :27; reports/z9.md).

**Classification of the remaining paper-own and Proof? binders.**

| Binder | Prop (location) | Class | Source | Status |
|---|---|---|---|---|
| hND | `LQGMeasureNonDyadicDilationPart` | Step | cited input, not staged | kept by operator ruling (tasks/li.md:196; req 104a) |
| hLit | `MatedCRT.S2VG.LitExistence` (FirstPass/S2VG/Literature.lean:44) | HB Proposed (lead li 2026-11-11 08:20) | HarmonicBalls Proposed/LQG.lean (abbrev) | not staged in External: FOR OPERATOR |
| hBM | `LitWholePlaneBallMass` (FirstPass/S2VG/Literature.lean:25) | HB Proposed (lead li 2026-11-11 08:20) | HarmonicBalls Proposed/LQG.lean:154; Ding-Gwynne arXiv:1807.01072 Lemma 3.8 | not staged in External: FOR OPERATOR |
| hCC | `LitCoordChange` (FirstPass/S2VG/Literature.lean:32) | HB Proposed (lead li 2026-11-11 08:20) | HarmonicBalls Proposed/LQG.lean (abbrev) | not staged in External: FOR OPERATOR |
| hμ | `LitQuantumConeLQGMeasureExistence` (FirstPass/S4S6c/LitConeLQG68.lean:26) | HB Proposed (lead li 2026-11-11 08:20) | not checked this round | not staged in External: FOR OPERATOR |
| hBE | `FrozenOneSidedBoundaryContinuity 𝒮` (FirstPass/S3i/Frozen.lean:44) | Proof? | not checked this round | examine (3.6) |
| hnj | `StrictGapFixedTimeUnionStep 𝒮` (FirstPass/S4d/StrictGapReduction.lean:35) | Step | paper-own step | needs proof (4.2) |
| hcan | `ConeCanonicalHalfBallStep` (FirstPass/S2g.lean:81) | Step | paper-own step | needs proof (4.2); owner z9 (lead li 2026-11-11 08:20); kept as binder in 5.3 (HLsRewire53.lean) |
| hcl | `ConeHalfBallClosureInsideStep` (Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18) | Step | paper-own step | needs proof (4.2); owner z9; kept as binder in 5.3 (HLsRewire53.lean) |
| hLs | `ConeScaleInvarianceCodedStmt` (FirstPass/S2g/LawCoded.lean:20) | paper-own (coded 2.6) | paper-own | discharged in 5.3: `coneScaleInvarianceCoded_ownBinders` (HLsRewire53.lean:46); its inputs hcan, hcl, hND stay |
| h24c | `ConeHarmonicBallsUpToFixedTimeCorrectedStmt` (FirstPass/S2b.lean:43) | paper-own (corrected 2.4) | paper-own | blocked (5.1) |

## Table

Generated by the z1 ledger script from the repository (`/tmp/z1s/ledger.py` on the work machine). It is a snapshot;
regenerate after any change to a counted declaration.

| Result | Counted declaration | file:line | Kind | Binder classes | Flagged binders | Note |
|---|---|---|---|---|---|---|
| 1.4 | `closed_1_4_full` | MatedCRT/FirstPass/Closure/Final14Full.lean:21 | DERIVED (FirstPass/Closure/Final14Composed.lean) | External 4 Frozen 30 HB 13 Proposed 1 Step 1 core 1 data 2 | Step:hND | Audit B6 accepted (lead, 05:35 UTC). firstPassMain_1_4 (FirstPass/Main.lean:46) is not counted. |
| 1.4n | `closed_1_4_full_noSC` | MatedCRT/FirstPass/Closure/HSCRewire.lean:30 | DERIVED (from `closed_1_4_full`, row 1.4) | row 1.4 binders minus hSC, hSCHB | none | hSC and hSCHB removed, discharged from hI2 (Frozen, present); no binder added. |
| 1.6 | `closed_1_6_full` | MatedCRT/FirstPass/Closure/Final14Full.lean:89 | DERIVED (FirstPass/Closure/Final14Composed.lean) | External 4 Frozen 30 HB 13 Proposed 1 Step 1 core 1 data 2 | Step:hND | Audit B6 accepted (lead, 05:35 UTC). firstPassMain_1_6 (FirstPass/Main.lean) is not counted. |
| 1.6n | `closed_1_6_full_noSC` | MatedCRT/FirstPass/Closure/HSCRewire.lean:98 | DERIVED (from `closed_1_6_full`, row 1.6) | row 1.6 binders minus hSC, hSCHB | none | hSC and hSCHB removed, discharged from hI2; no binder added. |
| 2.3 | `closed_2_3_lit` | MatedCRT/FirstPass/Closure/Final23.lean:43 | COUNTED (proof) | External 1 Frozen 13 HB 13 Proposed 1 Step 1 | Step:hND | closed_2_3_lit: h22 is closed_2_2_lit; hND is the operator-staged literature input (req 104a). |
| 2.3n | `closed_2_3_lit_noSC` | MatedCRT/FirstPass/Closure/HSCRewire.lean:166 | DERIVED (from `closed_2_3_lit`, row 2.3) | row 2.3 binders minus hSCHB | none | hSCHB removed, discharged from hI2HB; no binder added. |
| 2.4 | `firstPass_2_4_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:133 | DERIVED (own-binder wrapper of `firstPass_2_4_canonical_p2`) | Frozen 7 HB 12 | none | Own-binder wrapper: h27 by `volumeGrowthStmt_of_berestyckiGwynne hBG`. Route of the h24 input (Phase2Rewire). Not named in tasks/li.md; to be confirmed by the lead. |
| 2.5 | `firstPass_2_5_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:153 | DERIVED (own-binder wrapper of `firstPass_2_5_canonical_p2`) | External 1 Frozen 9 HB 12 Step 1 | Step:hND (kept by operator ruling; enters with `closed_2_2_ownBinders`) | Own-binder wrapper: h27 by hBG; h22 by `closed_2_2_ownBinders` (hscale, hBG, hND). hE1, hE2 kept (classes Frozen/HB as in the ledger). |
| 2.6 | `firstPass_2_6_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:174 | DERIVED (own-binder wrapper of `firstPass_2_6_corrected_p2`) | External 1 Frozen 9 HB 12 Step 1 | Step:hND (kept by operator ruling; enters with `closed_2_2_ownBinders`) | Own-binder wrapper as 2.5. Candidate; not named in tasks/li.md; to be confirmed by the lead. |
| 2.13 | `closed_2_13` | MatedCRT/FirstPass/Closure/Section2.lean:33 | DERIVED (FirstPass/S1S2S8SA.lean) | Frozen 1 data 1 | none | Audit m1: binds hcell (FrozenAdjacentCellsMeetAe). Wrapper closed_2_13_cellRewire (Closure/CellRewire.lean). |
| 2.17 | `firstPass_2_17_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:85 | DERIVED (own-binder wrapper of `firstPass_2_17`) | Frozen 1 | none | Own-binder wrapper: h27 by `volumeGrowthStmt_of_berestyckiGwynne hBG` (Proofs/Sec3/ConeBallMass.lean:17; hBG Frozen). |
| 2.19 | `closed_2_19_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:39 | DERIVED (own-binder wrapper of `closed_2_19`) | core 1 Frozen 1 data 2 | none | Own-binder wrapper of closed_2_19 (Closure/Section2.lean:40): h27 supplied by the cited volume-growth input (hBG Frozen). |
| 3.1 | `firstPass_3_1_faithful` | MatedCRT/FirstPass/S3c.lean:125 | COUNTED (proof) | DRAFT 2 External 1 Frozen 1 data 1 | DRAFT:h27, DRAFT:h218 | Audit m3. Own-binder wrapper `firstPass_3_1_ownBinders` (MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:92) removes h27 and h218 (h218 by `CertifiedReferenceModel.exitTimeUpperBound`); row kept on `firstPass_3_1_faithful` per lead. Concludes `DiscretePotentialTightnessPointwiseStmt 𝒮` (S3c.lean:100; samplewise form, fidelity fix §1.3), not the Draft `DiscretePotentialTightnessStmt 𝒮` (Draft/Section3.lean:42). Corrected tex lemma:discrete-potential-tightness (l.981-986): "every connected domain D ⊂ B_ρ"; the paper does not say D is open. `IsOpen D` is the printed hypothesis: "domain" = open connected set (lead li 2026-11-11 08:20; S3c.lean:105; the Draft has IsConnected only). closed_3_1 (weak form, DiscretePotentialTightnessCorrectedStmt) is not counted; closed_3_1_faithful / closed_3_1_countable do not exist. Alternative: firstPass_3_1_countable (S3c/CountableFamilies.lean:97). |
| 3.3 | `closed_3_3_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:45 | DERIVED (own-binder wrapper of `closed_3_3`) | core 1 Frozen 1 data 2 | none | Own-binder wrapper of closed_3_3 (Closure/Section3.lean:43): h27 supplied as in the 2.19 row. |
| 3.4 | `closed_3_4_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:51 | DERIVED (own-binder wrapper of `closed_3_4`) | core 1 Frozen 1 data 2 | none | Own-binder wrapper of closed_3_4 (Closure/Section3.lean:36): h27 supplied as in the 2.19 row. |
| 3.5 | `closed_3_5_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:57 | DERIVED (own-binder wrapper of `closed_3_5`) | core 1 Frozen 2 data 2 | none | Own-binder wrapper of closed_3_5 (Closure/Section3.lean:66): h27 supplied; hexc (FrozenBrownianOutwardExcursionAtExit) stays. |
| 3.6 | `firstPass_3_6_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:197 | DERIVED (own-binder wrapper of `firstPass_3_6_closed`) | data 2 core 1 External 1 Frozen 2 Proof? 1 | Proof?:hBE | Own-binder wrapper (partial): h211 and h28 by the CertifiedReferenceModel projections on hC. hBE (FrozenOneSidedBoundaryContinuity, FirstPass/S3i/Frozen.lean:44) stays. Operator note 13:12 UTC: counted via firstPass_3_6_closed. |
| 3.7 | `firstPass_3_7_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:103 | DERIVED (own-binder wrapper of `firstPass_3_7_corrected`) | External 1 core 1 Frozen 3 data 2 | none | Own-binder wrapper of firstPass_3_7_corrected (S3f.lean:29): h27 and h218 (core) and h33, h35c (via 3.3 and 3.5 wrappers). |
| 4.1 | `firstPass_4_1_coneLaw_ownBinders` | MatedCRT/FirstPass/Closure/HLsRewire53.lean:64 | DERIVED (own-binder wrapper of `firstPass_4_1_coneLaw_h35c`, MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean:48, commit e7a5833) | data 2 core 1 Frozen 3 (hBG, hexc, hcone) | none | Cone-law form (lead li 2026-11-11 08:20). hcone can be the projection `hC.frozenConeScaling` (conjunct 8 of CertifiedReferenceModel); not applied here. |
| 4.2 | `closed_4_2_clean` | MatedCRT/FirstPass/Closure/Chain42ConeLaw.lean:116 | COUNTED (proof, cone-law form; hcone FrozenConeScalingLaw, not the false FrozenConeEnvironmentScaling) | Frozen: hstd hCentre hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hconf hI2 (FrozenLQGVolumeGrowthAllScales) hK hloc hE hFL hBG hND hrescale hE1 hE2 hscale hpc hsmp hwmp hpole hG hcone; cited: h28 (Lemma 2.8), h210 h34 h214 h218 hH h33 h23 hm; corrected: h35c (Lemma 3.5), h24c (Lemma 2.4) | Step:hND (kept by operator ruling) | Lead li 2026-11-11 09:13: row 4.2 DONE. |
| 4.3 | `closed_4_3` | MatedCRT/FirstPass/Closure/Section4.lean:18 | DERIVED (FirstPass/S3S4.lean) | data 1 | none |  |
| 4.4 | `closed_4_4` | MatedCRT/FirstPass/Closure/Section4.lean:22 | DERIVED (FirstPass/S3S4.lean) | data 1 | none |  |
| 4.5 | `closed_4_5` | MatedCRT/FirstPass/Closure/Section4.lean:27 | DERIVED (FirstPass/S3S4.lean) | data 1 | none |  |
| 4.6 | `firstPass_4_6_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean:74 | DERIVED (`firstPass_4_6_corrected`, MatedCRT/FirstPass/S3S4.lean:102, with h28 and the corrected Lemma 3.5 input h35c, commit e7a5833) | DRAFT 5 (h27 h218 h28 h35c h37) External 1 (hm) Frozen 1 (hH) data 2 | DRAFT:h27, DRAFT:h218, DRAFT:h28, DRAFT:h35c, DRAFT:h37 | h28 (CellSizeEstimateStmt) is the bridge input added in e7a5833; the DRAFT binders are open (h37 blocked, reports/z12.md). |
| 4.7 | `closed_4_7_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:65 | DERIVED (own-binder wrapper of `closed_4_7`) | core 1 Frozen 1 data 2 | none | Own-binder wrapper of closed_4_7 (Closure/Section4.lean:31): h27 supplied. |
| 4.8 | `closed_4_8_corrected_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:71 | DERIVED (own-binder wrapper of `closed_4_8_corrected`) | core 1 Frozen 2 data 2 | none | Own-binder wrapper of closed_4_8_corrected (S4x8.lean:45): h27 supplied; hexc stays. |
| 5.1 | `closed_5_1_clean` | MatedCRT/FirstPass/Closure/Clean51And54.lean:40 | COUNTED (proof) | External 1 Frozen 21 HB 14 Step 1 core 1 data 2 | Step:hND (kept by operator ruling) | DRAFT 0. Own-binder wrapper of `closed_5_1_ownBinders` (H24cBridge.lean:89): h22 by `closed_2_2_ownBinders` (hBG Frozen, hscale External, hND Step), hG15 by `greenFunctionCrudeBound_of_canonical` from Frozen hcanon (BG20 Lemma 5.6). Lead li 2026-11-11 08:20. Owner z9 (reports/z9.md, commit a1339bd). |
| 5.2 | `closed_5_2_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:79 | DERIVED (own-binder wrapper of `closed_5_2`) | core 1 Frozen 1 data 2 | none | Own-binder wrapper of closed_5_2 (Closure/Section5.lean:17): h27 supplied. |
| 5.3 | `closed_5_3_clean` | MatedCRT/FirstPass/Closure/HLsRewire53.lean:109 | COUNTED (proof) | core 1 data 2 External 1 (hscale) Step 1 (hND) Frozen 11 (hBG hE1 hE2 hF3 hfirst hstd hCentre hconf hK hE hFL) HB 11 (hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hloc hI2) | Step:hND (kept by operator ruling) | Discharged: hcan and hcl (Closure/Steps42.lean:40, :106); hSC by `frozenClusterStrongCompatibility_of_volumeGrowth hI2` (Closure/HSCDerived.lean:19; class 'derived from hI2, HB exhaustion route; differs from the printed proof of Lemma 5.8'); hcl class 'derived in Lean (S5r/ClosureInside.lean:24)'; hM := hC.mepsScaling; hcone := hC.frozenConeScaling; hF, hmin, hF1, hG, hexc by committed proofs (LPBridge/InRepoProofs.lean:35, LPBridge/MinimumPrinciples.lean:30, LPBridge/UniversalMeasurability.lean:18, HBRewire.lean:40, LPBridge/BrownianOutwardExcursion.lean:113). Predecessor: `closed_5_3_ownBinders` (HLsRewire53.lean:73, ecfbc55). Build of the bb7e129 form: BUILD OK (logs/lb/093821-2900417.log). hI2 not taken from `lqgVolumeGrowthAllScalesStmt_litI2` (S2VG/Literature.lean:58), which needs five literature inputs. Lead li 2026-11-11 08:58. |
| 5.4 | `closed_5_4_clean` | MatedCRT/FirstPass/Closure/Clean51And54.lean:73 | DERIVED (FirstPass/S5S6S7.lean:42) | core 1 data 2 Frozen 1 | none | DRAFT 0. h215 from hcanon as in 5.1; h216 and h29 are projections of core hC (no counted row for Lemmas 2.9, 2.16). Owner z9 (commit a1339bd). |
| 6.1 | `firstPass_6_1_corrected` | MatedCRT/FirstPass/S2g/Assembly2456.lean:31 | DERIVED (FirstPass/S2g/Section6Canonical.lean) | DRAFT 3 Frozen 10 HB 13 data 1 | DRAFT:h610, DRAFT:h51, DRAFT:h27 |  |
| 6.4 | `firstPass_6_4_uniform` | MatedCRT/FirstPass/S6p.lean:213 | COUNTED (proof) | Frozen 4 | none | Operator note 05:50 UTC: counted via firstPass_6_4_uniform (S6p.lean). |
| 6.5 | `firstPass_6_5_uniform` | MatedCRT/FirstPass/S6q.lean:26 | DERIVED (FirstPass/S6p.lean) | Frozen 3 | none | Candidate; the uniform form firstPass_6_5_uniform is named in tasks/li.md. |
| 6.7 | `firstPass_6_7` | MatedCRT/FirstPass/LIClosed68Y.lean:30 | DERIVED (FirstPass/S4S6c/ShellChainCGRCYSqHalf68.lean) | Frozen 1 Proof? 4 Proposed 1 core 1 data 2 | Proof?:hLit, Proof?:hBM, Proof?:hCC, Proof?:hμ | Operator note 22:13 UTC: counted (FAITHFUL) in FirstPass/LIClosed68Y.lean. |
| 6.8 | `firstPass_6_8` | MatedCRT/FirstPass/LIClosed68Y.lean:40 | DERIVED (FirstPass/S4S6c/ShellChainCGRCYSqHalf68.lean) | Frozen 1 Proof? 4 Proposed 1 core 1 data 2 | Proof?:hLit, Proof?:hBM, Proof?:hCC, Proof?:hμ | Operator note 22:13 UTC: counted (FAITHFUL) in FirstPass/LIClosed68Y.lean. |
| 6.9 | `firstPass_6_9` | MatedCRT/FirstPass/LIClosed68Y.lean:51 | DERIVED (FirstPass/S4S6c/ShellChainCGRCYSqHalf68.lean) | Frozen 1 Proof? 4 Proposed 1 core 1 data 2 | Proof?:hLit, Proof?:hBM, Proof?:hCC, Proof?:hμ | Operator note 22:13 UTC: counted (FAITHFUL) in FirstPass/LIClosed68Y.lean. |
| 6.10 | `closed_6_10_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:123 | DERIVED (own-binder wrapper of `closed_6_10`) | core 1 Frozen 5 data 2 | none | Own-binder wrapper: h27 by hBG; Frozen h0, h2, hV, hR stay. |
| 7.1 | `firstPass_7_1` | MatedCRT/FirstPass/S5S6S7.lean:98 | DERIVED (Proofs/Sec7/DivSandpileUpperBound/ShellIterationOfMeshScaling.lean) | DRAFT 8 External 2 Frozen 4 data 1 | DRAFT:hcone, DRAFT:h216, DRAFT:h27, DRAFT:h28, DRAFT:h29, DRAFT:h218, DRAFT:hconv, DRAFT:hgreen |  |
| 7.2 | `closed_7_2` | MatedCRT/FirstPass/Closure/Section7.lean:18 | DERIVED (FirstPass/S5S6S7.lean) | core 1 data 2 | none |  |
| 7.3 | `closed_7_3` | MatedCRT/FirstPass/Closure/Section7.lean:23 | DERIVED (FirstPass/S5S6S7.lean) | data 1 | none |  |
| 8.1 | `firstPass_8_1` | MatedCRT/FirstPass/S1S2S8SA.lean:65 | DERIVED (Steps/Sec8/IDLAConstrainedConvergence.lean) | DRAFT 4 data 1 | DRAFT:h42, DRAFT:h51, DRAFT:h61, DRAFT:h71 |  |
| A.1 | `discreteDivergenceTheorem` | MatedCRT/Proofs/SecA/DiscreteDivergence.lean:54 | COUNTED (proof) |  | none |  |
| A.2 | `discreteBasicPropertiesGeneral` | MatedCRT/Proofs/SecA/Statements.lean:62 | DERIVED (Steps/SecA/DiscreteObstacle.lean) |  | none | Name not verified; located by the generator. |
| A.3 | `discreteLaplacianBoundGeneral` | MatedCRT/Proofs/SecA/Statements.lean:66 | DERIVED (Steps/SecA/DiscreteObstacle.lean) |  | none | Name not verified; located by the generator. |
| A.4 | `discreteConservationOfMassGeneral` | MatedCRT/Proofs/SecA/Statements.lean:71 | DERIVED (Steps/SecA/DiscreteObstacle.lean) |  | none |  |
| B6 | `firstPassMain_1_4_full` | MatedCRT/FirstPass/Main.lean:114 | DERIVED (FirstPass/Closure/Final14Full.lean) | External 4 Frozen 30 HB 13 Proposed 1 Step 1 core 1 data 2 | Step:hND |  |
| B6 | `firstPassMain_1_6_full` | MatedCRT/FirstPass/Main.lean:174 | DERIVED (FirstPass/Closure/Final14Full.lean) | External 4 Frozen 30 HB 13 Proposed 1 Step 1 core 1 data 2 | Step:hND |  |
| m1 | `closed_2_13_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean:21 | DERIVED (FirstPass/Closure/Section2.lean) | data 1 | none |  |
| m1 | `closed_5_1_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean:30 | DERIVED (FirstPass/Closure/Prop51.lean) | DRAFT 3 External 1 Frozen 19 HB 14 Proof? 1 core 1 data 2 | DRAFT:h27, DRAFT:h22, Proof?:h24c, DRAFT:hG15 |  |
