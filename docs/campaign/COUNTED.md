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
  External, Frozen, Proposed, HB (Harmonic-Balls-LQG/HarmonicBalls/Draft), HBdef (other HarmonicBalls), model core
  (CertifiedReferenceModel and CertifiedReferenceModelCore, SLERef/Certified.lean:54 and FirstPass/S5qe.lean:33; class `model core`, lead li 2026-11-11 08:20), data (SpaceFillingSLEModel, `ν`), Def (MatedCRT/Defs), Step (a paper step outside
  Frozen, External and Proposed), DRAFT (MatedCRT/Draft, a Draft statement of this paper), Proof? (defined in a
  non-Frozen FirstPass or Proofs file, to be examined), std (Mathlib types). A binder whose Prop is an alias (its
  definition is one identifier) takes the class of the target when the target is Proposed, External, HB or DRAFT.
- **Flagged binders**: binders of class DRAFT, Step or Proof?. Under the literature-binder rule these must be replaced
  by theorems, except `hND` (LQGMeasureNonDyadicDilationPart), kept by operator ruling (tasks/li.md:196; req 104a). A
  row with `none` has no flagged binder.

## Open items for the lead

- **3.1 (audit m3).** `closed_3_1` concludes `DiscretePotentialTightnessCorrectedStmt`, the weak form; it is not
  counted. Two earlier candidate names for 3.1 were never declared and are not used. The counted candidates are
  `firstPass_3_1_faithful` (FirstPass/S3c.lean:125, samplewise form, `DiscretePotentialTightnessPointwiseStmt`) and
  `firstPass_3_1_countable` (FirstPass/S3c/CountableFamilies.lean:97, countable families). The Draft
  (Draft/Section3.lean:42) has no `IsOpen D`; both candidates assume `IsOpen D`. The row uses the samplewise form. The
  Lead decision (lead li 2026-11-11 08:20): "domain" in the corrected tex l.981-986 ("every connected domain D ⊂ B_ρ") means an open connected set (the standard convention of potential theory), so `IsOpen D` is the printed hypothesis, not an addition; the "not in the paper" flag is dropped. The choice of the samplewise form is not changed by this decision.
- **1.4 and 1.6 (audit B6).** Counted as `closed_1_4_lp_noSC_noSup` and `closed_1_6_lp_noSC_noSup` (Closure/LssDerived.lean:54 and :95; MQ-li-4), which apply `closed_1_4_lp_noSC` and `closed_1_6_lp_noSC` (Closure/Clean14And16LPNoSC.lean;
  rule 1, see the section on LP forms). The earlier counted forms are `closed_1_4_full` and `closed_1_6_full`
  (Closure/Final14Full.lean), the same binders as `firstPassMain_1_4_full` and `firstPassMain_1_6_full` (FirstPass/Main.lean,
  section Counted). Their only flagged binder is `hND`.
- **5.1 (audit m1).** `closed_5_1` binds `hcell`; the wrapper `closed_5_1_cellRewire` (Closure/CellRewire.lean) applies
  `adjacentCellsMeetAeStep` instead. Both still bind paper-step inputs (`h22`, `h24c`, `h27`, `hG15`); see the flags.
- **2.13 (audit m1).** `closed_2_13` binds `hcell`; the wrapper `closed_2_13_cellRewire` (Closure/CellRewire.lean)
  has no `hcell`.
- **Candidates not named in tasks/li.md**: 2.4, 2.5, 2.17, 4.1, 4.2, 5.3, 6.1, 7.1, 8.1, A.2, A.3, A.4 (2.6 and 6.5 are confirmed by the lead, p2-ledger-lp-counted-status). The
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
- `hcone : FrozenConeEnvironmentScaling 𝒮` (Frozen/S3S4.lean:27) holds for every model with the three SLE closure inputs. The counted
  4.1 form `firstPass_4_1_ownBinders_counted` (H35CorrectedRewire.lean:62) and the 4.2 copy `firstPass_4_2_final_h35c`
  (H35CorrectedRewire.lean:64) bind it. The 4.1 cone-law form `firstPass_4_1_coneLaw_h35c` binds
  `FrozenConeScalingLaw` instead (Frozen/S4S6c.lean:18). The 4.2 row needs the same replacement; the operator decides.
- 4.6 copy (z12): operator decision needed, add `h28` (or `hC`) to `firstPass_4_6_corrected`'s copy.
- Import clash (resolved, lead operator note li 2026-11-11 08:44): the two-argument `MatedCRT.ratPoint` (CircleAverage.lean:23) is renamed `MatedCRT.rationalGridPoint`; the one-argument `ratPoint` (LawCode.lean:24) keeps its name. Pure rename, no statement change.
- The Frozen binders `hexc` (FrozenBrownianOutwardExcursionAtExit) and `hcone` (FrozenConeScalingLaw) are added to the
  5.3 and 4.1 rows as inputs of `closed_3_5` and of the cone-law route; the operator to confirm.

## MQ-li-4 counted-form switch (lead decision, operator note 13:14 UTC)

Rows 1.4, 1.4n, 1.6, 1.6n, B6 (1.4 and 1.6), 5.1, 5.1lp, m1 (5.1 cellRewire), 6.1, 6.1lp, 8.1 and 8.1lp count the `_noSup` wrapper of their declaration in MatedCRT/FirstPass/Closure/LssDerived.lean (commit 3588558d). Each wrapper is its base declaration with `hsup : FrozenLeastSupersolutionMemCone 𝒮` replaced by `h27 : VolumeGrowthStmt` (DRAFT, Draft/Section2.lean:121), except `closed_5_1_cellRewire_noSup`, which drops `hsup` (h27 was already a binder). The base name stays as the "applies" chain entry. Under rule 1 the `_noSup` form is not a strict sub-list of its base (one binder swapped); it is counted by the lead decision. The Frozen count drops by one, the DRAFT count rises by one (h27, flagged), except m1 (Frozen drops by one). `FrozenLeastSupersolutionMemCone` is DERIVED (FROZEN-PROVENANCE.md, row 72).

## LP forms under the counting rule (p2-ledger-lp-counted-status, 2026-11-11)

Rule 1 (lead): an `_lp` or `_noSC` form is the counted form of its row iff its binder list is a strict sub-list of the base form's binder list (same names and types, same conclusion). If no binder is discharged, the form is an alias and the base row stays counted (DUPLICATES.md D11). If a binder is added or strengthened, the form is an LP alternative and is not counted. The check compared the binder lists (names and type text) and the conclusions of the Lean signatures at HEAD 77939262 (re-checked after 0a692f2d; the only cited file changed in between is Clean2xLP.lean, by a docstring edit, and its line numbers and binder lists are unchanged).

| Row | LP form (file:line) | Base form compared (file:line) | Outcome |
|---|---|---|---|
| 1.4 | `closed_1_4_lp_noSC` (Clean14And16LPNoSC.lean:24); `closed_1_4_lp` (Final14LP.lean:35) | `closed_1_4_full` (Final14Full.lean:21) | Counted: `closed_1_4_lp_noSC_noSup` (LssDerived.lean:54; MQ-li-4), applying `closed_1_4_lp_noSC`. Chain: noSC (hSCHB dropped) inside lp (15 binders dropped) inside full. |
| 1.6 | `closed_1_6_lp_noSC` (Clean14And16LPNoSC.lean:73); `closed_1_6_lp` (Final14LP.lean:89) | `closed_1_6_full` (Final14Full.lean:89) | Counted: `closed_1_6_lp_noSC_noSup` (LssDerived.lean:95; MQ-li-4), applying `closed_1_6_lp_noSC`. Same chain. |
| 2.3 | `closed_2_3_lp` (Clean2xLP.lean:37) | `closed_2_3_lit` (Final23.lean:43); `closed_2_3_lit_noSC` (HSCRewire.lean:166) | Counted: `closed_2_3_lp` (hSCHB, hU, hmeasT, hmin, hGB, hpole dropped vs 2.3). |
| 2.4 | `closed_2_4_lp` (Clean2xLP.lean:77) | `firstPass_2_4_ownBinders` (OwnBinderRewire.lean:133) | Counted (hSC dropped). |
| 2.5 | `closed_2_5_lp` (Clean2xLP.lean:99) | `firstPass_2_5_ownBinders` (OwnBinderRewire.lean:153) | Counted (hSC dropped). |
| 2.6 | `closed_2_6_lp` (Clean2xLP.lean:122) | `firstPass_2_6_ownBinders` (OwnBinderRewire.lean:174) | Counted (hSC dropped). Row 2.6 confirmed. |
| 2.13 | `closed_2_13_lp` (CleanSec23LP.lean:31) | `closed_2_13_cellRewire` (CellRewire.lean:21) | Alias (identical). D10. |
| 3.1 | `closed_3_1_lp` (CleanSec23LP.lean:37) | `firstPass_3_1_faithful` (S3c.lean:125) | LP alternative, not counted. Added: `hBG` (Frozen), `hC` (model core), `ν` (data). Removed: h27, h218 (DRAFT). |
| 3.5 | `closed_3_5_lp` (CleanSec23LP.lean:45) | `closed_3_5_ownBinders` (OwnBinderRewire.lean:57) | Counted (hexc dropped). |
| 3.6 | `closed_3_6_lp_uniform` (CleanSec23LPUniform.lean:30, commit 5953dbf2) | - | Counted (lead op 16:02 (1), GO with conditions) and CONDITIONAL on hBE = `FrozenOneSidedBoundaryContinuityFlooredUniform` (uniform floored form; cited GMS arXiv:1807.07511v3 Thm 3.9 (3.31) + Lemma 3.11, "as proved (proof of Thm 3.9)"; FROZEN-PROVENANCE row 83, PENDING TRUTH CHECK). |
| 3.7 | `closed_3_7_lp` (CleanSec23LP.lean:61) | `firstPass_3_7_ownBinders` (OwnBinderRewire.lean:103) | Counted (hexc dropped). |
| 4.1 | `closed_4_1_lp` (CleanSec456LP.lean:30) | `firstPass_4_1_coneLaw_ownBinders` (HLsRewire53.lean:65) | Counted (hexc, hcone dropped). |
| 4.2 | `closed_4_2_lp` (Clean42And5LP.lean:47) | `closed_4_2_clean` (Chain42ConeLaw.lean:116) | Counted (hG, hpc, hsmp, hwmp, hpole dropped). |
| 4.8 | `closed_4_8_lp` (CleanSec456LP.lean:38) | `closed_4_8_corrected_ownBinders` (OwnBinderRewire.lean:71) | Counted (hexc dropped). |
| 5.1 | `closed_5_1_lp` (Clean42And5LP.lean:79) | `closed_5_1_clean` (Clean51And54.lean:40) | Counted as `closed_5_1_lp_noSup` (LssDerived.lean:353; MQ-li-4), applying `closed_5_1_lp` (hμae, hSB, hU, hexc, hG, hLoc, hpair, hmeasT, hmin dropped). |
| 5.3 | `closed_5_3_lp` (Clean42And5LP.lean:108) | `closed_5_3_clean` (HLsRewire53.lean:109) | Alias (identical). D11. |
| 5.4 | `closed_5_4_lp` (Clean42And5LP.lean:130) | `closed_5_4_clean` (Clean51And54.lean:73) | Alias (identical). D11. |
| 6.1 | `closed_6_1_lp` (Clean61And71LP.lean:43) | `closed_6_1_clean` (Clean61And81.lean:31) | Counted as `closed_6_1_lp_noSup` (LssDerived.lean:257; MQ-li-4), applying `closed_6_1_lp` (11 binders dropped). |
| 6.4 | `closed_6_4_lp` (CleanSec456LP.lean:45) | `firstPass_6_4_uniform` (S6p.lean:213) | Counted (hR dropped; the conclusion is the same constant, written `FirstPass64.` in the LP file). |
| 6.5 | none | none | `firstPass_6_5_uniform` (S6q.lean:26) confirmed by the operator decision (tasks/li.md:373). |
| 6.10 | `closed_6_10_lp` (CleanSec456LP.lean:52) | `closed_6_10_ownBinders` (OwnBinderRewire.lean:123) | Counted (hR dropped). |
| 7.1 | `closed_7_1_lp` (Clean61And71LP.lean:84) | `closed_7_1_clean` (Clean71.lean:42) | Counted (7 binders dropped). |
| 8.1 | `closed_8_1_lp` (Clean81LP.lean:43) | `closed_8_1_full` (Clean81Full.lean:19) | Counted as `closed_8_1_lp_noSup` (LssDerived.lean:295; MQ-li-4), applying `closed_8_1_lp` (13 binders dropped; the 8 DRAFT binders and h24c are kept). |

The forms 1.4n, 1.6n and 2.3lp are rows of their own in the table; each is the same declaration as the counted form of its row. The rows of the table were edited by hand after the generator run to record these outcomes.

## Existence of the coupling

Status: **PENDING TRUTH CHECK**. Existence is not proved in this repository; it is a cited literature input. It concerns
the valid environments `MatedCRTEnv.IsValid 𝒮 γ` (MatedCRT/Defs/Setting.lean:142).

- **Literature inputs named.** `IsMatingOfTreesCoupling` (LatticeProb module
  `LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling` (Lattice-Probability/LatticeProb/Bonanno/MatedCRTHarmonic/Frozen/IsMatingOfTreesCoupling.lean:61); MatedCRT/Defs/Setting.lean:7, MatedCRT/Defs/Setting.lean:14, MatedCRT/Defs/Setting.lean:157-165) is the coupling
  conjunct of `IsValid`. `MatedCRTEnv.IsValid` (Setting.lean:142) has the fields `isQuantumCone`, `isLQGMeasure`,
  `isSLE` and the coupling. `HasReferenceEnvironments 𝒮` (MatedCRT/FirstPass/SLERef/Reference.lean:42) gives valid
  environments for every γ ∈ (0,2); it is a conjunct of `CertifiedReferenceModel ν 𝒮` (SLERef/Certified.lean:54, :54).
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

Wrappers (the rows above are updated): `closed_2_19_ownBinders` (line 39), `closed_3_3_ownBinders` (line 45), `closed_3_4_ownBinders` (line 51), `closed_3_5_ownBinders` (line 57), `closed_4_7_ownBinders` (line 65), `closed_4_8_corrected_ownBinders` (line 71), `closed_5_2_ownBinders` (line 79), `firstPass_2_17_ownBinders` (line 85), `firstPass_3_1_ownBinders` (line 92), and `firstPass_3_7_ownBinders` (line 103) (row 3.1 kept on `firstPass_3_1_faithful`). Second batch: `closed_2_2_ownBinders` (line 116), `closed_6_10_ownBinders` (line 123), `firstPass_2_4_ownBinders` (line 133), `firstPass_2_5_ownBinders` (line 153), `firstPass_2_6_ownBinders` (line 174), `firstPass_4_1_ownBinders` (line 211, partial). No flagged binder remains in the first ten; the partial ones keep the flags shown in their rows.

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
  `Assembly/Main.lean:156` from `MainHypotheses`. z12 copies (H35CorrectedRewire.lean): `firstPass_4_1_coneLaw_h35c` (:48),
  `firstPass_4_2_final_h35c` (:217), `firstPass_4_1_ownBinders_h35c`, `firstPass_4_1_ownBinders_counted`. Used by 5.3 (h41) above.
- **BLOCKED h24** `ConeHarmonicBallsUpToFixedTimeStmt` (4.2). Available: `ConeHarmonicBallsUpToFixedTimeCanonicalStmt` (2.4).
- **BLOCKED h24c** `ConeHarmonicBallsUpToFixedTimeCorrectedStmt` (5.1; FirstPass/S2b.lean:43). No counted theorem concludes it.
- **BLOCKED hG15, h215, owner z9** (lead li 2026-11-11 08:20) `GreenFunctionCrudeBoundStmt 𝒮` (Draft/Section2.lean:201; cited 2.15). Expected: this Prop. `firstPass_4_1_ownBinders` (line 211) has h35 as its only Draft binder.
  Available: none (the only occurrences in MatedCRT are binders, e.g. `firstPass_5_4`, S5S6S7.lean:42). Blocks 5.1 and 5.4.
- **hLs (5.3), discharged** `ConeScaleInvarianceCodedStmt` (FirstPass/S2g/LawCoded.lean:20) by `coneScaleInvarianceCoded_ownBinders`
  (HLsRewire53.lean:46) = `firstPass_2_6_coded_of_globalFamilyFactor` (S2g/LawCoded.lean:33) applied to
  `coneGlobalFamilyFactor_ownBinders` (HLsRewire53.lean:41) = `coneGlobalFamilyFactor_proved` (S2i/GlobalFactor.lean:519) with
  `hcan`, `hcl`, `closed_2_2_ownBinders` (h22, keeps `hND`), `volumeGrowthStmt_of_berestyckiGwynne` (h27). Lead li 2026-11-11 08:20.
- **h41 (5.3), discharged** by `firstPass_4_1_coneLaw_ownBinders` (HLsRewire53.lean:65) = `firstPass_4_1_coneLaw_h35c`
  (H35CorrectedRewire.lean:39) with the core reference model `hC` and `closed_3_5` (input `hexc`, Frozen); cone-law input `hcone`
  (`FrozenConeScalingLaw`, Frozen/S4S6c.lean:18). Not the counted 4.1 form.
- **BLOCKED h51, h61, h71, h42** (6.1, 8.1): h51 needs `closed_5_1` (blocked by h24c, hG15); h61 needs the 6.1 result (now `firstPass_6_1_corrected`)
  (blocked by h51); h71 needs `firstPass_7_1` (blocked by hconv); h42 needs `firstPass_4_2_final` (blocked by h35, h24),
  or `Phase2Rewire.lean:338` (not examined this round).
- hconv (7.1), h41 (5.3): `firstPass_4_1` (blocked by h35). h37 (4.6): `firstPass_3_7_ownBinders` (blocked by h35 in 4.6).
- hE1 `ConeCircleLawUniqueStep`, hE2 `ConeReferenceExistsStep` (bound by `firstPass_2_5_canonical_p2`, `firstPass_2_6_corrected_p2`,
  and by the 5.3 route): **resolved** (lead li 2026-11-11 08:20): keep the class Frozen, as the file defines them
  (FirstPass/Frozen/S2i.lean:16, :27; reports/z9.md).

**Classification of the remaining paper-own and Proof? binders.**

| Binder | Prop (location) | Class | Source | Status |
|---|---|---|---|---|
| hND | `LQGMeasureNonDyadicDilationPart` | Step | cited input, not staged | kept by operator ruling (tasks/li.md:196; req 104a); option (A), lead decision: stays a cited input. Cited: paper Fact 2.2 IV (corrected tex:483-488) for phi(z) = s z; DS11 Prop 2.1, SW16 Thm 1.1; the extension to the cone at the origin is the paper's claim (tex:471-472), unwritten; TRUE as typed (MQ-li-3, MEDIUM). MQ-li-13 (13:20 UTC): citation-scope note, SW16 does not cover the cone at the origin (attribution at tex:490-491); no erratum | DERIVED 2026-11-12: lqgMeasureNonDyadicDilationPart_holds (MatedCRT/FirstPass/Derived/ConeDilationRatioHolds.lean), supplied in the counted forms of Derived/Counted.lean. |
| hLit | `MatedCRT.S2VG.LitExistence` (FirstPass/S2VG/Literature.lean:44) | HB Proposed (lead li 2026-11-11 08:20) | HarmonicBalls Harmonic-Balls-LQG/HarmonicBalls/Proposed/LQG.lean (abbrev) | not staged in External: FOR OPERATOR |
| hBM | `LitWholePlaneBallMass` (FirstPass/S2VG/Literature.lean:25) | HB Proposed (lead li 2026-11-11 08:20) | Harmonic-Balls-LQG/HarmonicBalls/Proposed/LQG.lean:154; Ding-Gwynne arXiv:1807.01072 Lemma 3.8 | not staged in External: FOR OPERATOR |
| hCC | `LitCoordChange` (FirstPass/S2VG/Literature.lean:32) | HB Proposed (lead li 2026-11-11 08:20) | HarmonicBalls Harmonic-Balls-LQG/HarmonicBalls/Proposed/LQG.lean (abbrev) | not staged in External: FOR OPERATOR |
| hμ | `LitQuantumConeLQGMeasureExistence` (FirstPass/S4S6c/LitConeLQG68.lean:26) | HB Proposed (lead li 2026-11-11 08:20) | not checked this round | not staged in External: FOR OPERATOR |
| hnj | `StrictGapFixedTimeUnionStep 𝒮` (FirstPass/S4d/StrictGapReduction.lean:35) | Step | paper-own step | needs proof (4.2) |
| hcan | `ConeCanonicalHalfBallStep` (FirstPass/S2g.lean:81) | Step | paper-own step | needs proof (4.2); owner z9 (lead li 2026-11-11 08:20); kept as binder in 5.3 (HLsRewire53.lean) |
| hcl | `ConeHalfBallClosureInsideStep` (Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18) | Step | paper-own step | needs proof (4.2); owner z9; kept as binder in 5.3 (HLsRewire53.lean) |
| hLs | `ConeScaleInvarianceCodedStmt` (FirstPass/S2g/LawCoded.lean:20) | paper-own (coded 2.6) | paper-own | discharged in 5.3: `coneScaleInvarianceCoded_ownBinders` (HLsRewire53.lean:52); its inputs hcan, hcl, hND stay |
| h24c | `ConeHarmonicBallsUpToFixedTimeCorrectedStmt` (FirstPass/S2b.lean:43) | paper-own (corrected 2.4) | paper-own | blocked (5.1) |

## Table

Generated by the z1 ledger script from the repository (`/tmp/z1s/ledger.py` on the work machine). It is a snapshot;
regenerate after any change to a counted declaration.

| Result | Counted declaration | file:line | Kind | Binder classes | Flagged binders | Note |
|---|---|---|---|---|---|---|
| 1.4 | `closed_1_4_lp_noSC_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:54 | DERIVED (LssDerived.lean:54, applies `closed_1_4_lp_noSC`, MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean:24; chain `closed_1_4_lp`, Final14LP.lean:35) | data 2 core 1 External 1 Step 1 HB 11 Frozen 19 DRAFT 1 (36 binders) | Step:hND; DRAFT:h27 (MQ-li-4) | Rule 1: `closed_1_4_lp` (37 binders) and `closed_1_4_lp_noSC` (36) are strict sub-lists of the earlier counted form `closed_1_4_full` (Final14Full.lean:21, 52 binders), same conclusion. Audit B6 accepted (lead, 05:35 UTC). firstPassMain_1_4 (FirstPass/Main.lean:50) is not counted. |
| 1.4n | `closed_1_4_lp_noSC_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:54 | DERIVED (LssDerived.lean:54, applies `closed_1_4_lp_noSC`, MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean:24; chain `closed_1_4_lp`, Final14LP.lean:35) | data 2 core 1 External 1 Step 1 HB 11 Frozen 19 DRAFT 1 (36 binders) | Step:hND; DRAFT:h27 (MQ-li-4) | Counted form of row 1.4 (same declaration as row 1.4; switched with it, MQ-li-4). Commit 17ca4173 (z5). Replaces `closed_1_4_full_noSC` (HSCRewire.lean:30; row 1.4 binders minus hSC, hSCHB). hSCHB discharged by `frozenClusterStrongCompatibility_of_volumeGrowth hI2HB` (FirstPass/Closure/HSCDerived.lean:19); hI2HB is the same Prop as hI2 (`FrozenLQGVolumeGrowthAllScales`, Frozen/S5Cited.lean:39, defined as `LQGVolumeGrowthAllScalesStmt.{0}`), so no hypothesis is added. The other discharges of `closed_1_4_lp` are those listed in the Final14LP.lean docstring (not re-audited here). Its base `closed_1_4_dedup` (Final14Dedup.lean:36) is not a row; row 1.4 still counts `closed_1_4_full` (open point for the lead). |
| 1.6 | `closed_1_6_lp_noSC_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:95 | DERIVED (LssDerived.lean:95, applies `closed_1_6_lp_noSC`, MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean:73; chain `closed_1_6_lp`, Final14LP.lean:89) | data 2 core 1 External 1 Step 1 HB 11 Frozen 19 DRAFT 1 (36 binders) | Step:hND; DRAFT:h27 (MQ-li-4) | Rule 1: `closed_1_6_lp` (37 binders) and `closed_1_6_lp_noSC` (36) are strict sub-lists of the earlier counted form `closed_1_6_full` (Final14Full.lean:89, 52 binders), same conclusion. Audit B6 accepted (lead, 05:35 UTC). firstPassMain_1_6 (FirstPass/Main.lean) is not counted. |
| 1.6n | `closed_1_6_lp_noSC_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:95 | DERIVED (LssDerived.lean:95, applies `closed_1_6_lp_noSC`, MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean:73; chain `closed_1_6_lp`, Final14LP.lean:89) | data 2 core 1 External 1 Step 1 HB 11 Frozen 19 DRAFT 1 (36 binders) | Step:hND; DRAFT:h27 (MQ-li-4) | Counted form of row 1.6 (same declaration as row 1.6; switched with it, MQ-li-4). Commit 17ca4173 (z5). Replaces `closed_1_6_full_noSC` (HSCRewire.lean:98). Same discharge as row 1.4n: hSCHB from hI2HB (HSCDerived.lean:19), no hypothesis added. |
| 2.3 | `closed_2_3_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean:37 | DERIVED (from `closed_2_3_lit_noSC`, row 2.3n) | External 1 Frozen 10 HB 11 Step 1 (23 binders) | Step:hND | Rule 1: `closed_2_3_lp` is a strict sub-list of `closed_2_3_lit_noSC` and of the earlier counted form `closed_2_3_lit` (Final23.lean:43, 29 binders; hSCHB, hU, hmeasT, hmin, hGB, hpole dropped), same conclusion. Binder h22 is closed_2_2_lit; hND is the operator-staged literature input (req 104a). |
| 2.3n | `closed_2_3_lit_noSC` | MatedCRT/FirstPass/Closure/HSCRewire.lean:166 | DERIVED (from `closed_2_3_lit`, row 2.3) | row 2.3 binders minus hSCHB | none | Rule 1: strict sub-list of `closed_2_3_lit`; the counted form of row 2.3 is `closed_2_3_lp`, a strict sub-list of this form. hSCHB removed, discharged from hI2HB; no binder added. |
| 2.4 | `closed_2_4_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean:77 | DERIVED (own-binder wrapper `firstPass_2_4_ownBinders`) | Frozen 7 HB 11 (18 binders) | none | Rule 1: strict sub-list of `firstPass_2_4_ownBinders` (OwnBinderRewire.lean:133, 19 binders; hSC dropped), same conclusion; that wrapper is the earlier counted form (of `firstPass_2_4_canonical_p2`). Own-binder wrapper: h27 by `volumeGrowthStmt_of_berestyckiGwynne hBG`. Route of the h24 input (Phase2Rewire). Not named in tasks/li.md; to be confirmed by the lead. |
| 2.5 | `closed_2_5_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean:99 | DERIVED (own-binder wrapper `firstPass_2_5_ownBinders`) | External 1 Frozen 9 HB 11 Step 1 (22 binders) | Step:hND (kept by operator ruling; enters with `closed_2_2_ownBinders`) | Rule 1: strict sub-list of `firstPass_2_5_ownBinders` (OwnBinderRewire.lean:153, 23 binders; hSC dropped), same conclusion; that wrapper is the earlier counted form (of `firstPass_2_5_canonical_p2`). Own-binder wrapper: h27 by hBG; h22 by `closed_2_2_ownBinders` (hscale, hBG, hND). hE1, hE2 kept (classes Frozen/HB as in the ledger). |
| 2.6 | `closed_2_6_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean:122 | DERIVED (own-binder wrapper `firstPass_2_6_ownBinders`) | External 1 Frozen 9 HB 11 Step 1 (22 binders) | Step:hND (kept by operator ruling; enters with `closed_2_2_ownBinders`) | Confirmed by the lead (p2-ledger-lp-counted-status), as 2.5. Rule 1: strict sub-list of `firstPass_2_6_ownBinders` (OwnBinderRewire.lean:174, 23 binders; hSC dropped), same conclusion; that wrapper is the earlier counted form (of `firstPass_2_6_corrected_p2`). |
| 2.3lp | `closed_2_3_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean:37 | DERIVED (from `closed_2_3_lit_noSC`, row 2.3n) | External 1 Frozen 10 HB 11 Step 1 | Step:hND | Counted form of row 2.3 (rule 1; same declaration). Commit 8a716fde (z8). LP form: hU, hmeasT, hmin (LPBridge `_holds`), hGB, hpole (HBRewire `_of_hb`) discharged. 28 -> 23 binders. |
| 2.4lp | `closed_2_4_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean:77 | DERIVED (own-binder wrapper `firstPass_2_4_ownBinders`) | Frozen 7 HB 11 | none | Counted form of row 2.4 (rule 1; same declaration). Commit 8a716fde (z8). hSC discharged by `frozenClusterStrongCompatibility_of_volumeGrowth` (HSCDerived.lean:19). 19 -> 18 binders. |
| 2.5lp | `closed_2_5_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean:99 | DERIVED (own-binder wrapper `firstPass_2_5_ownBinders`) | External 1 Frozen 9 HB 11 Step 1 | Step:hND | Counted form of row 2.5 (rule 1; same declaration). Commit 8a716fde (z8). hSC discharged as 2.4; hND kept (operator ruling). 23 -> 22 binders. |
| 2.6lp | `closed_2_6_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean:122 | DERIVED (own-binder wrapper `firstPass_2_6_ownBinders`) | External 1 Frozen 9 HB 11 Step 1 | Step:hND | Counted form of row 2.6 (rule 1; same declaration). Commit 8a716fde (z8). As 2.5. 23 -> 22 binders. |
| 2.13 | `closed_2_13_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean:21 | DERIVED (FirstPass/Closure/Section2.lean) | data 1 | none | Audit m1: no hcell (`adjacentCellsMeetAeStep 𝒮`). Replaces the counted row `closed_2_13` (binds hcell, Frozen 1); same statement as the m1 row below. LP form `closed_2_13_lp` (FirstPass/Closure/CleanSec23LP.lean:31) is identical (rule 1: no binder discharged), an alias listed in DUPLICATES.md D10. |
| 2.17 | `firstPass_2_17_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:85 | DERIVED (own-binder wrapper of `firstPass_2_17`) | Frozen 1 | none | Own-binder wrapper: h27 by `volumeGrowthStmt_of_berestyckiGwynne hBG` (Proofs/Sec3/ConeBallMass.lean:17; hBG Frozen). No LP form: remaining binder hBG = `FrozenBerestyckiGwynneConeBallMass` (Berestycki-Gwynne arXiv:2003.10320v2 Lemma A.1), class (c) cited (lead li 10:20). |
| 2.19 | `closed_2_19_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:39 | DERIVED (own-binder wrapper of `closed_2_19`) | core 1 Frozen 1 data 2 | none | Own-binder wrapper of closed_2_19 (Closure/Section2.lean:40): h27 supplied by the cited volume-growth input (hBG Frozen). No LP form: remaining binder hBG = `FrozenBerestyckiGwynneConeBallMass` (Berestycki-Gwynne arXiv:2003.10320v2 Lemma A.1), class (c) cited (lead li 10:20). |
| 3.1 | `firstPass_3_1_faithful` | MatedCRT/FirstPass/S3c.lean:125 | COUNTED (proof) | DRAFT 2 External 1 Frozen 1 data 1 | DRAFT:h27, DRAFT:h218 | Audit m3. Own-binder wrapper `firstPass_3_1_ownBinders` (MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:92) removes h27 and h218 (h218 by `CertifiedReferenceModel.exitTimeUpperBound`); row kept on `firstPass_3_1_faithful` per lead. Concludes `DiscretePotentialTightnessPointwiseStmt 𝒮` (S3c.lean:100; samplewise form, fidelity fix §1.3), not the Draft `DiscretePotentialTightnessStmt 𝒮` (Draft/Section3.lean:42). Corrected tex lemma:discrete-potential-tightness (l.981-986): "every connected domain D ⊂ B_ρ"; the paper does not say D is open. `IsOpen D` is the printed hypothesis: "domain" = open connected set (lead li 2026-11-11 08:20; Draft/Section3.lean:42; the Draft has IsConnected only). closed_3_1 (weak form, DiscretePotentialTightnessCorrectedStmt) is not counted; closed_3_1_faithful / closed_3_1_countable do not exist. Alternative: firstPass_3_1_countable (S3c/CountableFamilies.lean:97). LP alternative, not counted (rule 1: binders added). `closed_3_1_lp` (FirstPass/Closure/CleanSec23LP.lean:37; data 2, core 1, External 1, Frozen 2: hBG, h32) adds `hBG` (Frozen), `hC` (model core) and `ν` (data), and drops the Draft binders h27 and h218 (lead li 10:20). |
| 3.3 | `closed_3_3_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:45 | DERIVED (own-binder wrapper of `closed_3_3`) | core 1 Frozen 1 data 2 | none | Own-binder wrapper of closed_3_3 (Closure/Section3.lean:43): h27 supplied as in the 2.19 row. No LP form: remaining binder hBG = `FrozenBerestyckiGwynneConeBallMass` (Berestycki-Gwynne arXiv:2003.10320v2 Lemma A.1), class (c) cited (lead li 10:20). |
| 3.4 | `closed_3_4_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:51 | DERIVED (own-binder wrapper of `closed_3_4`) | core 1 Frozen 1 data 2 | none | Own-binder wrapper of closed_3_4 (Closure/Section3.lean:36): h27 supplied as in the 2.19 row. No LP form: remaining binder hBG = `FrozenBerestyckiGwynneConeBallMass` (Berestycki-Gwynne arXiv:2003.10320v2 Lemma A.1), class (c) cited (lead li 10:20). |
| 3.5 | `closed_3_5_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean:45 | DERIVED (CleanSec23LP.lean; closed_3_5_ownBinders) | core 1 Frozen 1 data 2 | none | hexc discharged by `frozenBrownianOutwardExcursionAtExit_holds` (LPBridge/BrownianOutwardExcursion.lean:113), exact type. Rule 1: counted; strict sub-list of `closed_3_5_ownBinders` (hexc dropped). Remaining Frozen binder hBG (class (c) cited). Replaces `closed_3_5_ownBinders` (OwnBinderRewire.lean:57; core 1 Frozen 2 data 2). |
| 3.6 | `closed_3_6_lp_uniform` | MatedCRT/FirstPass/Closure/CleanSec23LPUniform.lean:30 (commit 5953dbf2) | DERIVED (CleanSec23LPUniform.lean; closed_3_6_full_floored_uniform_bm, Closure/Lemma36FlooredUniform.lean; hexc discharged by frozenBrownianOutwardExcursionAtExit_holds, LPBridge/BrownianOutwardExcursion.lean:113) | data 2 core 1 External 1 Frozen 1 Cited 1 | Cited:hBE (uniform floored form; GMS Thm 3.9 (3.31) + Lemma 3.11, source label "as proved (proof of Thm 3.9)") | **CONDITIONAL** (lead li 16:58 (SW), after op 16:02 (1)): hBE = FrozenOneSidedBoundaryContinuityFlooredUniform (S3i/LensFloored.lean:68; FROZEN-PROVENANCE row 83, PENDING TRUTH CHECK: uniformity in rho from beta = beta(gamma), operator decision). FROZEN-PROVENANCE row 81); the earlier clause "CONDITIONAL on hBE (MQ-li-7a)" is replaced by the row 83 condition. Floored `closed_3_6_rate_floored` (Lemma36RateFloored.lean:112) remains as a separate form. Frozen 1 is h32 (FrozenDiscreteHolderContinuityCorrected, UNSURE). Own-binder wrapper (partial): h211 and h28 by the CertifiedReferenceModel projections on hC. |
| 3.7 | `closed_3_7_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean:61 | DERIVED (CleanSec23LP.lean; firstPass_3_7_ownBinders) | External 1 core 1 Frozen 2 data 2 | none | hexc discharged by `frozenBrownianOutwardExcursionAtExit_holds`, exact type. Frozen 2: hBG (class (c) cited) and h32 (FrozenDiscreteHolderContinuityCorrected, UNSURE). Rule 1: counted; strict sub-list of `firstPass_3_7_ownBinders` (hexc dropped). Replaces `firstPass_3_7_ownBinders` (OwnBinderRewire.lean:103; Frozen 3). |
| 4.1 | `closed_4_1_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean:30 | DERIVED (CleanSec456LP.lean:30, applies `firstPass_4_1_coneLaw_ownBinders`, MatedCRT/FirstPass/Closure/HLsRewire53.lean:65) | data 2 core 1 Frozen 1 (hBG) | none | Commit a4ac5fc6 (z5). Rule 1: counted; strict sub-list of `firstPass_4_1_coneLaw_ownBinders` (hexc and hcone dropped). Replaces `firstPass_4_1_coneLaw_ownBinders` (data 2 core 1 Frozen 3: hBG, hexc, hcone; cone-law form of `firstPass_4_1_coneLaw_h35c`, H35CorrectedRewire.lean:48, commit e7a5833; lead li 08:20). hexc discharged by `frozenBrownianOutwardExcursionAtExit_holds` (LPBridge/BrownianOutwardExcursion.lean:113); hcone discharged by `hC.frozenConeScaling` (SLERef/Certified.lean:111, CRM conjunct 8, exact type), the option noted in the earlier version of this row, now applied. |
| 4.2 | `closed_4_2_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean:47 | DERIVED (Clean42And5LP.lean:47, applies `closed_4_2_clean`; LP-bridge form) | data 1 (𝒮) External 2 DRAFT 8 paper-own 1 Step 1 HB 10 Frozen 13 (36 binders; hcone FrozenConeScalingLaw, not FrozenConeEnvironmentScaling) | DRAFT:h210, DRAFT:h34, DRAFT:h214, DRAFT:h28, DRAFT:h35c, DRAFT:h218, DRAFT:h23, DRAFT:h33; paper-own:h24c; Step:hND | Rule 1: strict sub-list of `closed_4_2_clean` (Chain42ConeLaw.lean:116, 41 binders; hG, hpc, hsmp, hwmp, hpole dropped), same conclusion. The earlier counted form `closed_4_2_clean` is the COUNTED (proof, cone-law form) row. Lead li 2026-11-11 09:13: row 4.2 DONE. |
| 4.3 | `closed_4_3` | MatedCRT/FirstPass/Closure/Section4.lean:18 | DERIVED (FirstPass/S3S4.lean) | data 1 | none |  |
| 4.4 | `closed_4_4` | MatedCRT/FirstPass/Closure/Section4.lean:22 | DERIVED (FirstPass/S3S4.lean) | data 1 | none |  |
| 4.5 | `closed_4_5` | MatedCRT/FirstPass/Closure/Section4.lean:27 | DERIVED (FirstPass/S3S4.lean) | data 1 | none |  |
| 4.6 | `firstPass_4_6_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean:74 | DERIVED (`firstPass_4_6_corrected`, MatedCRT/FirstPass/S3S4.lean:102, with h28 and the corrected Lemma 3.5 input h35c, commit e7a5833) | DRAFT 5 (h27 h218 h28 h35c h37) External 1 (hm) Frozen 1 (hH) data 2 | DRAFT:h27, DRAFT:h218, DRAFT:h28, DRAFT:h35c, DRAFT:h37 | h28 (CellSizeEstimateStmt) is the bridge input added in e7a5833; the DRAFT binders are open (h37 blocked, reports/z12.md). |
| 4.7 | `closed_4_7_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:65 | DERIVED (own-binder wrapper of `closed_4_7`) | core 1 Frozen 1 data 2 | none | Own-binder wrapper of closed_4_7 (Closure/Section4.lean:31): h27 supplied. |
| 4.8 | `closed_4_8_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean:38 | DERIVED (CleanSec456LP.lean:38, applies `closed_4_8_corrected_ownBinders`, MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:71) | core 1 Frozen 1 data 2 (hBG) | none | Commit a4ac5fc6 (z5). Rule 1: counted; strict sub-list of `closed_4_8_corrected_ownBinders` (hexc dropped). Replaces `closed_4_8_corrected_ownBinders` (core 1 Frozen 2 data 2; wrapper of closed_4_8_corrected, S4x8.lean:45, h27 supplied). hexc discharged by `frozenBrownianOutwardExcursionAtExit_holds` (LPBridge/BrownianOutwardExcursion.lean:113), exact type. hBG (class (c) cited) remains. |
| 5.1 | `closed_5_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:353 | DERIVED (LssDerived.lean:353, applies `closed_5_1_lp`, MatedCRT/FirstPass/Closure/Clean42And5LP.lean:79) | data 2 core 1 External 1 Step 1 HB 14 Frozen 11 DRAFT 1 (31 binders) | Step:hND (kept by operator ruling); DRAFT:h27 (MQ-li-4) | Rule 1 (base form, before the MQ-li-4 switch): counted; strict sub-list of `closed_5_1_clean` (Clean51And54.lean:40, 40 binders; hμae, hSB, hU, hexc, hG, hLoc, hpair, hmeasT, hmin dropped), same conclusion. DRAFT 1 (h27 from the MQ-li-4 switch; was 0). Earlier counted form `closed_5_1_clean`: own-binder wrapper of `closed_5_1_ownBinders` (H24cBridge.lean:89): h22 by `closed_2_2_ownBinders` (hBG Frozen, hscale External, hND Step), hG15 by `greenFunctionCrudeBound_of_canonical` from Frozen hcanon (BG20 Lemma 5.6). Lead li 2026-11-11 08:20. Owner z9 (reports/z9.md, commit a1339bd). |
| 5.2 | `closed_5_2_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:79 | DERIVED (own-binder wrapper of `closed_5_2`) | core 1 Frozen 1 data 2 | none | Own-binder wrapper of closed_5_2 (Closure/Section5.lean:17): h27 supplied. |
| 5.3 | `closed_5_3_clean` | MatedCRT/FirstPass/Closure/HLsRewire53.lean:109 | COUNTED (proof) | core 1 data 2 External 1 (hscale) Step 1 (hND) Frozen 11 (hBG hE1 hE2 hF3 hfirst hstd hCentre hconf hK hE hFL) HB 11 (hOpen hSup hCons hMono hCompat hBdry hExist hThm11 hProp56 hloc hI2) | Step:hND (kept by operator ruling) | Discharged: hcan and hcl (Closure/Steps42.lean:40, :106); hSC by `frozenClusterStrongCompatibility_of_volumeGrowth hI2` (Closure/HSCDerived.lean:19; class 'derived from hI2, HB exhaustion route; differs from the printed proof of Lemma 5.8'); hcl class 'derived in Lean (S5r/ClosureInside.lean:24)'; hM := hC.mepsScaling; hcone := hC.frozenConeScaling; hF, hmin, hF1, hG, hexc by committed proofs (LPBridge/InRepoProofs.lean:35, LPBridge/MinimumPrinciples.lean:30, LPBridge/UniversalMeasurability.lean:18, HBRewire.lean:40, LPBridge/BrownianOutwardExcursion.lean:113). Predecessor: `closed_5_3_ownBinders` (HLsRewire53.lean:78, ecfbc55). Build of the bb7e1297 form: BUILD OK. hI2 not taken from `lqgVolumeGrowthAllScalesStmt_litI2` (S2VG/Literature.lean:56), which needs five literature inputs. Lead li 2026-11-11 08:58. |
| 5.4 | `closed_5_4_clean` | MatedCRT/FirstPass/Closure/Clean51And54.lean:73 | DERIVED (FirstPass/S5S6S7.lean:42) | core 1 data 2 Frozen 1 | none | DRAFT 0. h215 from hcanon as in 5.1; h216 and h29 are projections of core hC (no counted row for Lemmas 2.9, 2.16). Owner z9 (commit a1339bd). |
| 6.1 | `closed_6_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:257 | DERIVED (LssDerived.lean:257, applies `closed_6_1_lp`, Clean61And71LP.lean:43, which applies `closed_6_1_clean`) | data 2 core 1 External 1 Step 1 HB 12 Frozen 15 DRAFT 1 (33 binders) | Step:hND (kept by operator ruling); DRAFT:h27 (MQ-li-4) | Rule 1 (base form, before the MQ-li-4 switch): counted; strict sub-list of `closed_6_1_clean` (Clean61And81.lean:31, 44 binders; hμae, hSB, hU, hexc, hpole, hLoc, hpair, hmeasT, hmin, hR, hGB dropped), same conclusion. Earlier counted form `closed_6_1_clean`: Commit 2fb105c. Replaces `firstPass_6_1_corrected` (its DRAFT 3 removed: h610 by `closed_6_10_ownBinders`, h51 by `closed_5_1_clean`, h27 by `volumeGrowthStmt_of_berestyckiGwynne hBG`). 44 binders incl. 𝒮 ν, recounted from the signature. |
| 6.1lp | `closed_6_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:257 | DERIVED (LssDerived.lean:257, applies `closed_6_1_lp`, Clean61And71LP.lean:43, which applies `closed_6_1_clean`) | data 2 core 1 External 1 Step 1 HB 12 Frozen 15 DRAFT 1 | Step:hND; DRAFT:h27 (MQ-li-4) | Counted form of row 6.1 (same declaration as row 6.1; switched with it, MQ-li-4). Commit 7b19a40a (z5). 11 of 42 non-data binders discharged by committed concluders (hμae hSB hU hexc hpole hLoc hpair hmeasT hmin hR hGB). 33 binders. |
| 6.4 | `closed_6_4_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean:45 | DERIVED (CleanSec456LP.lean:45, applies `firstPass_6_4_uniform`, MatedCRT/FirstPass/S6p.lean:213) | Frozen 3 (h0, h2, hV) | none | Commit a4ac5fc6 (z5). Operator note 05:50 UTC named `firstPass_6_4_uniform` (S6p.lean); rule 1: counted, a strict sub-list of `firstPass_6_4_uniform` (hR dropped; same conclusion). hR (`FPConeMeanZeroRestriction`, Frozen 4 in the base) is discharged by `fpConeMeanZeroRestriction_holds` (LPBridge/ConeMeanZeroRestrictionFinal.lean:144), exact type. |
| 6.5 | `firstPass_6_5_uniform` | MatedCRT/FirstPass/S6q.lean:26 | DERIVED (FirstPass/S6p.lean) | Frozen 3 | none | Confirmed by the lead (p2-ledger-lp-counted-status): the operator's uniform form (tasks/li.md:373). |
| 6.7 | `firstPass_6_7` | MatedCRT/FirstPass/LIClosed68Y.lean:30 | DERIVED (FirstPass/S4S6c/ShellChainCGRCYSqHalf68.lean) | Frozen 1 Proof? 4 Proposed 1 core 1 data 2 | Proof?:hLit, Proof?:hBM, Proof?:hCC, Proof?:hμ | Operator note 22:13 UTC: counted (FAITHFUL) in FirstPass/LIClosed68Y.lean. |
| 6.8 | `firstPass_6_8` | MatedCRT/FirstPass/LIClosed68Y.lean:40 | DERIVED (FirstPass/S4S6c/ShellChainCGRCYSqHalf68.lean) | Frozen 1 Proof? 4 Proposed 1 core 1 data 2 | Proof?:hLit, Proof?:hBM, Proof?:hCC, Proof?:hμ | Operator note 22:13 UTC: counted (FAITHFUL) in FirstPass/LIClosed68Y.lean. |
| 6.9 | `firstPass_6_9` | MatedCRT/FirstPass/LIClosed68Y.lean:51 | DERIVED (FirstPass/S4S6c/ShellChainCGRCYSqHalf68.lean) | Frozen 1 Proof? 4 Proposed 1 core 1 data 2 | Proof?:hLit, Proof?:hBM, Proof?:hCC, Proof?:hμ | Operator note 22:13 UTC: counted (FAITHFUL) in FirstPass/LIClosed68Y.lean. |
| 6.10 | `closed_6_10_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean:52 | DERIVED (CleanSec456LP.lean:52, applies `closed_6_10_ownBinders`, MatedCRT/FirstPass/Closure/OwnBinderRewire.lean:123) | core 1 Frozen 4 data 2 (hBG, h0, h2, hV) | none | Commit a4ac5fc6 (z5). Rule 1: counted; strict sub-list of `closed_6_10_ownBinders` (hR dropped). Replaces `closed_6_10_ownBinders` (core 1 Frozen 5 data 2). h27 by hBG as before; hR discharged by `fpConeMeanZeroRestriction_holds` (LPBridge/ConeMeanZeroRestrictionFinal.lean:144), exact type. |
| 7.1 | `closed_7_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean:84 | DERIVED (Clean61And71LP.lean:84, applies `closed_7_1_clean`) | data 2 core 1 External 1 Step 1 HB 11 Frozen 13 (29 binders) | Step:hND (kept by operator ruling) | Rule 1: counted; strict sub-list of `closed_7_1_clean` (Clean71.lean:42, 36 binders; hexc, hR, hU, hmeasT, hmin, hGB, hpole dropped), same conclusion. Earlier counted form `closed_7_1_clean`: Commit 84ed358. Replaces `firstPass_7_1`: all 8 DRAFT binders (hcone h216 h27 h28 h29 h218 hconv hgreen) removed. 36 binders incl. 𝒮 ν. |
| 7.1lp | `closed_7_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean:84 | DERIVED (Clean61And71LP.lean:84, applies `closed_7_1_clean`) | data 2 core 1 External 1 Step 1 HB 11 Frozen 13 | Step:hND | Counted form of row 7.1 (rule 1; same declaration). Commit 7b19a40a (z5). 7 of 34 non-data binders discharged (hexc hU hmeasT hmin hGB hpole hR). 29 binders. |
| 7.2 | `closed_7_2` | MatedCRT/FirstPass/Closure/Section7.lean:18 | DERIVED (FirstPass/S5S6S7.lean) | core 1 data 2 | none |  |
| 7.3 | `closed_7_3` | MatedCRT/FirstPass/Closure/Section7.lean:23 | DERIVED (FirstPass/S5S6S7.lean) | data 1 | none |  |
| 8.1 | `closed_8_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:295 | DERIVED (LssDerived.lean:295, applies `closed_8_1_lp`, Clean81LP.lean:43) | data 2 core 1 External 2 DRAFT 9 paper-own 1 Step 1 HB 12 Frozen 18 (46 binders) | DRAFT:h210, DRAFT:h34, DRAFT:h214, DRAFT:h28, DRAFT:h35c, DRAFT:h218, DRAFT:h23, DRAFT:h33; paper-own:h24c; Step:hND; DRAFT:h27 (MQ-li-4) | Rule 1 (base form, before the MQ-li-4 switch): counted; strict sub-list of `closed_8_1_full` (Clean81Full.lean:19, 59 binders; hG, hpc, hsmp, hmin, hpole, hμae, hSB, hU, hexc, hLoc, hpair, hmeasT, hR dropped), same conclusion. Earlier counted form `closed_8_1_full`: commit a9bd0055. Replaces `firstPass_8_1`: its four DRAFT binders h42, h51, h61, h71 are supplied. Commit message "no DRAFT binder" is not literal: 8 MatedCRT/Draft statements and h24c (FirstPass/S2b.lean:43) remain. 59 binders (recount; archive z12 gave 9 cited, Frozen 29, External 4, data 1). |
| 8.1lp | `closed_8_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:295 | DERIVED (LssDerived.lean:295, applies `closed_8_1_lp`, Clean81LP.lean:43) | data 2 core 1 External 2 DRAFT 9 paper-own 1 Step 1 HB 12 Frozen 18 | DRAFT (8) and paper-own h24c as in `closed_8_1_full`; Step:hND; DRAFT:h27 (MQ-li-4) | Counted form of row 8.1 (rule 1; same declaration). Commit a04b0cb4 (z12). 13 of the 59 binders of `closed_8_1_full` discharged by committed concluders; 46 binders. |
| 4.2lp | `closed_4_2_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean:47 | DERIVED (Clean42And5LP.lean:47) | data 1 (𝒮) External 2 DRAFT 8 paper-own 1 Step 1 HB 10 Frozen 13 | DRAFT:h210, DRAFT:h34, DRAFT:h214, DRAFT:h28, DRAFT:h35c, DRAFT:h218, DRAFT:h23, DRAFT:h33; paper-own:h24c; Step:hND | Commit e2d3bf22 (z9), LP-bridge form of the 4.2 counted form. 36 binders, no ν. |
| 5.1lp | `closed_5_1_lp_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:353 | DERIVED (LssDerived.lean:353, applies `closed_5_1_lp`, MatedCRT/FirstPass/Closure/Clean42And5LP.lean:79) | data 2 core 1 External 1 Step 1 HB 14 Frozen 11 DRAFT 1 | Step:hND; DRAFT:h27 (MQ-li-4) | Counted form of row 5.1 (same declaration as row 5.1; switched with it, MQ-li-4). Commit e2d3bf22 (z9). 31 binders. |
| 5.3lp | `closed_5_3_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean:108 | DERIVED (Clean42And5LP.lean:108) | data 2 core 1 External 1 Step 1 HB 11 Frozen 11 | Step:hND | Alias of row 5.3 (rule 1: identical binder list and conclusion; DUPLICATES.md D11). Commit e2d3bf22 (z9). 27 binders. |
| 5.4lp | `closed_5_4_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean:130 | DERIVED (Clean42And5LP.lean:130) | data 2 core 1 Frozen 1 | none | Alias of row 5.4 (rule 1: identical binder list and conclusion; DUPLICATES.md D11). Commit e2d3bf22 (z9). 4 binders. |
| A.1 | `discreteDivergenceTheorem` | MatedCRT/Proofs/SecA/DiscreteDivergence.lean:54 | COUNTED (proof) |  | none |  |
| A.2 | `discreteBasicPropertiesGeneral` | MatedCRT/Proofs/SecA/Statements.lean:62 | DERIVED (Steps/SecA/DiscreteObstacle.lean) |  | none | Name not verified; located by the generator. |
| A.3 | `discreteLaplacianBoundGeneral` | MatedCRT/Proofs/SecA/Statements.lean:66 | DERIVED (Steps/SecA/DiscreteObstacle.lean) |  | none | Name not verified; located by the generator. |
| A.4 | `discreteConservationOfMassGeneral` | MatedCRT/Proofs/SecA/Statements.lean:71 | DERIVED (Steps/SecA/DiscreteObstacle.lean) |  | none |  |
| B6 | `firstPassMain_1_4_full_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:136 | DERIVED (LssDerived.lean:136, applies `firstPassMain_1_4_full`, FirstPass/Main.lean:112; chain FirstPass/Closure/Final14Full.lean) | External 4 Frozen 29 DRAFT 1 HB 13 Proposed 1 Step 1 core 1 data 2 | Step:hND; DRAFT:h27 (MQ-li-4) |  |
| B6 | `firstPassMain_1_6_full_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:193 | DERIVED (LssDerived.lean:193, applies `firstPassMain_1_6_full`, FirstPass/Main.lean:172; chain FirstPass/Closure/Final14Full.lean) | External 4 Frozen 29 DRAFT 1 HB 13 Proposed 1 Step 1 core 1 data 2 | Step:hND; DRAFT:h27 (MQ-li-4) |  |
| m1 | `closed_2_13_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean:21 | DERIVED (FirstPass/Closure/Section2.lean) | data 1 | none |  |
| m1 | `closed_5_1_cellRewire_noSup` | MatedCRT/FirstPass/Closure/LssDerived.lean:396 | DERIVED (LssDerived.lean:396, applies `closed_5_1_cellRewire`, FirstPass/Closure/CellRewire.lean:30; chain FirstPass/Closure/Prop51.lean) | DRAFT 3 External 1 Frozen 18 HB 14 Proof? 1 core 1 data 2 | DRAFT:h27, DRAFT:h22, Proof?:h24c, DRAFT:hG15 (hsup dropped, MQ-li-4) |  |

## Appendix B rows (audit M13; outside the inventory)

The Appendix B occupation identity (`frozenLBMGreenOccupationRescaled_*`, `MatedCRT/Proofs/Sec3/KilledOccupation/`) has no row in INVENTORY.tsv. These rows track it for audit M13 (B5). Binder counts come from the signatures (added 2026-11-11, p2-ledger-rows-and-inventory-refresh). Inline `∀` Props are not classed, since no file defines them. `hS0` is cited (MQ-li-8e). `hlaw` is the named input `ConeUnitDiskGFFLaw` (MQ-li-12).

| Form | file:line | Commit | Binders | Named inputs and flags | Note |
|---|---|---|---|---|---|
| `frozenLBMGreenOccupationRescaled_closed` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure.lean:35 | 7a508a1 | 20 = 𝒮, ν, dA + 17 hypotheses: hm0 hWeight hMeas hS6 hBG hGreen hS0 hτ hτmeas hGint hσint hw hVar hνmeas hconvB1 hLjoint hLpath | hS0 (cited, MQ-li-8e) | hExit by `planar_exit_ae_lt_top`; hBase by `baseOccupationIdentity_of_GMC` (its GMC binders named) |
| `frozenLBMGreenOccupationRescaled_closed2` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure2.lean:32 | 582e360, 6675b36 | 15 = 𝒮, ν, dA + 12 hypotheses: hm0 hWeight hMeas hS6 hBG hS0 hw hVar hνmeas hconvB1 hLjoint hLpath | hS0 (cited, MQ-li-8e) | hGreen by `greenDiskFormula`; hτ hτmeas hGint hσint by `baseOccupationIdentity_of_GMC'` (BaseClockBinders.lean:228); hExit by `planar_exit_ae_lt_top`. The z12 report's "15, plus 𝒮" counts 𝒮 twice; 15 is the total. |
| `frozenLBMGreenOccupationRescaled_closed3` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure3.lean:68 | 23f4c7e6 | 15 = 𝒮, ν, dA + the 12 hypotheses of closed2 | hS0 (cited, MQ-li-8e) | not in the lead's list; committed after closed2 |
| `frozenLBMGreenOccupationRescaled_closed4` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure4.lean:76 | d90cbe4e | 17 = 𝒮, ν, dA + 14 hypotheses: hm0 hWeight hMeas hlaw hE hKern hBG hS0 hw hVar hνmeas hconvB1 hLjoint hLpath | hlaw : `ConeUnitDiskGFFLaw` (MQ-li-12); hS0 (cited, MQ-li-8e) | not in the lead's list; committed. hS6 is replaced by `hS6_cone`, with the origin tail moment from `coneOriginTailMoment_of_law` applied to hlaw |
| `frozenLBMGreenOccupationRescaled_closed5` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure5.lean:19 | d51a926b | 16 = 𝒮, ν, dA + 13 hypotheses: hWeight hMeas hlaw hE hKern hBG hS0 hw hVar hνmeas hconvB1 hLjoint hLpath | hlaw : `ConeUnitDiskGFFLaw` (MQ-li-12); hS0 (cited, MQ-li-8e) | hm0 discharged by MatedCRTEnv.IsValid.m₀_pos (eq:mo; HarmonicPathExit.lean:114; alias MatedCRTEnv.m₀_pos in M0Positive.lean, 793bf5b4) |
| `frozenLBMGreenOccupationRescaled_of_coneGFFLaw` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosureCone.lean:48 | ac2932c7 | 3 = 𝒮 + 2 hypotheses: hlaw hGFF | hlaw : `ConeUnitDiskGFFLaw` (MQ-li-12); hGFF (inline `∀` Prop, not classed; TRUE as typed, MQ-fp-1, confirmed by the independent check) | No binder for the weight identity, the mass bound, hS0 or the GMC clock inputs of closed5. The clock route of MQ-li-17: limit clock along a subsequence with summable gaps (LimClockIdentification.lean, LimClockKernel.lean), chaos limit weighted by the Green function (GmcGreenMeasure.lean), occupation measure of the limit clock (ClockOccupationMeasure.lean), transfer along eq:gff (ConeOccupationTransfer.lean), rescaling (RescaledClockOccupation.lean). hGFF is the occupation identity of the clock of `h^ℂ - γ log|·|`, `h^ℂ` a whole-plane GFF, with an independent planar Brownian motion, for every whole-plane GFF model. |
| `frozenLBMGreenOccupationRescaled_of_fieldLaw` | MatedCRT/FirstPass/Closure/AppendixBRewire.lean:124 | 56d06e72 | 3 = 𝒮 + 2 hypotheses: hFL hGFF | hFL : `FPConeWholePlaneFieldLaw` (Frozen; already a binder of the counted forms of 1.4, 1.6 and 5.1); hGFF as in the row above | hlaw by `coneUnitDiskGFFLaw_of_fieldLaw hFL` (AppendixBRewire.lean:55). This is the form used by `CertifiedReferenceModelCoreNoOccupation.toCore_of_fieldLaw` and `.toModel_of_fieldLaw` (AppendixBRewire.lean:131, :140). |

Binder classification of `frozenLBMGreenOccupationRescaled_closed4` by z11 (reports/z11.md, BINDER LIST; lead li 10:20, item (d)). data 3: 𝒮 (`SpaceFillingSLEModel`), ν and dA (families). Proof? 6: hlaw `ConeUnitDiskGFFLaw` (ConeGFFTransfer.lean:40; TRUE as typed, HIGH, MQ-li-12 (a); the law identity is no longer PENDING TRUTH CHECK), hS0 `KilledBrownianOccupationOnBall` (Potential.lean:275; cited, MQ-li-8e), hBG `BGMassUpperBoundDyadic` (WeightIdentity.lean; eq:occ-BGmass), hWeight `OccWeightIdentity` (MQ-li-10b), hw `circleWeight`, hLpath `clockGapMean` (conditional GMC clock input, as in closure3). Step 8: hE (chi_a-parts convergence, kept named, G1), hKern, hMeas, hVar, hνmeas, hLjoint, hconvB1 (measurability and data class, MQ-li-8g), hm0 (0 < S.m0, eq:mo). Discharged inside, not binders: hGreen (greenDiskFormula), hExit (planar_exit_ae_lt_top), hτ hτmeas hGint hσint (BaseClockBinders textbook binders), hS6 (hS6_cone, ConeClockTransfer.lean:454), hT0cone (coneOriginTailMoment_of_law, ConeOriginTails.lean:284), and the hS0 bridge (brownianOccupationOnBall_of_killed, OccupationClosure4.lean:41). Lead rulings needed on the flagged Step inputs hE, hKern, hMeas, hm0. closed5 (d51a926b) = closed4 with hm0 discharged; the other 13 binders keep the classification above.

## Derived-input forms (proved inputs supplied; 2026-11-11)

Inputs of the counted theorems that are now theorems are supplied in `MatedCRT/FirstPass/Derived/Counted.lean`: for each
counted declaration `T` that binds such an input, `T_derivedInputs` has the same conclusion and the remaining binders
(copied from the signature of `T`). The counted declarations of the Table are unchanged; the binder counts below replace
theirs for the purpose of "what is still an input". Axioms: `MatedCRT/Audit/DerivedCountedAxioms.lean` (each line prints
`propext`, `Classical.choice`, `Quot.sound`).

Proved inputs:

| input | Prop | theorem | proof |
|---|---|---|---|
| disc Green function, centre formula | `FrozenGreenBallCentre` (FirstPass/Frozen/S2g.lean:45) | `frozenGreenBallCentre_holds` (FirstPass/Derived/DiscGreenCentre.lean) | `HarmonicBalls.greenFunction_ball` at the centre |
| disc Green function, nonnegative and continuous off the centre | `FrozenDiskGreenNonnegCont` (FirstPass/Frozen/S1c.lean:38) | `frozenDiskGreenNonnegCont_holds` (same file) | centre formula; `HarmonicBalls.continuousOn_greenFunction_ball` |

Inputs supplied from other inputs of the same counted theorem (2026-11-11). Seven statements of the Harmonic-Balls paper
(arXiv:2208.11795) that the counted theorems bind are, in the Harmonic-Balls package, theorems whose only hypotheses are
other Harmonic-Balls statements which the same counted theorems bind as well. They are supplied by those theorems, so
the binders disappear and none is added. In every counted theorem concerned, the volume-growth input is the binder of
type `LQGVolumeGrowthAllScalesStmt.{0}` (or its copy `FrozenLQGVolumeGrowthAllScales`), and the existence and uniqueness
inputs are the binders of types `ExistenceHarmonicBallsStmt.{0}` and `UniquenessHarmonicBallsStmt.{0}`.

| input (HB result) | Prop | Harmonic-Balls theorem | from |
|---|---|---|---|
| least supersolution (3.1) | `LeastSupersolutionMemStmt.{0}` | `HarmonicBalls.leastSupersolutionMem_proved` (Proofs/Sec3/Basic.lean:204) | volume growth (I2) |
| open cluster, Laplacian (3.2) | `ClusterOpenLaplacianStmt.{0}` | `HarmonicBalls.clusterOpenLaplacian_proved` (Proofs/Sec3/OpenLaplacian.lean:25) | volume growth |
| monotonicity (3.3) | `ClusterMonotoneStmt.{0}` | `HarmonicBalls.clusterMonotone_proved` (Proofs/Sec3/Basic.lean:209) | volume growth |
| conservation of mass (3.4) | `ClusterConservationOfMassStmt.{0}` | `HarmonicBalls.clusterConservationOfMass_proved` (Proofs/Sec3/ConservationOfMassLemma.lean:30) | volume growth |
| compatibility (3.5) | `ClusterCompatibilityStmt.{0}` | `HarmonicBalls.clusterCompatibility_proved` (Proofs/Sec3/ClusterCompatibility.lean:360) | volume growth |
| very good annuli, Harnack-type estimate (6.11) | `VeryGoodAnnulusHarnackTypeStmt.{0}`, `FrozenVeryGoodAnnulusHarnackType` | `HarmonicBalls.Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only` (Proofs/Sec6/VolumeGrowthConsequences.lean:19) | volume growth |
| existence and uniqueness (1.1) | `ExistenceUniquenessHarmonicBallsStmt.{0}` | `HarmonicBalls.existenceUniquenessHarmonicBallsStmt_of_sec5` (Assembly/ExistenceUniqueness.lean:39) | existence (5.5) and uniqueness (5.6) |

Third pass (2026-11-11): the search is mechanical. For each counted theorem a Lean script lists the hypotheses which
follow from the other hypotheses of the same theorem by theorems of this repository and of the Harmonic-Balls package
(forward chaining on the statements; the generated file `MatedCRT/FirstPass/Derived/Counted.lean` is the check, each
`have` line there is one theorem applied to remaining binders and to earlier lines). Besides the rows above, this
supplies, wherever the needed hypotheses are bound:

* Lemma 2.7 `VolumeGrowthStmt` from the Berestycki-Gwynne cone ball-mass input (`volumeGrowthStmt_of_berestyckiGwynne`);
* the whole-plane model step `WholePlaneLQGModelStep` from the measure-existence input with insertion
  (`FirstPass.S2m.firstPass_wholePlaneLQGModel_of_existence`);
* HB strong compatibility `ClusterStrongCompatibilityStmt` from volume growth
  (`frozenClusterStrongCompatibility_of_volumeGrowth`);
* own results bound as hypotheses, from the hypotheses of their counted proofs: 2.3 `ConeHarmonicBallsStmt`, 2.4
  (corrected) `ConeHarmonicBallsUpToFixedTimeCorrectedStmt`, 3.3 `UniformConvergenceGreenKernelStmt`, 3.4
  `IntegralConvergenceGreenFunctionStmt`, 3.5 (corrected) `DiscreteDirichletProblemCorrectedStmt`;
* consequences of the certified reference model, from the model hypothesis itself: `CellSizeEstimateStmt`,
  `DegreeMeasureConvergenceStmt`, `GreenKernelUpperBoundStmt`, `ExitTimeUpperBoundStmt`, `MepsScalingInput`,
  `FrozenConeScalingLaw`, `DiscreteHolderContinuityCorrectedStep`.

Input binders of the counted 1.4 and 1.6 forms after this: 22 (24 minus the data `𝒮`, `ν`): 5.5 (existence), 2.4
(volume growth) and 1.3 (local set) are the Harmonic-Balls statements still bound.

Fourth pass (2026-11-12): the library proves the existence of the γ-LQG measure of every whole-plane GFF (with an
`α₀`-log singularity, `α₀ < Q`) and its coordinate change under `x ↦ (x - z)/r`. Three inputs are now theorems,
`MatedCRT/FirstPass/Derived/LQGMeasureInputs.lean` (9edd6aa8; axioms propext, Classical.choice, Quot.sound):
`FrozenLQGMeasureExistenceInsertion` (`frozenLQGMeasureExistenceInsertion_holds`), `WholePlaneLQGExistenceStep`
(`wholePlaneLQGExistenceStep_holds`; alias `FPWholePlaneLQGExistence`) and `WholePlaneLQGCoordinateChangeStep`
(`wholePlaneLQGCoordinateChangeStep_holds`; alias `FPWholePlaneLQGCoordinateChange`). The same pass also supplies the
inputs proved meanwhile in `Derived/ConeRadialDivergence.lean` (`FrozenConeRadialDivergenceCorrected`),
`Derived/ConeCircleLawUnique.lean` (`ConeCircleLawUniqueStep`) and `Derived/ConeWholePlaneFieldLaw.lean`
(`FPConeWholePlaneFieldLaw`). Input binders of the 1.4 and 1.6 forms after this: 16 (18 minus the data `𝒮`, `ν`).

Fifth pass (2026-11-12): `FrozenInsertionCoordinateRule` (#33, binder `hK`; the γ-LQG coordinate change rule for
one fixed affine map, Duplantier-Sheffield 2011, Proposition 2.1) is a theorem,
`MatedCRT/FirstPass/Derived/InsertionCoordinateRule.lean` (`frozenInsertionCoordinateRule_holds`; axioms propext,
Classical.choice, Quot.sound), from the library theorem
`LatticeProb.LQG.LQGSingularScaledLimit.ae_isLQGLimit_affine_fieldCircleAverage` through the bridges
`isWholePlaneGFF_iff`, `isLQGMeasureOfField_iff` and `isLQGLimit_iff`. Input binders of the 1.4 and 1.6 forms after
this: 15 (17 minus the data `𝒮`, `ν`).

Derived forms (binders of `T` -> binders of `T_derivedInputs`; 20 forms; binder names as in `T`):

| counted `T` | binders | supplied |
|---|---|---|
| `closed_1_4_lp_noSC_noSup` | 36 -> 17 | h0, h2, hdiv, hF3, h27, hFL, hGBC, hK, hE, hE1, h32, h611, hSup, hCons, hMono, hCompat, hThm11, hBdryHB, hProp56HB |
| `closed_1_6_lp_noSC_noSup` | 36 -> 17 | h0, h2, hdiv, hF3, h27, hFL, hGBC, hK, hE, hE1, h32, h611, hSup, hCons, hMono, hCompat, hThm11, hBdryHB, hProp56HB |
| `closed_2_3_lp` | 23 -> 11 | hGBC, h32, hSup, hCons, hMono, hCompat, hThm11, hProp56HB, hK, hE, hFL, hE1 |
| `closed_2_4_lp` | 18 -> 7 | hCentre, hOpen, hSup, hCons, hMono, hCompat, hThm11, hProp56, hK, hE, hFL |
| `closed_2_5_lp` | 22 -> 10 | hCentre, hOpen, hSup, hCons, hMono, hCompat, hThm11, hProp56, hK, hE, hFL, hE1 |
| `closed_2_6_lp` | 22 -> 10 | hCentre, hOpen, hSup, hCons, hMono, hCompat, hThm11, hProp56, hK, hE, hFL, hE1 |
| `closed_3_6_lp_uniform` | 6 -> 4 | _hm, _h32 |
| `closed_3_7_lp` | 6 -> 4 | hm, h32 |
| `closed_4_2_lp` | 36 -> 21 | h23, h24c, h33, hCentre, hOpen, hSup, hCons, hMono, hCompat, hThm11, hProp56, hK, hE, hFL, hE1 |
| `closed_5_1_lp_noSup` | 31 -> 14 | h27, hmodel, hFL, hGBC, hK, hE, hE1, h32, h611, hSup, hCons, hMono, hCompat, hBdry, hThm11, hProp56, hSC |
| `closed_5_3_clean` | 27 -> 14 | hCentre, hOpen, hSup, hCons, hMono, hCompat, hThm11, hProp56, hK, hE, hFL, hE1, hF3 |
| `closed_6_1_lp_noSup` | 33 -> 15 | h27, hmodel, hFL, hCentre, hK, hE, hE1, hOpen, h611, hSup, hCons, hMono, hCompat, hBdry, hThm11, hProp56, h0, h2 |
| `closed_6_4_lp` | 3 -> 1 | h0, h2 |
| `closed_6_10_lp` | 7 -> 5 | h0, h2 |
| `closed_7_1_lp` | 29 -> 15 | h0, h2, hGBC, h32, hSup, hCons, hMono, hCompat, hThm11, hProp56HB, hK, hE, hFL, hE1 |
| `closed_8_1_lp_noSup` | 46 -> 16 | hm, h210, h34, h214, h28, h35c, h218, hH, hcone, h23, h24c, h33, hCentre, hOpen, hSup, hCons, hMono, hCompat, hBdry, hThm11, hProp56, hK, hE, hFL, hE1, h27, hmodel, h611, h0, h2 |
| `firstPass_6_5_uniform` | 3 -> 1 | h0, h2 |
| `firstPass_6_7` | 9 -> 8 | hB1 |
| `firstPass_6_8` | 9 -> 8 | hB1 |
| `firstPass_6_9` | 9 -> 8 | hB1 |

Sixth pass (2026-11-12): seven more inputs are theorems without hypotheses,
`MatedCRT/FirstPass/Derived/HBBallMassHolds.lean` (axioms propext, Classical.choice, Quot.sound), all from the
whole-plane LQG ball-mass bounds of Ding-Gwynne (library theorem `LatticeProb.LQG.wholePlaneLQGBallMassBoundsLP_holds`,
Harmonic-Balls `wholePlaneLQGBallMassBounds_holds`): `hBG` (#45 `FrozenBerestyckiGwynneConeBallMass`,
`frozenBerestyckiGwynneConeBallMass_holds`), `hconf` (#29 `FrozenHBInitialConfinement`, `frozenHBInitialConfinement_holds`),
`hI2`/`hI2HB` (`frozenLQGVolumeGrowthAllScales_holds`), `h82` (`frozenTypicalPointManyGoodScales_holds`), `hBdry`/`hBdryHB`
(`frozenClusterBoundaryMeasureZero_holds`), `hExist`/`hExistHB` (HB Theorem 1.1 existence, `existenceHarmonicBallsStmt_holds`)
and `hloc`/`hlocHB` (`harmonicBallLocalSetStmt_holds`). Regenerated `Derived/Counted.lean`, `Derived/CountedMinimal.lean`
and `Audit/DerivedCountedAxioms.lean`. The 1.4 and 1.6 forms now bind four inputs: `hcore : CertifiedReferenceModelCore ν 𝒮`,
`hscale : QuantumConeScalingInput`, `hEnvS : ConeEnvironmentScalingUnderSLE 𝒮`, `hG15 : FrozenGreenFunctionCrudeBound 𝒮`.

Ninth pass (2026-11-13): `hEnvS : ConeEnvironmentScalingUnderSLE 𝒮` follows from `hscale` for every model
(Derived/EnvironmentScalingHolds.lean, `coneEnvironmentScalingUnderSLE_of_scaling`). The forms
`closed_1_4_lp_noSC_noSup_derivedInputs_envScaling` and `closed_1_6_lp_noSC_noSup_derivedInputs_envScaling` are the
`_reducedCore` forms (Derived/CoreGffLowerDerived.lean) without the binder `hEnvS`.

Tenth pass (2026-11-13): the Green kernel bounds `h12 : GreenKernelUpperBoundStmt 𝒮` (Lemma 2.15),
`h13 : GreenKernelLowerBoundStmt 𝒮` (Lemma 2.16) and the corrected discrete Hölder estimate
`h15 : FrozenDiscreteHolderContinuityCorrected 𝒮` (Lemma 3.2) follow, for a model with normalized law `ν` and valid
reference environments, from one one-sided mating-rigid set `G` (`hG : MatingRigidLEOn G`) that is full for every
`γ`-correlated two-sided Brownian law (`hGnull`): `greenKernelUpperBoundStmt_of_reference`,
`greenKernelLowerBoundStmt_of_reference`, `frozenDiscreteHolderContinuityCorrected_of_reference` (with
`cellSizeEstimateStmt_holds`). The forms `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity` and
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity` (Derived/EnvironmentScalingRigidity.lean) are the
`_envScaling` forms with `h12`, `h13`, `h15` replaced by the pair `(hGnull, hG)`.

Eleventh pass (2026-11-13): the pair `(hGnull, hG)` is supplied for `G := rigiditySet matingTriplePoints`.
`matingRigidLEOn_rigiditySet` proves `hG` with no input (the triple-point straddle lemma for the mating relation), and
`measure_compl_rigiditySet_matingTriplePoints_eq_zero` proves `hGnull` from four almost-sure properties of the
`γ`-correlated two-sided Brownian law: descent on both sides of each rational time (`hdesc`), Lévy's excursion-count
formula at each rational anchor in both time directions (`hexc`), no common weak contour pair (`hNC`), and the
triple-point size bound (`hZ3`: countable or of Hausdorff dimension `< 1/2`). The forms
`closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs` and
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs` (Derived/MatingRigidityAssembly.lean) are the
`_envScaling_rigidity` forms with `(hGnull, hG)` replaced by `(hdesc, hexc, hNC, hZ3)`.

Eleventh pass (2026-11-13): the lower half `hlow` of (1.8) (`F_ε(c₁ ε⁻¹) < 1/2`, Berestycki-Gwynne (1.8)) follows from
`h12`, `h13` and Berestycki-Gwynne Lemma 6.9 in its printed form (`h632`: `ψ₀` superpolynomial and independent of the
environment; inline hypothesis, no new Prop): `mεCdf_lower_of_lemma69` (Derived/CoreGffLowerOfLemma69.lean), through
the strong Lemma 6.11 (Derived/ExitTimeLowerLemma611Strong.lean) and `mεCdf_lower_of_exitTimeLowerTail`
(Derived/MepsLowerAssembly.lean); Lemma 2.18 is supplied by `exitTimeUpperBoundStmt_of_greenKernelUpper` (from `h12`).
The forms `closed_1_4_lp_noSC_noSup_derivedInputs_lemma69`, `closed_1_6_lp_noSC_noSup_derivedInputs_lemma69` are the
`_envScaling` forms, and `closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity_lemma69`,
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity_lemma69` (Derived/CoreGffLowerOfLemma69Rigidity.lean) the
`_envScaling_rigidity` forms, with `hlow` replaced by `h632`. Axioms propext, Classical.choice, Quot.sound.

Eleventh pass (2026-11-14): Berestycki-Gwynne Lemma 6.9 (`h632`, estimate (6.32)) follows from the uniform-start
invariance principle for the walk on the mated-CRT map, the named literature input `GMS21UniformStartInput`
([GMS21, Theorem 3.4], S6j/LitUniformStartInvariance.lean): `ExitTimeLowerTail.exitTimeLowerTail_of_uniformStart`
(S6j/ExitTimeLowerTail.lean), through the transfer of the walk event to planar Brownian motion modulo time
parametrization and the Brownian displacement-time bound (6.29) (S6j/ExitTailCombine.lean). The forms
`closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidity_uniformStart`,
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidity_uniformStart` (Derived/CoreGffLowerOfUniformStart.lean)
are the `_rigidity_lemma69` forms with `h632` replaced by `hN4 : GMS21UniformStartInput 𝒮`. Axioms propext,
Classical.choice, Quot.sound.

Eleventh pass (2026-11-14): Berestycki-Gwynne Lemma 6.10 (`h636`, estimate (6.36), the binder of the scaling
theorems `hEqLaw_of_scaling`, `hEqPath_of_scaling` and `isTightMeasureSet_data_interpWalkLaw_of_scaling`) follows from
the same named input `GMS21UniformStartInput`: `ExitTimeUpperTail.exitTimeUpperTail_of_uniformStart`
(S6j/ExitTimeUpperTail.lean). The walk side is the chain of successive exits of separation `δ - c`
(S6j/ExitTailUpperWalk.lean), the per-environment step is S6j/ExitTailUpperStep.lean, the Brownian estimate (6.22) is
S6j/ExitTailUpperBrownian.lean, with the displacement-time comparisons of Lattice-Probability
(`ContinuousPathStepTimeChain`, `ContinuousPathStepTimeStay`, `BrownianStayScaled`). The forms
`hEqLaw_of_uniformStart`, `hEqPath_of_uniformStart` and `isTightMeasureSet_data_interpWalkLaw_of_uniformStart`
(Derived/ScalingOfUniformStart.lean) are the scaling theorems with `h632` and `h636` both replaced by
`hN4 : GMS21UniformStartInput 𝒮`. The remaining binders of the scaling theorems are the Section 2 inputs
`h32, h213, h214, h217, h219`, the cone scaling `hEnvS` and the Lemma 6.13 bound `hbd`. Axioms propext,
Classical.choice, Quot.sound.

Eleventh pass (2026-11-14): the two reductions combined. The forms
`closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart`,
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart`
(Derived/CoreRigidityInputsUniformStart.lean) are the `_rigidityInputs` forms with `hlow` replaced by `hN4`
(equivalently, the `_rigidity_uniformStart` forms with `(hGnull, hG)` replaced by `(hdesc, hexc, hNC, hZ3)`). Binders:
`h1`, `h2`, `hN4`, `h10`, `h11`, `hdesc`, `hexc`, `hNC`, `hZ3`, `hGFF`, `hscale`. Axioms propext, Classical.choice,
Quot.sound.

Eleventh pass (2026-11-14): two of the four almost sure properties of correlated Brownian motion derived. `hdesc`
(descent on both sides of each rational time) is supplied in
`closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent`,
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent`
(Derived/CoreRigidityInputsRationalDescent.lean, 3b151695). `hexc` (Lévy's excursion-count formula at each rational
anchor in both time directions) holds for every `γ`-correlated two-sided Brownian law: Lattice-Probability
`LatticeProb.CorrelatedBM.ae_excursionCount_lrCoord` (Prob/CorrelatedBMExcursionCount.lean). The forms
`closed_1_4_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount`,
`closed_1_6_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount`
(Derived/CoreRigidityInputsExcursionCount.lean) are the `_ratDescent` forms without `hexc`. Binders: `h1`, `h2`,
`hN4`, `h10`, `h11`, `hNC`, `hZ3`, `hGFF`, `hscale`. Axioms propext, Classical.choice, Quot.sound.

Derived forms after the sixth pass (binders of `T` -> binders of `T_derivedInputs`; 31 forms):

| counted `T` | binders | supplied |
|---|---|---|
| `closed_1_4_lp_noSC_noSup` | 36 -> 6 | hBG, h0, h2, hV, hdiv, hF3, h27, hFL, hstd, hGBC, hconf, hK, hE, hE1, hE2, h32, h611, h82, hSup, hCons, hMono, hCompat, hThm11, hrescale, hND, hBdryHB, hExistHB, hProp56HB, hI2HB, hlocHB |
| `closed_1_6_lp_noSC_noSup` | 36 -> 6 | hBG, h0, h2, hV, hdiv, hF3, h27, hFL, hstd, hGBC, hconf, hK, hE, hE1, hE2, h32, h611, h82, hSup, hCons, hMono, hCompat, hThm11, hrescale, hND, hBdryHB, hExistHB, hProp56HB, hI2HB, hlocHB |
| `closed_2_3_lp` | 23 -> 1 | hBG, hND, hstd, hGBC, h32, hSup, hCons, hMono, hCompat, hBdryHB, hExistHB, hThm11, hProp56HB, hconf, hI2HB, hK, hlocHB, hE, hFL, hE1, hE2, hrescale |
| `closed_2_4_lp` | 18 -> 0 | hstd, hCentre, hOpen, hSup, hCons, hMono, hCompat, hBdry, hExist, hThm11, hProp56, hconf, hI2, hK, hloc, hE, hFL, hBG |
| `closed_2_5_lp` | 22 -> 1 | hstd, hCentre, hOpen, hSup, hCons, hMono, hCompat, hBdry, hExist, hThm11, hProp56, hconf, hI2, hK, hloc, hE, hFL, hBG, hE1, hE2, hND |
| `closed_2_6_lp` | 22 -> 1 | hstd, hCentre, hOpen, hSup, hCons, hMono, hCompat, hBdry, hExist, hThm11, hProp56, hconf, hI2, hK, hloc, hE, hFL, hBG, hE1, hE2, hND |
| `closed_2_19_ownBinders` | 4 -> 3 | hBG |
| `closed_3_3_ownBinders` | 4 -> 3 | hBG |
| `closed_3_4_ownBinders` | 4 -> 3 | hBG |
| `closed_3_5_lp` | 4 -> 3 | hBG |
| `closed_3_6_lp_uniform` | 6 -> 4 | _hm, _h32 |
| `closed_3_7_lp` | 6 -> 3 | hBG, hm, h32 |
| `closed_4_1_lp` | 4 -> 3 | hBG |
| `closed_4_2_lp` | 36 -> 11 | h23, h24c, h33, hstd, hCentre, hOpen, hSup, hCons, hMono, hCompat, hBdry, hExist, hThm11, hProp56, hconf, hI2, hK, hloc, hE, hFL, hBG, hE1, hE2, hND, hrescale |
| `closed_4_7_ownBinders` | 4 -> 3 | hBG |
| `closed_4_8_lp` | 4 -> 3 | hBG |
| `closed_5_1_lp_noSup` | 31 -> 5 | h27, hmodel, hFL, hstd, hGBC, hconf, hK, hE, hE1, hE2, hND, h32, h611, h82, hI2, hSup, hCons, hMono, hCompat, hBdry, hEx, hThm11, hProp56, hloc, hSC, hBG |
| `closed_5_2_ownBinders` | 4 -> 3 | hBG |
| `closed_5_3_clean` | 27 -> 5 | hBG, hND, hstd, hCentre, hOpen, hSup, hCons, hMono, hCompat, hBdry, hExist, hThm11, hProp56, hconf, hI2, hK, hloc, hE, hFL, hE1, hE2, hF3 |
| `closed_6_1_lp_noSup` | 33 -> 5 | h27, hmodel, hFL, hstd, hCentre, hconf, hK, hE, hE1, hE2, hND, hOpen, h611, h82, hI2, hSup, hCons, hMono, hCompat, hBdry, hExist, hThm11, hProp56, hloc, hBG, h0, h2, hV |
| `closed_6_4_lp` | 3 -> 0 | h0, h2, hV |
| `closed_6_10_lp` | 7 -> 3 | hBG, h0, h2, hV |
| `closed_7_1_lp` | 29 -> 4 | hBG, h0, h2, hV, hND, hstd, hGBC, h32, hSup, hCons, hMono, hCompat, hBdryHB, hExistHB, hThm11, hProp56HB, hconf, hI2HB, hK, hlocHB, hE, hFL, hE1, hE2, hrescale |
| `closed_8_1_lp_noSup` | 46 -> 5 | hm, h210, h34, h214, h28, h35c, h218, hH, hcone, h23, h24c, h33, hstd, hCentre, hOpen, hSup, hCons, hMono, hCompat, hBdry, hExist, hThm11, hProp56, hconf, hI2, hK, hloc, hE, hFL, hBG, hE1, hE2, hND, hrescale, h27, hmodel, h611, h82, h0, h2, hV |
| `firstPass_2_17_ownBinders` | 1 -> 0 | hBG |
| `firstPass_3_1_faithful` | 5 -> 4 | h27 |
| `firstPass_4_6_h35c` | 8 -> 7 | h27 |
| `firstPass_6_5_uniform` | 3 -> 0 | h0, h2, hV |
| `firstPass_6_7` | 9 -> 6 | hCC, hB1, hBG |
| `firstPass_6_8` | 9 -> 6 | hCC, hB1, hBG |
| `firstPass_6_9` | 9 -> 6 | hCC, hB1, hBG |

### Hypotheses the conclusions do not need (second stage; 2026-11-11)

`MatedCRT/FirstPass/Derived/CountedMinimal.lean` (generated; axiom audit `MatedCRT/Audit/MinimalCountedAxioms.lean`:
propext, Classical.choice, Quot.sound). For a counted theorem `T` (in its form of the table above when it has one),
`T_minimalInputs` states the same conclusion from a proper subset of the hypotheses: the conclusion follows without the
others by theorems already in the repository (search over all compiled theorems of this repository and of the
Harmonic-Balls package; the compiled file is the check). No binder is added and `T` is unchanged. The search finds no
such reduction for the other counted theorems; in particular the forms of 1.4 and 1.6 keep their 17 binders.

| counted `T` | binders | not needed |
|---|---|---|
| `closed_4_2_lp` | 21 -> 20 | hcone (`FrozenConeScalingLaw`) |
| `firstPass_6_7` | 8 -> 6 | hLit, hμ (`LitQuantumConeLQGMeasureExistence`) |
| `firstPass_6_8` | 8 -> 6 | hLit, hμ |
| `firstPass_6_9` | 8 -> 6 | hLit, hμ |

## Appendix B path: forms with the occupation identity or the strong compatibility derived (2026-11-11)

The counted declarations of the Table are unchanged. The forms below have the same conclusions as the counted forms of
their rows. Axioms: `MatedCRT/Audit/AppendixBAxioms.lean` (3c1fada4; 14 lines, each prints `propext`,
`Classical.choice`, `Quot.sound`).

| result | form | file:line | commit | binders | relation to the counted form of the Table |
|---|---|---|---|---|---|
| 5.1 | `closed_5_1_lp_noSup_noSC` | MatedCRT/FirstPass/Closure/Clean51NoSC.lean:24 | 488d5bf2 | 30: data 2 core 1 External 1 Step 1 HB 13 Frozen 11 DRAFT 1 | Strict sub-list of `closed_5_1_lp_noSup` (31 binders), same order: `hSC : ClusterStrongCompatibilityStmt` is supplied by `frozenClusterStrongCompatibility_of_volumeGrowth hI2` (Closure/HSCDerived.lean:19), as in rows 1.4n and 1.6n. Rule 1 applies. The Table row 5.1 is not switched here, because `closed_5_1_lp_noSup_derivedInputs` (previous section) is stated over the Table form. |
| 1.4 | `closed_1_4_derivedOccupation` | MatedCRT/FirstPass/Closure/AppendixBRewire.lean:156 | c4e59c78 | 35 | Not a sub-list of `closed_1_4_lp_noSC_noSup` (36 binders). hF3 and hGBC are supplied (`frozenDiskGreenNonnegCont_holds`, `frozenGreenBallCentre_holds`). `hcore : CertifiedReferenceModelCore ν 𝒮` is replaced by `hcoreB : CertifiedReferenceModelCoreNoOccupation ν 𝒮` (AppendixBRewire.lean:65: the conjuncts of the core other than `FrozenLBMGreenOccupationRescaled 𝒮`; a sub-conjunction, not a new frozen Prop). One binder is added, hGFF. The other 32 binders are those of the counted form. |
| 1.6 | `closed_1_6_derivedOccupation` | MatedCRT/FirstPass/Closure/AppendixBRewire.lean:206 | c4e59c78 | 35 | As row 1.4, over `closed_1_6_lp_noSC_noSup`. |

- **hGFF** is an inline `∀` Prop, written once per file (OccupationClosureCone.lean:49, AppendixBRewire.lean:103); no
  file defines it and it is not printed verbatim in the paper. Statement: for every whole-plane GFF model, every
  strictly increasing sequence of dyadic scales along which the gaps of the regularized clocks of `h^ℂ - γ log|·|`
  satisfy the summable bounds, and every countable family of measurable subsets of the disc `B_r(z)`, almost surely
  the expected occupation measure of the limit clock up to the exit time of the disc is finite and agrees on the
  family with the chaos limit weighted by twice the Green function of the disc. Math desk: TRUE as typed (MQ-fp-1,
  confirmed by the independent check; notes/fp-gaps/MATH-ANSWERS.md); its written reduction uses the convergence of
  the chaos (Berestycki 2017, Theorem 1.1), the occupation formula of killed Brownian motion on a disc and the
  polarity of points. It is a cited input.
- **Whether `closed_1_4_derivedOccupation` and `closed_1_6_derivedOccupation` replace the counted forms of 1.4 and 1.6
  is an operator decision** (rule 1 does not apply: one binder is added).
- The other counted theorems that bind `hC : CertifiedReferenceModel ν 𝒮` lose the Appendix B conjunct in the same way,
  by `hC := hcoreB.toModel_of_fieldLaw hFL hGFF hT` (AppendixBRewire.lean:140); no wrapper is committed for them.

### Appendix B input hGFF: killed occupation identity proved (2026-11-14)

- `KilledBrownianOccupationOnBall z r` (Potential.lean:275; the binder `hS0` of the `closed`-`closed5` forms and the
  binder `hK` of `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation`, LimClockOccupationReduction.lean:130)
  is now a theorem for every `z`, `r`: `killedBrownianOccupationOnBall` (FirstPass/Derived/KilledBrownianOccupationHolds.lean,
  0de6b9d9). Route: Dynkin at the exit time, logarithmic potential, exit averages of the Newtonian kernel on a disc
  (4e7df48f, 59a52c94, 84cb0edb, 8c25244f, 226277ea), smooth-test agreement of the killed occupation measure with
  `2 G(y, x) dx` (8a541e55), and equality of finite measures from smooth compactly supported tests (Lattice-Probability
  `measure_eq_of_forall_integral_contDiff_hasCompactSupport_eq`). Axioms propext, Classical.choice, Quot.sound.
- Derived wrapper `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation_derived` (same file): `hGFF` follows
  from `hlaw` and the two remaining inputs `hU` (uniform integrability of the regularized clock integrals) and `hF0`
  (finiteness of the Green-weighted chaos at the pole 0). No counted form changes.
- `hF0` is now a theorem: `ae_gmcGreenMeasure_ball_lt_top_pole_zero` (FirstPass/Derived/GmcGreenMassAtPole.lean, f1f4b60a):
  for a whole-plane GFF, `0 < γ < 2`, `ρ < ρ₂ < 1` and a disc `B_r(z)` containing 0, almost surely the Green-weighted
  cut-off γ-LQG mass of `B_r(z)` with pole 0 is finite. Route: first moments tilted by `exp(-γ h_τ(0))` on the
  `e`-adic annuli about 0 (574b8b4c, 1aed8eee), Borel-Cantelli on the circle averages at 0 (55f50cda), the dyadic
  Green bound at the pole, no atom at 0, and finiteness on compact sets away from 0. Axioms propext,
  Classical.choice, Quot.sound.
- Derived wrapper `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_killedOccupation_F0_derived`
  (FirstPass/Derived/KilledBrownianOccupationF0Holds.lean): `hGFF` follows from `hlaw` and `hU` alone. The remaining
  input of hGFF is `hU`. No counted form changes.
- `hU` is a theorem: `uniformIntegrable_setLIntegral_regClockMeasure_dyadic`
  (FirstPass/Derived/RegClockUniformIntegrable.lean, 7307943d), with the derived wrapper
  `frozenLBMGreenOccupationRescaled_of_coneGFFLaw_derived` (same file): `hGFF` follows from `hlaw` alone. Route
  (GRV16 Thm 2.7(1), the L¹ Cauchy argument): finite first moments `E T_ε ≤ 2^{γ²} M E[σ]` from the first moment of
  the circle-average density (`lintegral_prod_setLIntegral_regClockMeasure_le`); below the distance from 0 to
  `tsupport g`, `E|T_{2^{-m-1}} - T_{2^{-m}}| ≤ K 2^{-κm}` (U4 near-diagonal occupation moment 804dde9..21aa9827 in
  the library, U5c 6c52328d, U5d fbb148a5); summable L¹ increments give one integrable dominating function (library
  `UniformIntegrableDominated`, 0a7c271), hence uniform integrability along every subsequence. Axioms propext,
  Classical.choice, Quot.sound. No counted form changes.
- `hGFF` is a theorem: `KilledOccupation.ae_mem_occupationAgreementEvent_holds`
  (FirstPass/Derived/RevuzOccupationHolds.lean, 6afaa549), exactly the binder `hGFF` of the counted forms, from
  `ae_mem_occupationAgreementEvent_of_killedOccupation` with its three inputs supplied (`killedBrownianOccupationOnBall`,
  `uniformIntegrable_setLIntegral_regClockMeasure_dyadic`, `ae_gmcGreenMeasure_ball_lt_top_pole_zero`). Same file:
  `coneUnitDiskGFFLaw_holds` (`hlaw` from `coneWholePlaneFieldLawStep_holds`), `frozenLBMGreenOccupationRescaled_holds`
  (conjunct 9 of `CertifiedReferenceModelCore`, no hypothesis), and the counted forms
  `closed_1_{4,6}_lp_noSC_noSup_derivedInputs_envScaling_rigidityInputs_uniformStart_ratDescent_excursionCount_cauchyGHM_revuz`
  = the `_cauchyGHM` forms (CoreRigidityInputsNoContourTriple.lean) with `hGFF` supplied; same conclusions, binders
  h1 h2 hN4 h10 h11 hCP hGHM hscale. Axioms propext, Classical.choice, Quot.sound; 0 warnings.

### Cauchy point polarity supplied (2026-11-14)

`LatticeProb.CorrelatedBM.cauchyPointPolarInput` (Lattice-Probability `Prob/CauchyPointPolar.lean`, 15c01bd) proves
the input `hCP`. Its proof uses first-passage estimates and a grid first-hit decomposition to establish a polarity
estimate, then passes to all levels using left continuity of the passage times.

`FirstPass/Derived/RevuzOccupationCauchyPolar.lean` (5120259b) supplies this theorem in four derived forms of
Theorems 1.4 and 1.6. The `_cauchyGHM_polar` forms retain `hGFF`; the `_cauchyGHM_revuz_polar` forms also supply
`hGFF` via the occupation identity above. The latter forms have the same conclusions as the `_cauchyGHM_revuz`
forms and retain the input hypotheses `h1`, `h2`, `hN4`, `h10`, `h11`, `hGHM`, and `hscale`.

### Uniform-start input: block-exit route (2026-11-19)

Status of `hN4 : GMS21UniformStartInput 𝒮` (the named literature input of the forms above; not yet discharged).
The input is reduced to walk-side block-exit data by new non-counted leaves, none of which removes a counted
hypothesis:
- `FirstPass/Derived/UniformStartGoodSandwich.lean:166` (`goodG`) is the event on which the stopped walk from every
  vertex of the closed ball of radius `ρ` satisfies the all-set inequality against stopped planar Brownian motion.
- `BlockExitSkeletonJoinParameters.lean` and `BlockExitSkeletonJoinParametersDerived.lean`
  (`exists_blockExit_parameters_allSet_le_derived`, the latter with the transfer of a one-sided Prokhorov bound through
  skeletons supplied by `LatticeProb.measure_preimage_le_of_prokhorovLE_of_approx`) choose the block parameters
  `(s, d', δ₀, N)` from `(ρ, R, κ)`, independently of the environment and the mesh, and record the Brownian reach
  bound (`κ/16`) within `N` blocks.
- `BlockExitSkeletonGoodG.lean` (`exists_blockExit_parameters_mem_goodG`, `ae_eventually_mem_goodG_of_blockExit`,
  `gms21UniformStartInput_of_blockExit`): `GMS21UniformStartInput 𝒮` follows from the single walk-side hypothesis
  `hwalk`: for every valid environment, `0 < ρ < R`, `κ > 0`, null mesh `e` and all positive `(s, d', δ₀, N)` at which
  Brownian motion from `closedBall 0 ρ` reaches the far set within `N` blocks outside probability `(κ/2)/16`: almost
  surely eventually in the mesh, at every vertex in `closedBall 0 ρ`, the laws of the block-exit positions of the
  interpolated walk and of planar Brownian motion satisfy `ProkhorovLE` at `(δ₀, (κ/2)/4)` and the walk misses the far
  set within `N` blocks with probability at most `(κ/2)/8`.
- `BlockExitSkeletonGoodGSandwich.lean` (`exists_blockExit_parameters_mem_goodG_sandwich`,
  `ae_eventually_mem_goodG_of_blockExit_sandwich`, `gms21UniformStartInput_of_blockExit_sandwich`): the same with the
  frozen set `farSet (ball 0 R) d'` replaced by `F = ballFrozenSet s (R + d')`
  (`BlockExitGridCellFrozen.lean`: the union of the closed grid cells of mesh `s` missing `ball 0 (R + d')`; measurable,
  grid compatible, and `farSet (ball 0 R) d₁ ⊆ F ⊆ farSet (ball 0 R) d'` for `d' + 2 s ≤ d₁`). The block parameters
  `(s, d', d₁, δ₀, N)` are independent of `F` (`BlockExitSkeletonJoinParametersSandwichDerived.lean`). The walk-side
  hypothesis `hwalk` is then stated for all positive `(s, d', δ₀, N)` and every `d₁ ≥ d' + 2 s`, with the Prokhorov
  bound and the non-reach bound for the walk frozen on `F`, and the Brownian reach guard `(κ/2)/16` at `F`. Its chain
  ingredients are the grid-compatible frozen kernels of `BrownianBlockExitChain.lean`
  (`prokhorovLE_chainSeqLaw_frozenBlockExit_of_gridLineStable`); the walk-side adapter for `F` is not yet written.
- The reach guard is essential: without it `hwalk` is false (`N = 0`, the walk cannot reach the far set).
- Remaining for `hwalk`: the closeness of the one-step block-exit kernels (invariance principle input, `hclose`) and the
  chain from the one-step bound to the `N`-block law (`BlockExitWalk*.lean`), and the walk reach bound.
- `GMS21UniformStartOfHdiag.lean` (`gms21UniformStartInput_of_hdiag`): `GMS21UniformStartInput 𝒮` follows from the
  single diagonal estimate `hdiag`, stated almost surely, eventually in the mesh, along every null sequence. This is the
  form the literature does not give for the `γ`-quantum cone: the convergence of the walk (Gwynne-Miller-Sheffield,
  Tutte embedding of the mated-CRT map, Theorem 3.4) is in probability.
- `UniformStartSubsequence.lean` and `GMS21UniformStartOfHdiagProb.lean` (`gms21UniformStartInput_of_hdiagProb`):
  `GMS21UniformStartInput 𝒮` follows from `hdiagProb`, the diagonal estimate in probability: for every valid
  environment, `s > 0`, `ρ₀` and `δ > 0` there is a scale `θ ∈ (0, s / 2]` with `24 θ / s ≤ δ / 2` such that for every
  `θ' > 0` there is `ε₀ > 0` with, for all `ε ∈ (0, ε₀)`, the outer measure of the set of environments in which some
  point `y` off `ballFrozenSet s ρ₀` and some vertex `u` within `θ` of `y` have the one-step block-exit kernel of the
  walk not `(δ, δ / 2)`-close to the planar Brownian exit law from `u` out of the block of `y`, at most `θ'`. The chain
  of the previous items is rerun along a subsequence of each null sequence (`ae_eventually_mem_goodG_of_blockExit_sandwich_sub`,
  `exists_eps_uniformStart_bound_sub`, `gms21UniformStartInput_of_blockExit_sandwich_sub`). Two general measure-theory
  statements (first Borel-Cantelli along a subsequence for arbitrary sets, reverse Fatou along subsequences) are
  inline hypotheses of `gms21UniformStartInput_of_hdiagProb`; `gms21UniformStartInput_of_hdiagProb_derived`
  (`GMS21UniformStartOfHdiagProbDerived.lean`) supplies both from the library
  (`LatticeProb.exists_strictMono_ae_eventually_notMem_of_tendsto_measure`,
  `LatticeProb.exists_eps_measure_compl_le_of_ae_eventually_subseq`). `hdiagProb` is the remaining content of
  `GMS21UniformStartInput`.
The alternative inner-ball cellwise chain (`UniformStartGoodPackageInner.lean`, `GMS21UniformStartOfCellwiseInner.lean`)
is kept as a second route.

### Brownian-limit input in reference form; time-change inputs proved (2026-11-19)

- `FirstPass/Derived/BG20ReferenceOfEveryEnvironment.lean` (`bg20Reference_of_bg20`): the binder `hBG` of
  `randomWalkToLBMStmt_of_bg20` (Berestycki-Gwynne (2020), Theorem 1.2, in every valid environment) implies, given
  `h1` and `h10`, the binder `hBGref`: one valid environment of a model with law `ν`, with measurable versions of its
  field and curve, along which the convergence holds. So `hBGref` is no stronger than `hBG`.
- `FirstPass/Derived/RandomWalkToLBMStmtOfBG20Reference.lean` (`randomWalkToLBMStmt_of_bg20_reference`,
  `closed_1_4_quantumConeScaling_coneDimension_bg20ref`, `closed_1_6_quantumConeScaling_coneDimension_bg20ref`):
  Theorems 1.4 and 1.6 with binders `h1 h2 hN4 h10 hBGref`. The convergence is transferred from the reference
  environment to every valid environment sharing `ν` (identical joint law of curve and multiplicities,
  `FirstPass/Derived/IdentificationTransfer.lean`).
- The three literature inputs of `External/RevuzTimeChange.lean`, ingredients of the identification of subsequential
  limits as time-changed Brownian motion (Berestycki-Gwynne (2020), Proposition 7.10) inside `hBGref`, are proved;
  none is a counted binder:
  - `RevuzInvariantInput` (`:128`): `revuzInvariantInput_derived` (`FirstPass/Derived/RevuzInvariant.lean`);
  - `TimeChangeInvariantUniqueInput` (`:136`): `timeChangeInvariantUniqueInput_derived`
    (`FirstPass/Derived/TimeChangeInvariantUnique.lean`);
  - `RevuzUniquenessInput` (`:120`): `revuzUniquenessInput_derived` (`FirstPass/Derived/RevuzUniqueness.lean`;
    Fukushima-Oshima-Takeda (2011), Theorem 5.1.4, via localizers of the σ-finite Revuz measure and the dyadic Taylor
    expansion of `log(1 + N²)` for the difference `N` of two window integrals).
  `FirstPass/Derived/MarkovTimeChangeRevuzUniqueDerived.lean`
  (`exists_pathLaw_time_scale_of_isMarkovTCBM_revuzUnique_derived`,
  `exists_measurable_timeScale_of_isMarkovTCBM_revuzUnique_derived`) states the time-change identifications with no
  Revuz hypothesis left. Remaining content of `hBGref` (a description only: no Lean statement isolates these parts,
  and no counted route imports the wrappers above yet): the other parts of the proof of Berestycki-Gwynne (2020),
  Theorem 1.2 (Markov property of subsequential limits, invariance of the LQG measure, the time-change constant being
  deterministic) and the existence of a valid environment realizing the reference construction (`h1`, `h10`).

### Lemma 7.4 (binder `hN5`): the Markov half is proved, the time-change half remains (2026-11-19)

- `FirstPass/Derived/MarkovHalfOfHN5.lean` (`ae_markovAt_of_tendsto_law_interpWalkLaw`): if the interpolated walk
  laws `P̃^{ε_n}` converge in law to `ν₂`, the quenched walk laws are equicontinuous in law and `m_{ε_n} → ∞`, then for
  every `(z₀, t)` the limit `s` satisfies `MarkovAt s z₀ t` for `ν₂`-almost every `s`.
- `FirstPass/Derived/HN5OfDefinesTimeChange.lean` (`hN5_of_defines`): the counted binder `hN5` (conclusion
  `∀ᵐ P ∂ν₂, IsMarkovTCBM P`) follows from `hEnvS`, `hN4`, `h1`, `h10`, `hU` and a binder `hN5a` with the same premises
  and the conclusion `∀ᵐ P ∂ν₂, DefinesTimeChangedBM P`. The equicontinuity in law comes from `hEqLaw_of_uniformStart_holder`
  and `m_{ε_n} → ∞` from `tendsto_mε_atTop_of_uniformStart`, both from `hN4`; the sequence is shifted so that
  `0 < m_{ε_n}` for every `n`.
- `FirstPass/Derived/ConvergenceOfIDLAOfMarkovLimitHN5a.lean` (`randomWalkToLBMStmt_of_markovLimit_derived_hN5a`):
  `randomWalkToLBMStmt_of_markovLimit_derived` with `hN5` replaced by `hN5a`. The counted theorems are unchanged.
- `hN5a` is a conjunct of the conclusion of `hN5`, hence no stronger than `hN5`. Remaining content of Lemma 7.4:
  that every subsequential limit defines a time change of Brownian motion (the part of the argument of
  Berestycki-Gwynne (2020) resting on [GMS21, Theorem 3.4] and Propositions 6.1 and 6.14 and the Skorokhod
  representation theorem); no Lean statement of it is proved yet.

#### Lemma 7.4, continued: no flat intervals, strict monotonicity of the time change (2026-11-19)

- `FirstPass/Derived/NoFlatOfTendstoLaw.lean` (`ae_forall_apply_constantOnInterval_eq_zero_of_tendsto_law_interpWalkLaw`):
  if the interpolated walk laws converge in law to `ν₂` then `ν₂`-almost surely, for every `z`, `P_z` gives mass zero
  to the paths constant on an interval of positive length (Berestycki-Gwynne (2020), Proposition 6.1, last claim),
  from `hEnvS`, `hN4`, `h1`, `h10`, `hU` (the inputs of the window estimate are supplied as in
  `hEqLaw_of_uniformStart_holder`).
- `FirstPass/Derived/HN5OfContinuousTimeChange.lean`: `definesTimeChangedBM_of_monotone_of_noFlat` (a continuous
  nondecreasing time change whose law has no flat interval is strictly increasing) and
  `hN5a_of_continuousTimeChange` (`hN5a` from `hN5b`, the same premises with `Monotone` in place of `StrictMono`).
- `FirstPass/Derived/ConvergenceOfIDLAOfMarkovLimitHN5b.lean` (`randomWalkToLBMStmt_of_markovLimit_derived_hN5b`):
  `randomWalkToLBMStmt_of_markovLimit_derived` with `hN5` replaced by `hN5b`. `hN5b` is implied by `hN5` (strictly
  increasing implies nondecreasing), so it is no stronger. Remaining content of Lemma 7.4: that a subsequential limit
  is a continuous nondecreasing time change of Brownian motion (equality of the laws of the stopped curve classes from
  `hN4`, then a coupling); blueprint `notes/blueprints/d2-11-N5a.md` in the fleet directory.
