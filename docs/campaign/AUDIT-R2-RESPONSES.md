# Audit round 2: responses (IDLA)

Responses to the round-2 audit of the IDLA paper (arXiv:2211.04891): notes/fp-gaps/OPUS-AUDIT-R2.md in the fleet directory (not in the repository). Finding IDs are those of the audit: K1 (line 33), M5 to M8 (lines 89 to 119), M13 to M15 (lines 153 to 176), MINOR IDLA (A) and (B) (lines 193 to 229), and the IDLA rows marked Partial or N in the audit tables (lines 230 to 309).

Status values: FIXED <commit> (text or Lean change landed); IN PROGRESS (<worker>) (owned by a worker, not landed); Responded (<reason>) (no change in this repository, with the reason; new mathematics is routed to the operator).

## Findings

| Row | Finding | Status |
|---|---|---|
| K1 | `FrozenOneSidedBoundaryContinuity` is false as typed (`FirstPass/S3i/Frozen.lean:44`) | IN PROGRESS (z9) |
| M5 | Campaign and audit voice in the paper body (subsection "Uses of Lemma 3.6", bracketed tags, Appendices B and C) | FIXED 9c18ae6, 0204400, 21d373b |
| M6 | Email locators for C4 and C34 (proofs of Lemmas 5.3 and 5.4) | FIXED 453b2ec, ed7f547 |
| M7 | Lemma 3.5 Step 3: limit Laplacian displayed as -1 (new mathematics: [C17] edit) | Responded (routed MQ-li-7b-d; awaiting math answer; truth check pending) |
| M8 | Proposition 7.1 Steps 1 and 2 defects (GAPS E-x2-1) omitted from the email | FIXED 453b2ec (email item, flagged open), ed7f547 (GAPS status) |
| M13 | B5: Appendix B theorem is a frozen conjunct of `CertifiedReferenceModelCore` | IN PROGRESS (z10; scope notes/li-tmp-z10-appB.md; gaps MQ-li-8a to 8e) |
| M14 | B6: COUNTED.md and `firstPassMain_1_4_full` / `_1_6_full` | FIXED 1f2548b (z1) |
| M15 | Non-vacuity of the coupling: GFF part | IN PROGRESS (z8; ledger section by z1; quantum-cone and LQG-measure existence cited, MQ-li-8f) |

### MINOR IDLA (A)

| Row | Finding | Status |
|---|---|---|
| A1 | [C32] annulus overlap (consecutive 7-adic annuli) | Responded (new mathematics, routed MQ-li-7b-d) |
| A2 | Unmarked edits at the Lemma 7.4 proof, Step 3 of Proposition 7.1 and the Lemma 7.2 display | FIXED 9c18ae6 |
| A3 | C29 inside the email tag "(C26 to C31)" | FIXED 453b2ec, ed7f547 |
| A4 | C25 email calls the support "positive stopped" | FIXED 453b2ec (email); ed7f547 (CORRECTIONS.md [C25]) |
| A5 | Theorem 4.1 proof typos at 2229, 2251, 2278 | Responded (routed MQ-li-7b-d) |
| A6 | C31 writes `\overline\Theta` | FIXED 453b2ec (email writes cl(Θ)) |
| A7 | Cluster-identity header names Lemma 4.3 | FIXED 453b2ec |
| A8 | Local `m_0` in the Lemma 6.8 replacement proof (paper line 3147) | FIXED 9c18ae6 (renamed varpi_0) |
| A9 | κ reused as a constant | Responded (notation only; left as is) |
| A10 | C11 list omits the Theorem 4.1 and Lemma 3.4 proofs | FIXED 453b2ec |
| A11 | "author-approved" and E-xx tags in paper comments | FIXED 9c18ae6 |
| A12 | `ERRATA-INTERNAL.md` stale lines | FIXED ed7f547 |
| A13 | `CORRECTIONS.md` [C1] writes c_0 for the limit constant | FIXED ed7f547 |
| A14 | [C13] same-walk rate presented as required | FIXED 453b2ec, ed7f547 (presented as optional) |

### MINOR IDLA (B)

| Row | Finding | Status |
|---|---|---|
| B1 | `hsup`: `ConeLeastSupersolutionTransfer` removes nothing (`FirstPass/S5kLemma31.lean:43`) | Responded (routed MQ-li-4) |
| B2 | Duplicate binders `hsc`, `hrp`, `hind` and six `*HB` duplicates (`S5Cited.lean:39-75`) | FIXED b5f433a, cf167df (Main.lean pointing: z1) |
| B3 | Derived-but-cited binders `hE1`/`hE2`, `hSC`, core conjunct 18 (truth UNSURE), `hBG` (truth pending) | IN PROGRESS (z12, p2-audit-r2-b3-owner-and-marker): analysis recorded in the section below; no binder discharged; `hSC`: every bounded open U derived in Lean from `hI2` (`LQGVolumeGrowthAllScalesStmt`) by Green-regular exhaustion (HB `Proofs/Sec5/StrongCompatibilityAssembly.lean:15`; axioms propext, Classical.choice, Quot.sound; exhaustion lemma `Proofs/Sec5/ExhaustionClusterCompatibility.lean`, no sorry); proof route differs from the printed proof of Lemma 5.8 (the Green-regular HB `Proofs/Sec5/GreenRegularLQGCompatibility.lean:25` is not used by that chain); the IDLA derivation is `frozenClusterStrongCompatibility_of_volumeGrowth` (`MatedCRT/FirstPass/Closure/HSCDerived.lean`, commit db6f210; axioms standard); `hSC` stays cited in IDLA; truth reduces to `hI2` and the exhaustion step (not in the printed source); `hE1`, `hE2` cited (MQ-li-8f); `hBG` literature input (truth pending); conjunct 18 cited (MQ-li-6) |
| B4 | Wrong claim at `FirstPass/S1d.lean:30` | FIXED 1ef63ce (z5) |
| B5 | Lemma 7.4: no counted theorem; `Draft/Section7.lean:67` still has ∀t | FIXED ff66f92 (`closed_7_4_corrected`) |
| B6 | LP `areaParam`: conditional on a vague limit; "is proved" docstring | FIXED fbc6a0e (z5, LP) |
| B7 | LP `RescaledEnvironmentInput` (self-labelled possibly false, unused): delete | Responded (1ef63ce): declaration kept, never deleted; docstring marked RETIRED at `MatedCRT/Proofs/Sec1/EnvironmentScaling.lean:76` |
| B8 | Docstrings cite `exists_isCorrelatedBM2` | FIXED fbc6a0e (LP worktree `/home/nitro/lean/LP-idla-phase2`, branch idla/phase2): the name is absent at fbc6a0e and at worktree HEAD 8354077; the LP pin in IDLA still cites it at `LatticeProb/Bonanno/MatedCRTHarmonic/Frozen/IsCorrelatedBM2.lean:13` (pin update is the operator's) |

## Round-1 items still open in the tables (audit lines 230 to 268)

| Row | Item | Status |
|---|---|---|
| R1-A7 | IDLA A7 (Partial) | FIXED 9c18ae6, 21d373b (= M5) |
| R1-C11 | IDLA C11 list (Partial) | FIXED 453b2ec (= A10) |
| R1-B5 | IDLA B5 (Partial) | IN PROGRESS (z10) (= M13) |
| R1-B6 | IDLA B6 (No) | FIXED 1f2548b (= M14) |
| R1-B7 | IDLA B7 (No; the fix is vacuous) | IN PROGRESS (z9) (= K1) |
| R1-m2 | IDLA m2, `hsup` (No) | Responded (routed MQ-li-4) (= B1) |
| R1-m3 | IDLA m3, `closed_3_1` is the weak form (No) | IN PROGRESS (z1; COUNTED.md counts `closed_3_1_faithful` and `closed_3_1_countable`) |
| R1-m4 | IDLA m4, Lemma 7.4 has no counted theorem (No) | FIXED ff66f92 (= B5) |
| R1-m7 | IDLA m7, LP non-vacuity assumed (M15) | IN PROGRESS (z8; ledger z1) (= M15) |

## IDLA part (A) rows marked P or N (audit lines 269 to 309)

| Row | Item | Status |
|---|---|---|
| P-C1/C17 | C17 partial (proof coefficients) | Responded (= M7, routed MQ-li-7b-d) |
| P-C13 | Rate is not minimal | FIXED 453b2ec, ed7f547 (= A14) |
| P-C2, C6, C7, C18, C27, C30, C33, C35 | Classified P (partly); applied in the corrected draft | Responded (applied before this round; no further change requested) |
| P-C16 | Campaign voice in the appendix | FIXED 9c18ae6, 21d373b (= M5) |
| P-C8, C25 | Unmarked edits | FIXED 9c18ae6 (= A2) |
| P-C21, C26 | Classified P; not fully re-derived by the audit | Responded (applied before this round; no text defect beyond the applied correction) |
| P-C23, C24 | N; labelled as clarifications | Responded (labelled as clarifications; no change) |
| P-C29 | N (exists only in the replacement proof) | FIXED 453b2ec, ed7f547 (= A3) |
| P-C32 | Partial (annulus overlap) | Responded (= A1, routed MQ-li-7b-d) |
| P-C34 | Classified P (locator) | FIXED 453b2ec, ed7f547 (= M6) |

## Evidence for the text rows

- paper/idla_mated_crt-corrected.tex: 9c18ae6, then 0204400 (sentence fix). Compiled with `pdflatex` twice in a scratch copy: 94 pages, no undefined references or citations. No build script exists in the repository; the .aux, .log and .pdf files in the repository were not touched.
- paper/appendix-lemma36-C13.tex, paper/appendix-occupation-C16.tex: 21d373b.
- docs/campaign/ERRATA-for-Ewain.md: 453b2ec.
- docs/campaign/ERRATA-INTERNAL.md, docs/campaign/CORRECTIONS.md, docs/campaign/GAPS-SEC2567A.md: ed7f547.
- Material removed from the paper body (the "Uses of Lemma 3.6" text, the Appendix C defects, the coefficient-2 counterexample) is recorded in ERRATA-INTERNAL.md; git history keeps the previous text.

## B3 detail (binder by binder; z12, p2-audit-r2-b3-owner-and-marker)

| Binder | Declaration | Repository proof of the same type | Paper derivation (corrected tex) | Truth status | Outcome |
|---|---|---|---|---|---|
| `hE1` ConeCircleLawUniqueStep | `MatedCRT/FirstPass/Frozen/S2i.lean:16` | none (no theorem with this conclusion) | definition only: tex:427-439 (Definition 2.1); tex:420-421 cites DMS Sec. 3.1; uniqueness in law not argued | TRUE as typed (S2i docstring; FROZEN-PROVENANCE row 21) | cited; Lean discharge open. Missing written steps: uniqueness of the conditioned-BM law `nu` (`Defs/QuantumCone.lean:45`); law uniqueness of the lateral process over `IsWholePlaneGFF` realizations (LP `GaussianLaw.lean:117` is finite-dimensional only); the circle process as a function of (radial, lateral) with the independence field (`Defs/QuantumCone.lean:81-100`). MQ-li-8f (radial-law locator) |
| `hE2` ConeReferenceExistsStep | `MatedCRT/FirstPass/Frozen/S2i.lean:27` | none | definition only: tex:427-439 | TRUE as typed, with caveat (S2i docstring) | cited; Lean discharge open. Existence of `nu` and of a canonical standard Borel model not in repository (LP `ExistGFF.lean:59` covers the lateral GFF only). MQ-li-8f (M15) |
| `hSC` FrozenClusterStrongCompatibility | `MatedCRT/FirstPass/Frozen/S5Cited.lean:74` (provenance row 55 says :114, stale) = HB `ClusterStrongCompatibilityStmt`, HB `Draft/Section5.lean:246` | HB `closure_5_8` (`HarmonicBalls/FirstPass/Closure/SecA45.lean:150`) with PROPOSED binders `hDG`, `hCC`, `hE`; HB `Steps/Sec5/StrongCompatibility.lean:41` (conditional) | no citation of HB Lemma 5.8 by number in the corrected tex; HB Thm 1.1, 5.5, Lemma 3.2 cited at tex:510 | docstring (S5Cited.lean:72): the corrected paper's Lemma 5.8 is stated for Green-regular domains only; the all-U statement follows from the regular-exhaustion argument (HB `Proofs/Sec5/ExhaustionClusterCompatibility.lean`) and its assembly (HB `Proofs/Sec5/StrongCompatibilityAssembly.lean:15`), which is not in the printed source | Derived in HB Lean from `hI2` and the exhaustion step (standard axioms). Not discharged in IDLA: `hSC` stays cited (S5Cited.lean:74). The frozen-weakening option is no longer needed for the Lean statement. Open for the operator: whether the exhaustion step is accepted as the all-U proof of printed Lemma 5.8 (the printed proof uses continuity of G_U up to ∂U; Draft/Section5.lean:235-250 docstring). The IDLA uses (`FirstPass/HBRewire.lean:109` and consumers) are for every bounded open U, so no U-restriction check is needed. No MQ yet |
| `hBG` FrozenBerestyckiGwynneConeBallMass | `MatedCRT/FirstPass/Frozen/S5Cited.lean:28` (= `BerestyckiGwynneConeBallMassStmt`, `MatedCRT/Proposed/BerestyckiGwynne.lean:23`) | none for the statement; `Proofs/Sec3/ConeBallMass.lean:17,54` consume `hBG` | cited: tex:657-668 (Lemma A.1 of BG20, `lemma:volume-growth`); tex:4629 (cited input list, eq. (A.1), p. 66) | pending (S5Cited docstring); drift convention of BG Def 2.2 fixed to +gamma in the Proposed docstring | literature input, cited; no discharge possible. Truth check pending. No MQ yet |
| core conjunct 18 `FPSimilarityTransferCorrected` | `MatedCRT/FirstPass/SLERef/Similarity.lean:39`; conjunct at `SLERef/Certified.lean:49,72`; projection `Certified.lean:151-152` | none; only the SUPERSEDED `SLEReferenceWithSimilarityInput` (`SLERef/Reference.lean:55-59`, projection `:85`) supplies it | none: no written similarity transfer; scale invariance only at tex:547-560 and tex:619-621 | UNSURE per model; universal closure over models FALSE (Similarity docstring) | assumed; not dischargeable as typed. The core bundle `CertifiedReferenceModelCore` (`FirstPass/S5qe.lean:33`) has 17 conjuncts, so "conjunct 18" is the full bundle. MQ-li-6 (non-vacuity of the 18-conjunct bundle) |

No wrapper file `MatedCRT/FirstPass/Closure/B3Discharge.lean` was written: no binder above has a repository proof with its exact type and only literature or frozen binders.
