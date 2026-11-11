# Audit round 1: responses

Responses to the independent audit of the corrected IDLA paper, round 1. Source: the audit round 1 report (fleet notes, not in the repository) (items A7 to A10, the IDLA email table at its lines 210 to 232, verdict at line 260). Line numbers refer to paper/idla_mated_crt-corrected.tex after the edits of 2026-11-11.

## IDLA (A)

No IDLA (A) finding was judged wrong. Every finding is either applied, or (for the MINIMAL-CORRECTION verdicts below) listed as not applied with its reason.

### Audit items A7 to A10

| Item | Status | Evidence (file:line) |
|---|---|---|
| A7: [C16] and [C13] arguments into the paper | Applied | Appendix B (occupation identity for Lemma 3.4, label app:occupation-proof) and Appendix C (replacement proof of Lemma 3.6, label app:lemma36), after Appendix A. The citations at tex:1308 and tex:1511 are now `Appendix~\ref{...}`. Transcribed from docs/campaign/OCCUPATION-PROOF.md and docs/campaign/LEMMA36-REPLACEMENT.md; campaign wording and the author-attribution lines removed. The Lemma 3.6 'audit of every use' subsection is rewritten with labels, because its line numbers referred to a superseded draft. Email: ERRATA item for Lemmas 3.4 and 3.6 cites Appendices B and C. |
| A8: c_0 overloaded | Applied | Limit constant renamed lambda_0 (was kappa_0 until follow-up item 3) := 2/m_0 (tex:724 and every use, 45 lines; email). Lemma A.3 constants renamed c_{BG,0}, c_{BG,1} (tex:908-910). Bold radius constant unchanged (boldsymbol c_0); the comment at tex:2680 and the email use the bold symbol. |
| A9: Lemma 6.4 and the translation | Applied | Printed proof of Lemma 6.4: K = floor(log_7 delta^{-1/2}) (tex:2809; was epsilon^{-1/2}). Translation sentence with marker [C32] before the application of lemma:annulus-iterate (tex:2808). The phi_z justification is written in the corrected tex at tex:2993-3006 (translation step, h(z+.) = h~ + phi_z), so it is cited, not new. C(gamma) corrected to C(gamma, boldsymbol c_0) (tex:2816, marker [C18]). Email: translation sentence removed from the Lemma 6.8 item; new Lemma 6.4 (proof) item. C29 attribution: the phrase 'after translating by z' is absent from paper/idla_mated_crt.tex (grep, no match); it occurs only in the [C26] replacement proof. The audit's finding is confirmed; the C29 ledger entry and the tex comment at tex:2993 now say so. |
| A10: [C9] locator | Applied | Email, Section 4 item: eq:cluster-and-lambdat (tex:1976) and eq:cluster-contained-in (tex:3898). |

### Table items

| Item | Status | Evidence (file:line) |
|---|---|---|
| TAB typo `\eps<TAB>o0` | Applied | tex:1021, tex:1025 restored to `\eps\to`; marker [C6] (tex:1019). |
| C11 lemma list | Applied | Email header: Lemmas 3.1, 3.3, 3.5, 3.7; Proposition 4.2; Lemmas 4.6 and 4.8. |
| [C13] marker at the unmarked consequence | Applied | tex:2135 (boundary-stability step of Lemma 4.8). Email, Lemma 4.8 item. |
| Stale C = C(gamma) at the Lemma 6.4 proof ([C18]) | Applied | tex:2816. |
| [C26]: bold c_0 shrinks; m_0 redefined locally | Applied | Email, Lemma 6.8 item: eq:c26-choice-c0 (tex:2945; c_0 < 1/48 and C_G^{-1} log(1/(8c_0)) - 1 >= 1/2) in addition to eq:choice-of-constant-annulus; local m_0 := mu_h(D_0) at tex:3147. The phrase 'statement unchanged' is qualified. |
| C26 and C28 'Wrong' texts | Applied | Email, Lemma 6.5 and Lemma 6.8 items: marked as consequences of the integrand correction [C5]. |
| [C5] 'PROVISIONAL' in ledger and marker | Applied | CORRECTIONS.md [C5] heading now CONFIRMED; tex:2673 comment no longer says provisional. The route question (Lemma 2.18 versus r-dependent s_2) is recorded in the [C5] ledger entry as still to be checked against the [C26] replacement. |
| C23, C24 relabelled | Applied | Email: 'Lemma 7.3 (clarification)' and the C23 remark inside the Lemmas 5.3 and 5.4 minor item. |
| C2, C7, C27 to a minor group | Applied | Email, Minor section: Lemma 2.13 (C2), Lemmas 4.4 and 4.5 (C7), good-annulus minimum to infimum (C27, split from the C5 item). |
| Wording at tex:504 and tex:1227 | Applied | Both now state the normalisation Delta G = -delta, with occupation density 2G; consistent with the lambda_0 definition at tex:724. Email, minor item 'Normalisation of the Green's function' (C1). |
| Missing item E-c1-2 (GAPS-SEC2567A.md) | Applied | tex:4305 (hypothesis line), tex:4307-4313 (remark, marker [C33]); email, Minor section 'Appendix A (connectedness)'. |
| INTERNAL section | Moved | docs/campaign/ERRATA-INTERNAL.md (new). Removed from the email. |

### MINIMAL-CORRECTION verdicts in docs/campaign/GAPS-SEC2567A.md

Each verdict has a status line under its heading (2026-11-11).

| Verdict | Status | Evidence / reason |
|---|---|---|
| E-x1-1 (Proposition 5.1 boundary) | Applied [C34] | tex:2455-2456; email minor item. |
| E-A8 (four proof occurrences of the boundary predicate) | Applied [C4] | tex:2397, 2403, 2432, 2472 (now the cell-union boundary). |
| E-c5-2 (arbitrary starting vertices in Definition 6.2) | NOT applied | Conflicts with the author-approved [C31], which takes the starting sites in Theta'. Operator decision needed: the verdict would take the starting sites in V^eps. |
| E-c3-1 (Lemma 7.4 path in Lambda_t^eps) | Already applied [C25] | tex:4028-4031 (statement uses Lambda_t^eps \ {0}). |
| E-c1-2 (Appendix A connectedness) | Applied [C33] | tex:4305-4313; email minor item. |
| E-m1-2 (dependence of s on t) | Applied [C23] | tex:2336 (statement) and tex:2436 (display in the proof of Proposition 5.1, s(rho,gamma,delta,t)). The GAPS displays at old lines 2096 and 2130 correspond to the single display found at tex:2432; mapping judged from content. |
| E-c5-1 (Lemma 6.9 local rate) | Statement order applied [C35]; replacement NOT applied | tex:3588 (s_3 chosen after s_0). The written replacement proof of the local-rate deduction replaces the author-approved [C19] tail argument (tex:3594-3630). Operator decision needed. |
| E-x3-2 (sequence quantifier, Lemmas 4.6 and 4.7) | Already applied [C12] | tex:2006 and nearby (ledger [C12]). |
| E-c3-3 (exit-time argument, T^b = T in distribution) | NOT applied | The written argument makes the strict growth closure(Lambda_s) in Lambda_t (open issue E-c5-3) an explicit prerequisite. Adding an open hypothesis to the paper would change its conclusion, so it needs an operator decision. |
| E-c2-3 (Proposition 6.1, measurable stopped family) | NOT applied | Conditional on the measurable family and on Lean-level inputs (ConeFamilyAEMeasurableStep, Lemma 2.4). The verdict names Lean declarations; no paper-level replacement text is written. |
| E-c2-7 (Proposition 5.1, relaxed Lemma 5.2) | NOT applied | Needs a new statement (relaxed Lemma 5.2 with a null-measurable O_2 and an envelope G) and the discrete-cluster inner estimate, which is conditional on E-c2-5 (open). A new lemma is not transcribed without an operator decision. |
| E-x2-1 (shell iteration, Proposition 7.1) | NOT applied | Conditional verdict. Its replacement is defined by reference to other Lean files and to inputs E-c3-2 and E-A10 (open). |

## IDLA (B)

Source: the audit round 1 report (fleet notes, not in the repository), IDLA (B) items B4 to B7 and the MINOR (B) list. Commit hashes and declaration names checked with git log and grep on the repository.

| Item | Status | Evidence (file:line) |
|---|---|---|
| B4: strongest counted Theorems 1.4/1.6 take paper-owned steps (`closed_1_4_derived_p2`, `closed_1_6_derived_p2`) | Fixed: fcd79e5 (z5) | MatedCRT/FirstPass/Closure/AuditRewire14.lean:53 (`closed_1_4_p3`) and :143 (`closed_1_6_p3`): the counted conclusions without the six paper-step binders, which are derived. |
| B5: the [C16] step is hidden inside a literature bundle | Fixed: 5f3fb57, aebb815 (z9); a118241 (z10) for the residual input | MatedCRT/FirstPass/SLERef/CertifiedCore.lean (`certifiedReferenceModel_of_core`); MatedCRT/FirstPass/Closure/AuditCore.lean (14 `_certCore` declarations). Residual input `BrownianOutwardExcursionAtExitStep`, MatedCRT/Steps/Sec3/ConvergenceHarmonicFunctions.lean:38: discharged in the 14 `_certCore_bm` wrappers (MatedCRT/FirstPass/Closure/Rewire53.lean:58, :73, :87, :100, :114, :129, :211, :293, :374, :456, :536, :616, :687, :756), which apply `frozenBrownianOutwardExcursionAtExit_holds`. The unwrapped originals still take the input (FirstPass/HdetSwap.lean:35, FirstPass/S3t.lean:331, FirstPass/SLERef/CertifiedCore.lean:23, FirstPass/S3S4b/TruncatedLawsBridge.lean:49): operator decision on those. |
| B6: `firstPassMain_1_4` and `firstPassMain_1_6` should not be counted | In progress: owner z1; decision: the counted declarations switch from `firstPassMain_1_4_full`/`_1_6_full` (Main.lean:114, :174) to `closed_1_4_full`/`closed_1_6_full` (Closure/Final14Full.lean:21, :89); ledger docs/campaign/COUNTED.md | MatedCRT/FirstPass/Main.lean:46 (`firstPassMain_1_4`); audit B6 at the audit report line 163. |
| MINOR (B) items | Pending operator (requests 95b to 95e) | Audit round 1 report, MINOR (B) section at line 233. |
| B7: Lemma 3.6 is only half proved | Fixed: 8759946 (z8) | MatedCRT.closed_3_6_full, MatedCRT/FirstPass/Closure/Lemma36Rate.lean:39; binds the cited FrozenOneSidedBoundaryContinuity (Gwynne-Miller-Sheffield, arXiv:1807.07511, Theorem 3.9), defined at MatedCRT/FirstPass/S3i/Frozen.lean:44. |

### Appendix consolidation (follow-up item 1)

One text per appendix in the corrected tex. Coverage of each source section of the two appendix sources (docs/campaign/OCCUPATION-PROOF.md, docs/campaign/LEMMA36-REPLACEMENT.md) by the kept text:

| Source section | Kept text (file:line) |
|---|---|
| OCCUPATION-PROOF.md 1, statement, normalization, inputs (lines 45-151) | paper/idla_mated_crt-corrected.tex:4534 |
| OCCUPATION-PROOF.md 2, nonsingular clock (152-271) | paper/idla_mated_crt-corrected.tex:4641 |
| OCCUPATION-PROOF.md 3, logarithmic insertion (272-456) | paper/idla_mated_crt-corrected.tex:4761 |
| OCCUPATION-PROOF.md 4, occupation and coefficient (457-528) | paper/idla_mated_crt-corrected.tex:4946 |
| OCCUPATION-PROOF.md 5, use in Lemma 3.4 (529-667) | paper/idla_mated_crt-corrected.tex:5018 |
| LEMMA36-REPLACEMENT.md 1, definitions and defects (28-121) | paper/appendix-lemma36-C13.tex:7 |
| LEMMA36-REPLACEMENT.md 2, precisely stated inputs (122-181) | paper/appendix-lemma36-C13.tex:101 |
| LEMMA36-REPLACEMENT.md 3, boundary-excursion estimate (182-414) | paper/appendix-lemma36-C13.tex:159 |
| LEMMA36-REPLACEMENT.md 4, continuity at the limiting paths (415-590) | paper/appendix-lemma36-C13.tex:392 |
| LEMMA36-REPLACEMENT.md 5, outer-stopped interpolation (591-627) | paper/appendix-lemma36-C13.tex:568 |
| LEMMA36-REPLACEMENT.md 6, audit of every use (628-690) | paper/idla_mated_crt-corrected.tex:5158 (condensed: the four items and the closing paragraph; the detailed source wording is NOT transcribed; open) |

Decisions:
- Appendix B stays inline (tex 4531-5155). paper/appendix-occupation-C16.tex is not \input: it still writes the constant as c_0 (appendix-occupation-C16.tex:485), which the [C1] renaming retired, and it is not edited here, since another file owner holds it. It is kept in the repository, unused, because nothing may be deleted here; operator decision.
- Appendix C uses paper/appendix-lemma36-C13.tex (\input at tex:5156), which covers sections 1 to 5 of the source more fully than the former inline text. The audit subsection of the former inline text is kept after it (tex:5158).
- The constant of the occupation identity is renamed lambda_0 (follow-up item 3); see the notation line in the list below.

### Follow-up items (round 2)

- Bibliography: berestycki2017elementary added as \bibitem[Ber17] in paper/idla_mated_crt-corrected.bbl (arXiv:1506.09113). The .bbl is the bibliography actually used (refs.bib is absent); the file is now tracked.
- Notation: the limit constant 2/m_0 is renamed lambda_0 (no occurrence of \lambda in the corrected tex or in the appendix sources before the rename). kappa stays the SLE parameter (tex:191).

## Reported missing items

- Bibliography: Berestycki, 'An elementary approach to Gaussian multiplicative chaos' (arXiv:1506.09113), cited in Appendix B (three places) with key `berestycki2017elementary`. The key is not in the paper's bibliography (paper/idla_mated_crt-corrected.bbl), and refs.bib is not in the repository. The scratch compile reports the citation as undefined. The entry must be added to refs.bib.
- Notation (follow-up item 3): the limit constant 2/m_0 is written lambda_0; kappa_0 was renamed to avoid the clash with the SLE parameter kappa (tex:191).

## IDLA status table

Scope: the IDLA findings of the audit round 1 report (fleet notes, not in the repository): sections A (lines 96-126), B (149-172), the IDLA email table (210-232) and the IDLA Lean minor list (242-249). Audit line numbers are in the "audit" column.
Rule: Fixed = a commit and file:line evidence; Responded = a response line in this file that is not pending; In progress = a named owner and a recorded decision, no commit yet (counted separately); Pending = no commit, no response and no decision, with the owner and request id.
Counts: Fixed 40, Responded 0, Pending 0, In progress 8 (total 48).
In progress rows (owner; decision): B6 firstPassMain_1_4 and _1_6 should not be counted (z1; counted declarations switch to closed_1_4_full/_1_6_full, ledger COUNTED.md); MINOR m1 hcell duplicates adjacentCellsMeetAeStep (z1; check hcell against adjacentCellsMeetAeStep); MINOR m2 FrozenLeastSupersolutionMemCone is a paper-side transfer (z5; operator 95e: HB Lemma 3.1 cited verbatim as a Proposed input, transfer proved in Lean at MatedCRT/FirstPass/S5kLemma31.lean (file added in 0487dc7)); MINOR m3 closed_3_1 is the weak form (z1; COUNTED.md counts closed_3_1_faithful and closed_3_1_countable, not closed_3_1); MINOR m4 Lemma 7.4 has no counted theorem; CrudeUpperBoundStmt vs [C25] (lead; new CrudeUpperBoundCorrectedStmt per [C25], Draft/Section7.lean:67 untouched, proof carved next); MINOR m5 beta minus pinned to (2+gamma)^2/2 + 1 (z5; check whether beta minus is existential in the counted 6.x statements); MINOR m6 FrozenVeryGoodAnnulusHarnackType uses "for every C_3" (lead; truth check queued as MQ-li-1 in the fleet queue notes/fp-gaps/MATH-QUEUE.md; the Prop is HarmonicBalls/Draft/Section6.lean:415 `VeryGoodAnnulusHarnackTypeStmt`, reached via FirstPass/Frozen/S5Cited.lean:44); MINOR m7 non-vacuity rests on IsMatingOfTreesCoupling (operator adds the LP snapshot to audit round 2; section "LP files for audit round 2" below).

| Finding | Audit line | Status | Evidence (commit; file:line or response) |
|---|---|---|---|
| A7 appendices B and C (occupation; Lemma 3.6) | 98 | Fixed | 1d7c3cd, 5c6854f; tex:4531 (Appendix B), tex:5156 (`\input` of Appendix C) |
| A8 overloaded c_0 | 106 | Fixed | 1d7c3cd, 5c6854f; tex:724 (`\lambda_0 := 2/m_0`), tex:908-910 (c_{BG,0}, c_{BG,1}) |
| A9 [C29] misattributed; Lemma 6.4 printed gap | 114 | Fixed | 1d7c3cd; tex:2808 ([C32]), tex:2809 (K with delta^{-1/2}); CORRECTIONS.md:123 |
| A10 [C9] wrong locator | 123 | Fixed | 1d7c3cd; tex:1976 (eq:cluster-and-lambdat), tex:3898 (eq:cluster-contained-in) |
| B4 counted Theorems 1.4/1.6 take paper-owned steps | 151 | Fixed | fcd79e5 (z5); FirstPass/Closure/AuditRewire14.lean:53 (`closed_1_4_p3`), :143 (`closed_1_6_p3`) |
| B5 [C16] step hidden in a literature bundle | 159 | Fixed | 5f3fb57, aebb815; FirstPass/SLERef/CertifiedCore.lean:22, FirstPass/Closure/AuditCore.lean:26 (14 `_certCore` declarations; originals unchanged); a118241 (z10): the residual input Steps/Sec3/ConvergenceHarmonicFunctions.lean:38 is discharged in the 14 `_certCore_bm` wrappers, FirstPass/Closure/Rewire53.lean:58-756; the unwrapped originals still take it (operator decision) |
| B6 firstPassMain_1_4 and _1_6 should not be counted | 163 | In progress | owner z1; decision: counted declarations switch from `firstPassMain_1_4_full`/`_1_6_full` to `closed_1_4_full`/`closed_1_6_full`; ledger docs/campaign/COUNTED.md; FirstPass/Main.lean:46 |
| B7 Lemma 3.6 only half proved | 167 | Fixed | 8759946; FirstPass/Closure/Lemma36Rate.lean:39 (`closed_3_6_full`) |
| C1 (email table) | 214 | Fixed | 12219de; tex:504 (marker); CORRECTIONS.md:7 |
| C2 (email table) | 215 | Fixed | 12219de; tex:829 (marker); CORRECTIONS.md:31; moved to Minor in 1d7c3cd, ERRATA-for-Ewain.md:61 |
| C3 (email table) | 215 | Fixed | 12219de; tex:990 (marker); CORRECTIONS.md:37 |
| C4 (email table) | 215 | Fixed | 12219de; tex:2338 (marker); CORRECTIONS.md:42 |
| C5 (email table) | 223 | Fixed | 12219de; tex:2673 (marker); CORRECTIONS.md:49; ledger CONFIRMED in 1d7c3cd |
| C6 (email table) | 216 | Fixed | 15e23b5; tex:1019 (marker); CORRECTIONS.md:56; TAB typo fixed in 1d7c3cd (tex:1021, 1025) |
| C7 (email table) | 215 | Fixed | ca0f323; tex:1983 (marker); CORRECTIONS.md:61; moved to Minor in 1d7c3cd, ERRATA-for-Ewain.md:61 |
| C8 (email table) | 215 | Fixed | ca0f323; tex:3941 (marker); CORRECTIONS.md:64 |
| C9 (email table) | 220 | Fixed | ca0f323; tex:1812 (marker); CORRECTIONS.md:67; locator fixed in 1d7c3cd (tex:1976, 3898) |
| C10 (email table) | 215 | Fixed | ca0f323; tex:980 (marker); CORRECTIONS.md:70 |
| C11 (email table) | 217 | Fixed | 0ba290f; tex:979 (marker); CORRECTIONS.md:73; email list fixed in 1d7c3cd |
| C12 (email table) | 215 | Fixed | 0ba290f; tex:2006 (marker); CORRECTIONS.md:76 |
| C13 (email table) | 218 | Fixed | 1c181f9; tex:1396 (marker); CORRECTIONS.md:79; unmarked consequence marked at tex:2135 in 1d7c3cd; audit note on strengthening not acted on |
| C14 (email table) | 215 | Fixed | 1c181f9; tex:2110 (marker); CORRECTIONS.md:83 |
| C15 (email table) | 215 | Fixed | db7762c; tex:719 (marker); CORRECTIONS.md:21 |
| C16 (email table) | 219 | Fixed | db7762c; tex:1246 (marker); CORRECTIONS.md:24; deferred file replaced by Appendices (1d7c3cd; tex:4531, 5156) |
| C17 (email table) | 214 | Fixed | db7762c; tex:1366 (marker); CORRECTIONS.md:28 |
| C18 (email table) | 221 | Fixed | 11ec135; tex:2679 (marker); CORRECTIONS.md:86; stale C at tex:2816 fixed in 1d7c3cd |
| C19 (email table) | 215 | Fixed | dd17ff9; tex:3619 (marker); CORRECTIONS.md:90 |
| C20 (email table) | 222 | Fixed | 968ce64; tex:1915 (marker); CORRECTIONS.md:93 |
| C21 (email table) | 222 | Fixed | 968ce64; tex:2330 (marker); CORRECTIONS.md:96 |
| C23 (email table) | 224 | Fixed | 3515643; tex:2335 (marker); CORRECTIONS.md:104; relabelled as clarification in 1d7c3cd |
| C24 (email table) | 224 | Fixed | 3515643; tex:3987 (marker); CORRECTIONS.md:108; relabelled as clarification in 1d7c3cd |
| C25 (email table) | 215 | Fixed | 3515643; tex:4028 (marker); CORRECTIONS.md:111 |
| C26 (email table) | 222 | Fixed | 89ba440; tex:2914 (marker); CORRECTIONS.md:114; email entry rewritten in 1d7c3cd |
| C27 (email table) | 215 | Fixed | 79b1b1c; tex:2675 (marker); CORRECTIONS.md:117; split and moved to Minor in 1d7c3cd |
| C28 (email table) | 222 | Fixed | 79b1b1c; tex:2698 (marker); CORRECTIONS.md:120; 'Wrong' texts marked in 1d7c3cd |
| C29 (email table) | 225 | Fixed | 79b1b1c; tex:3003 (marker); CORRECTIONS.md:123; ledger corrected in 1d7c3cd |
| C30 (email table) | 215 | Fixed | 79b1b1c; tex:2862 (marker); CORRECTIONS.md:126 |
| C31 (email table) | 215 | Fixed | 79b1b1c; tex:2628 (marker); CORRECTIONS.md:129 |
| E-c1-2 missing item (connectedness of V, Appendix A) | 227 | Fixed | 1d7c3cd; tex:4305-4313 (C33 marker at tex:4307); ERRATA-for-Ewain.md:61 (Minor) |
| Wording: 'Green's function for standard Brownian motion' | 228 | Fixed | 1d7c3cd; tex:504 and tex:1227 (C1 markers) |
| INTERNAL section of the email | 229 | Fixed | 1d7c3cd (moved out of the email); docs/campaign/ERRATA-INTERNAL.md:1 |
| MINOR m1 hcell duplicates adjacentCellsMeetAeStep | 243 | In progress | owner z1; decision: check hcell against adjacentCellsMeetAeStep |
| MINOR m2 FrozenLeastSupersolutionMemCone is a paper-side transfer | 244 | In progress | owner z5; decision (operator 95e): HB Lemma 3.1 cited verbatim as a Proposed input; transfer to FrozenLeastSupersolutionMemCone proved in Lean at MatedCRT/FirstPass/S5kLemma31.lean (file added in 0487dc7); used at FirstPass/S5k.lean:54 |
| MINOR m3 closed_3_1 is the weak form | 245 | In progress | owner z1; decision: COUNTED.md counts closed_3_1_faithful and closed_3_1_countable, not closed_3_1 |
| MINOR m4 Lemma 7.4 has no counted theorem; CrudeUpperBoundStmt vs [C25] | 246 | In progress | owner lead; decision: new CrudeUpperBoundCorrectedStmt per [C25]; Draft/Section7.lean:67 untouched; proof carved next |
| MINOR m5 beta minus pinned to (2+gamma)^2/2 + 1 | 247 | In progress | owner z5; decision: check whether beta minus is existential in the counted 6.x statements; FirstPass/S6d.lean (audit location :30) |
| MINOR m6 FrozenVeryGoodAnnulusHarnackType uses "for every C_3" | 248 | In progress | owner lead; decision: truth check queued as MQ-li-1 (notes/fp-gaps/MATH-QUEUE.md, fleet queue); the Prop is HarmonicBalls/Draft/Section6.lean:415 `VeryGoodAnnulusHarnackTypeStmt`, reached via FirstPass/Frozen/S5Cited.lean:44 |
| MINOR m7 non-vacuity rests on IsMatingOfTreesCoupling (absent from snapshot) | 249 | In progress | owner operator (adds the LP snapshot to audit round 2); decision: LP declarations and IDLA consumers in section "LP files for audit round 2" |

## LP files for audit round 2

Snapshot trees. Both trees hold the same file paths and line numbers for the rows below.
- Pinned: `.lake/packages/lattice-probability` (LatticeProb at rev 3912597, "Port Birkhoff ergodic theorem to Lean 4.35").
- Branch `idla/phase2`: `/home/nitro/lean/LP-idla-phase2` (HEAD 61f74b6).

| LP declaration | LP file (both trees) | Use in IDLA |
|---|---|---|
| `MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling` (structure, 24 fields) | LatticeProb/Bonanno/MatedCRTHarmonic/Frozen/IsMatingOfTreesCoupling.lean:61 | coupling clause of `MatedCRTEnv.IsValid` (MatedCRT/Defs/Setting.lean:157-165) |
| field `igMap` (existential witness `Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ)`, measurable) | IsMatingOfTreesCoupling.lean:84 (informal description :35) | imaginary-geometry map of `spaceFilling` (MatedCRT/Defs/Setting.lean:34, :43) |
| `coneField` | LatticeProb/Bonanno/MatedCRTHarmonic/Frozen/MatedCRTConeField.lean:28 | used in IsMatingOfTreesCoupling.lean:114, :120, :144 |
| `coneRadial` | LatticeProb/Bonanno/MatedCRTHarmonic/Frozen/MatedCRTConeRadial.lean:28 | used in IsMatingOfTreesCoupling.lean:114, :120, :144 |

IDLA consumers (grep over MatedCRT; several hits are docstring mentions):
- `MatedCRTEnv.IsValid` (MatedCRT/Defs/Setting.lean:141), the structure that carries the coupling clause at :157-165.
- `HasReferenceEnvironments` (MatedCRT/FirstPass/SLERef/Reference.lean:42-44): `∃ S : MatedCRTEnv ℝ, S.IsValid 𝒮 γ` for every γ in (0, 2). It is the non-vacuity statement. It is a conjunct of `CertifiedReferenceModel` (MatedCRT/FirstPass/SLERef/Certified.lean:64; projection :119). Whether `CertifiedReferenceModel` is discharged or assumed is NOT checked in this section.
- `MatedCRTEnv.IsValid.ae_no_earlier_origin_visit` (MatedCRT/Proofs/Sec4/DivSandpileLowerBound/SourceVertex.lean:103).
- `RescaledEnvironmentInput` (MatedCRT/Proofs/Sec1/EnvironmentScaling.lean:103) and `RescaledMatingOfTreesStep` (:149).
- Mentions of `IsMatingOfTreesCoupling` or `igMap`: MatedCRT/FirstPass/S5m.lean:12-13; MatedCRT/Proofs/Infra/MatingOfTrees.lean:7-8; MatedCRT/Proofs/MatingOfTrees/AdjacentContactWitnesses.lean:4, :24; MatedCRT/Proofs/Sec1/EnvironmentScaling/IGCurveScaling.lean:1, :7; MatedCRT/Proposed/StoppedPoleCanonicalMoments2026.lean:227 (`GMSCoordinateChangeStmt`).
