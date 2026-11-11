# COUNTED.md declaration check

Checks every row of the Table in `docs/campaign/COUNTED.md` (lines 193–260, including the LP forms and the audit rows m1 and B6), the Appendix B rows (lines 261–272), and every declaration that COUNTED.md names only in its prose (lines 1–192).

Checked at HEAD 3cd8222b (2026-11-11 11:26 UTC). The last commit to COUNTED.md is d4b3c0a2 (2026-11-11 11:02:41 UTC, "docs: COUNTED rule-1 outcomes for LP forms; 2.6 and 6.5 confirmed"), which landed before this check, so no commit is pending. Between 689539f8 and 3cd8222b only one docs file changed; the Lean axioms were built at 689539f8 (`lb`, log logs/lb/112409-3272666.log).

## Method

1. Declaration: the file named in the row is searched for the declaration keyword line (theorem, lemma, def, abbrev, structure, class, instance); the actual line is compared with the stated line. Prose-only names are searched under `MatedCRT/` (first match) and carry no stated line. The fully qualified name uses the namespace in force at the declaration.
2. Tracking: `git ls-files --error-unmatch`. Hashes: each 7–40-hex token in the row is checked with `git cat-file -t` and must be a commit.
3. Axioms: one `#print axioms` per distinct declaration in `MatedCRT/Audit/CountedAxioms.lean` (tracked; 52 imports), built with `lb` at 689539f8. "std" means exactly `propext, Classical.choice, Quot.sound`.

Fleet scripts (scratch, not committed): `/home/nitro/paper-fleets/mcrt/scratch-z8/` (`mkraw2.sh`, `check_rows.sh`, `mk.sh`, `post.sh`).

## Summary

- Rows checked: 120 = Table 60 (LP forms, 2.3lp to 8.1lp, and the rows m1 and B6 included), Appendix B 4, prose-only names 56.
- Distinct declarations: 108. Found: 120 of 120 rows. Missing: 0. Tracked by git: 120 of 120.
- Axioms: 108 of 108 distinct declarations report exactly `propext, Classical.choice, Quot.sound`. Non-standard: 0. sorryAx: 0.
- Commit hashes cited: 31; all are commits; unknown: 0.
- Rows OK: 120 of 120. Mismatches: 0.

## Mismatches for z1 (COUNTED.md line numbers)

None at HEAD 3cd8222b. The seven mismatches of the previous check are resolved:

- Row 4.1 is now `closed_4_1_lp` at `MatedCRT/FirstPass/Closure/CleanSec456LP.lean:30` (stated 30).
- Row 5.3 cites `bb7e1297`, a commit; `closed_5_3_clean` is at line 109 (stated 109).
- Rows B6 state 112 and 172, matching `MatedCRT/FirstPass/Main.lean:112` and `:172`.
- The prose names `closed_3_1_countable`, `closed_3_1_faithful` and `firstPass_6_1` are no longer named in COUNTED.md.

## Changes since the previous check (d72a47ac, 0a692f2d)

- Prose-only names went from 35 to 56 (the new "LP forms under the counting rule" and "Own-binder wrappers" sections name more declarations). All 56 exist under `MatedCRT/`.
- `MatedCRT/Audit/CountedAxioms.lean` was regenerated from the 108 distinct declarations: 52 imports (was 44); 15 declarations added (the `_lp` and `_lp_noSC` forms, `firstPass_3_6_closed`, `firstPass_6_1_corrected`, `MatedCRT.S2VG.LitExistence`, `MatedCRT.ratPoint`, `MatedCRT.rationalGridPoint`); 2 removed (`closed_1_4_full_noSC`, `closed_1_6_full_noSC`, no longer named: rows 1.4n and 1.6n now name `closed_1_4_lp_noSC` and `closed_1_6_lp_noSC`).

## Notes

- Prose-only names are declaration-like names in lines 1–192 that the table does not name. The check reports whether each exists and is axiom-clean; it does not decide whether a prose name is a counted declaration. Some are superseded forms, for example `closed_1_4_full` and `closed_1_6_full`, which the table no longer uses; both exist.
- Working tree versus HEAD: the first run (HEAD fd93ddc8, 11:10 UTC) read one uncommitted line in `MatedCRT/FirstPass/S5S6S7.lean`, which holds the counted `firstPass_5_4` (line 42) and `firstPass_7_1` (line 98). Both lines are the same at HEAD. That edit was committed (40b11f32) before the rerun. At the rerun the only uncommitted file was `MatedCRT/Audit/CountedAxioms.lean`.
- Hygiene commits fc07568d, 40b11f32, f94bb006, 8eccd128 and 689539f8 (comment edits) landed between the two runs; the stated lines still match at both (0 wrong-line).

## Full table

| COUNTED.md line | Row | Declaration | file | declared at | stated line | tracked | commit hashes (type) | #print axioms | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 200 | 1.4 | `closed_1_4_lp_noSC` | MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean | 24 | 24 | yes | - | std | OK |
| 201 | 1.4n | `closed_1_4_lp_noSC` | MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean | 24 | 24 | yes | 17ca4173 (commit) | std | OK |
| 202 | 1.6 | `closed_1_6_lp_noSC` | MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean | 73 | 73 | yes | - | std | OK |
| 203 | 1.6n | `closed_1_6_lp_noSC` | MatedCRT/FirstPass/Closure/Clean14And16LPNoSC.lean | 73 | 73 | yes | 17ca4173 (commit) | std | OK |
| 204 | 2.3 | `closed_2_3_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 37 | 37 | yes | - | std | OK |
| 205 | 2.3n | `closed_2_3_lit_noSC` | MatedCRT/FirstPass/Closure/HSCRewire.lean | 166 | 166 | yes | - | std | OK |
| 206 | 2.4 | `closed_2_4_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 77 | 77 | yes | - | std | OK |
| 207 | 2.5 | `closed_2_5_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 99 | 99 | yes | - | std | OK |
| 208 | 2.6 | `closed_2_6_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 122 | 122 | yes | - | std | OK |
| 209 | 2.3lp | `closed_2_3_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 37 | 37 | yes | 8a716fde (commit) | std | OK |
| 210 | 2.4lp | `closed_2_4_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 77 | 77 | yes | 8a716fde (commit) | std | OK |
| 211 | 2.5lp | `closed_2_5_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 99 | 99 | yes | 8a716fde (commit) | std | OK |
| 212 | 2.6lp | `closed_2_6_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 122 | 122 | yes | 8a716fde (commit) | std | OK |
| 213 | 2.13 | `closed_2_13_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean | 21 | 21 | yes | - | std | OK |
| 214 | 2.17 | `firstPass_2_17_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 85 | 85 | yes | - | std | OK |
| 215 | 2.19 | `closed_2_19_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 39 | 39 | yes | - | std | OK |
| 216 | 3.1 | `firstPass_3_1_faithful` | MatedCRT/FirstPass/S3c.lean | 125 | 125 | yes | - | std | OK |
| 217 | 3.3 | `closed_3_3_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 45 | 45 | yes | - | std | OK |
| 218 | 3.4 | `closed_3_4_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 51 | 51 | yes | - | std | OK |
| 219 | 3.5 | `closed_3_5_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 45 | 45 | yes | - | std | OK |
| 220 | 3.6 | `closed_3_6_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 53 | 53 | yes | - | std | OK |
| 221 | 3.7 | `closed_3_7_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 61 | 61 | yes | - | std | OK |
| 222 | 4.1 | `closed_4_1_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean | 30 | 30 | yes | a4ac5fc6 (commit), e7a5833 (commit) | std | OK |
| 223 | 4.2 | `closed_4_2_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 47 | 47 | yes | - | std | OK |
| 224 | 4.3 | `closed_4_3` | MatedCRT/FirstPass/Closure/Section4.lean | 18 | 18 | yes | - | std | OK |
| 225 | 4.4 | `closed_4_4` | MatedCRT/FirstPass/Closure/Section4.lean | 22 | 22 | yes | - | std | OK |
| 226 | 4.5 | `closed_4_5` | MatedCRT/FirstPass/Closure/Section4.lean | 27 | 27 | yes | - | std | OK |
| 227 | 4.6 | `firstPass_4_6_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 74 | 74 | yes | e7a5833 (commit) | std | OK |
| 228 | 4.7 | `closed_4_7_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 65 | 65 | yes | - | std | OK |
| 229 | 4.8 | `closed_4_8_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean | 38 | 38 | yes | a4ac5fc6 (commit) | std | OK |
| 230 | 5.1 | `closed_5_1_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 79 | 79 | yes | a1339bd (commit) | std | OK |
| 231 | 5.2 | `closed_5_2_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 79 | 79 | yes | - | std | OK |
| 232 | 5.3 | `closed_5_3_clean` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 109 | 109 | yes | bb7e1297 (commit), ecfbc55 (commit) | std | OK |
| 233 | 5.4 | `closed_5_4_clean` | MatedCRT/FirstPass/Closure/Clean51And54.lean | 73 | 73 | yes | a1339bd (commit) | std | OK |
| 234 | 6.1 | `closed_6_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean | 43 | 43 | yes | 2fb105c (commit) | std | OK |
| 235 | 6.1lp | `closed_6_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean | 43 | 43 | yes | 7b19a40a (commit) | std | OK |
| 236 | 6.4 | `closed_6_4_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean | 45 | 45 | yes | a4ac5fc6 (commit) | std | OK |
| 237 | 6.5 | `firstPass_6_5_uniform` | MatedCRT/FirstPass/S6q.lean | 26 | 26 | yes | - | std | OK |
| 238 | 6.7 | `firstPass_6_7` | MatedCRT/FirstPass/LIClosed68Y.lean | 30 | 30 | yes | - | std | OK |
| 239 | 6.8 | `firstPass_6_8` | MatedCRT/FirstPass/LIClosed68Y.lean | 40 | 40 | yes | - | std | OK |
| 240 | 6.9 | `firstPass_6_9` | MatedCRT/FirstPass/LIClosed68Y.lean | 51 | 51 | yes | - | std | OK |
| 241 | 6.10 | `closed_6_10_lp` | MatedCRT/FirstPass/Closure/CleanSec456LP.lean | 52 | 52 | yes | a4ac5fc6 (commit) | std | OK |
| 242 | 7.1 | `closed_7_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean | 84 | 84 | yes | 84ed358 (commit) | std | OK |
| 243 | 7.1lp | `closed_7_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean | 84 | 84 | yes | 7b19a40a (commit) | std | OK |
| 244 | 7.2 | `closed_7_2` | MatedCRT/FirstPass/Closure/Section7.lean | 18 | 18 | yes | - | std | OK |
| 245 | 7.3 | `closed_7_3` | MatedCRT/FirstPass/Closure/Section7.lean | 23 | 23 | yes | - | std | OK |
| 246 | 8.1 | `closed_8_1_lp` | MatedCRT/FirstPass/Closure/Clean81LP.lean | 43 | 43 | yes | a9bd0055 (commit) | std | OK |
| 247 | 8.1lp | `closed_8_1_lp` | MatedCRT/FirstPass/Closure/Clean81LP.lean | 43 | 43 | yes | a04b0cb4 (commit) | std | OK |
| 248 | 4.2lp | `closed_4_2_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 47 | 47 | yes | e2d3bf22 (commit) | std | OK |
| 249 | 5.1lp | `closed_5_1_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 79 | 79 | yes | e2d3bf22 (commit) | std | OK |
| 250 | 5.3lp | `closed_5_3_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 108 | 108 | yes | e2d3bf22 (commit) | std | OK |
| 251 | 5.4lp | `closed_5_4_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 130 | 130 | yes | e2d3bf22 (commit) | std | OK |
| 252 | A.1 | `discreteDivergenceTheorem` | MatedCRT/Proofs/SecA/DiscreteDivergence.lean | 54 | 54 | yes | - | std | OK |
| 253 | A.2 | `discreteBasicPropertiesGeneral` | MatedCRT/Proofs/SecA/Statements.lean | 62 | 62 | yes | - | std | OK |
| 254 | A.3 | `discreteLaplacianBoundGeneral` | MatedCRT/Proofs/SecA/Statements.lean | 66 | 66 | yes | - | std | OK |
| 255 | A.4 | `discreteConservationOfMassGeneral` | MatedCRT/Proofs/SecA/Statements.lean | 71 | 71 | yes | - | std | OK |
| 256 | B6 | `firstPassMain_1_4_full` | MatedCRT/FirstPass/Main.lean | 112 | 112 | yes | - | std | OK |
| 257 | B6 | `firstPassMain_1_6_full` | MatedCRT/FirstPass/Main.lean | 172 | 172 | yes | - | std | OK |
| 258 | m1 | `closed_2_13_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean | 21 | 21 | yes | - | std | OK |
| 259 | m1 | `closed_5_1_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean | 30 | 30 | yes | - | std | OK |
| 267 | AppB | `frozenLBMGreenOccupationRescaled_closed` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure.lean | 35 | 35 | yes | 7a508a1 (commit) | std | OK |
| 268 | AppB | `frozenLBMGreenOccupationRescaled_closed2` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure2.lean | 32 | 32 | yes | 582e360 (commit), 6675b36 (commit) | std | OK |
| 269 | AppB | `frozenLBMGreenOccupationRescaled_closed3` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure3.lean | 68 | 68 | yes | 23f4c7e6 (commit) | std | OK |
| 270 | AppB | `frozenLBMGreenOccupationRescaled_closed4` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure4.lean | 76 | 76 | yes | d90cbe4e (commit) | std | OK |
| 117 | prose | `MatedCRT.GFFExistence.exists_harmonicBalls_isWholePlaneGFF` | MatedCRT/FirstPass/LPBridge/GFFExistence.lean | 22 | not stated | yes | - | std | OK |
| 182 | prose | `MatedCRT.S2VG.LitExistence` | MatedCRT/FirstPass/S2VG/Literature.lean | 44 | not stated | yes | - | std | OK |
| 63 | prose | `MatedCRT.ratPoint` | MatedCRT/FirstPass/S2g/LawCode.lean | 24 | not stated | yes | - | std | OK |
| 63 | prose | `MatedCRT.rationalGridPoint` | MatedCRT/Proofs/Sec4/SubsequentialProperties/CircleAverage.lean | 23 | not stated | yes | - | std | OK |
| 32 | prose | `closed_1_4_full` | MatedCRT/FirstPass/Closure/Final14Full.lean | 21 | not stated | yes | - | std | OK |
| 73 | prose | `closed_1_4_lp` | MatedCRT/FirstPass/Closure/Final14LP.lean | 35 | not stated | yes | - | std | OK |
| 32 | prose | `closed_1_6_full` | MatedCRT/FirstPass/Closure/Final14Full.lean | 89 | not stated | yes | - | std | OK |
| 74 | prose | `closed_1_6_lp` | MatedCRT/FirstPass/Closure/Final14LP.lean | 89 | not stated | yes | - | std | OK |
| 37 | prose | `closed_2_13` | MatedCRT/FirstPass/Closure/Section2.lean | 33 | not stated | yes | - | std | OK |
| 79 | prose | `closed_2_13_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 31 | not stated | yes | - | std | OK |
| 145 | prose | `closed_2_2_lit` | MatedCRT/FirstPass/Closure/Final22.lean | 37 | not stated | yes | - | std | OK |
| 140 | prose | `closed_2_2_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 116 | not stated | yes | - | std | OK |
| 75 | prose | `closed_2_3_lit` | MatedCRT/FirstPass/Closure/Final23.lean | 43 | not stated | yes | - | std | OK |
| 25 | prose | `closed_3_1` | MatedCRT/FirstPass/Closure/Section3.lean | 31 | not stated | yes | - | std | OK |
| 80 | prose | `closed_3_1_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 37 | not stated | yes | - | std | OK |
| 65 | prose | `closed_3_5` | MatedCRT/FirstPass/Closure/Section3.lean | 66 | not stated | yes | - | std | OK |
| 81 | prose | `closed_3_5_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 57 | not stated | yes | - | std | OK |
| 85 | prose | `closed_4_2_clean` | MatedCRT/FirstPass/Closure/Chain42ConeLaw.lean | 116 | not stated | yes | - | std | OK |
| 86 | prose | `closed_4_8_corrected_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 71 | not stated | yes | - | std | OK |
| 35 | prose | `closed_5_1` | MatedCRT/FirstPass/Closure/Prop51.lean | 44 | not stated | yes | - | std | OK |
| 87 | prose | `closed_5_1_clean` | MatedCRT/FirstPass/Closure/Clean51And54.lean | 40 | not stated | yes | - | std | OK |
| 153 | prose | `closed_6_10` | MatedCRT/FirstPass/Closure/Section6.lean | 30 | not stated | yes | - | std | OK |
| 93 | prose | `closed_6_10_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 123 | not stated | yes | - | std | OK |
| 90 | prose | `closed_6_1_clean` | MatedCRT/FirstPass/Closure/Clean61And81.lean | 31 | not stated | yes | - | std | OK |
| 94 | prose | `closed_7_1_clean` | MatedCRT/FirstPass/Closure/Clean71.lean | 42 | not stated | yes | - | std | OK |
| 95 | prose | `closed_8_1_full` | MatedCRT/FirstPass/Closure/Clean81Full.lean | 19 | not stated | yes | - | std | OK |
| 164 | prose | `coneGlobalFamilyFactor_ownBinders` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 41 | not stated | yes | - | std | OK |
| 164 | prose | `coneGlobalFamilyFactor_proved` | MatedCRT/FirstPass/S2i/GlobalFactor.lean | 519 | not stated | yes | - | std | OK |
| 162 | prose | `coneScaleInvarianceCoded_ownBinders` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 52 | not stated | yes | - | std | OK |
| 5 | prose | `firstPassMain_1_4` | MatedCRT/FirstPass/Main.lean | 50 | not stated | yes | - | std | OK |
| 6 | prose | `firstPassMain_1_6` | MatedCRT/FirstPass/Main.lean | 80 | not stated | yes | - | std | OK |
| 76 | prose | `firstPass_2_4_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 133 | not stated | yes | - | std | OK |
| 173 | prose | `firstPass_2_5_canonical_p2` | MatedCRT/FirstPass/Phase2Rewire.lean | 229 | not stated | yes | - | std | OK |
| 77 | prose | `firstPass_2_5_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 153 | not stated | yes | - | std | OK |
| 163 | prose | `firstPass_2_6_coded_of_globalFamilyFactor` | MatedCRT/FirstPass/S2g/LawCoded.lean | 33 | not stated | yes | - | std | OK |
| 173 | prose | `firstPass_2_6_corrected_p2` | MatedCRT/FirstPass/Phase2Rewire.lean | 264 | not stated | yes | - | std | OK |
| 78 | prose | `firstPass_2_6_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 174 | not stated | yes | - | std | OK |
| 28 | prose | `firstPass_3_1_countable` | MatedCRT/FirstPass/S3c/CountableFamilies.lean | 97 | not stated | yes | - | std | OK |
| 140 | prose | `firstPass_3_1_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 92 | not stated | yes | - | std | OK |
| 82 | prose | `firstPass_3_6_closed` | MatedCRT/FirstPass/S3i/LensClosed.lean | 31 | not stated | yes | - | std | OK |
| 82 | prose | `firstPass_3_6_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 197 | not stated | yes | - | std | OK |
| 83 | prose | `firstPass_3_7_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 103 | not stated | yes | - | std | OK |
| 172 | prose | `firstPass_4_1` | MatedCRT/FirstPass/S3S4.lean | 115 | not stated | yes | - | std | OK |
| 60 | prose | `firstPass_4_1_coneLaw_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 48 | not stated | yes | - | std | OK |
| 84 | prose | `firstPass_4_1_coneLaw_ownBinders` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 65 | not stated | yes | - | std | OK |
| 140 | prose | `firstPass_4_1_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 211 | not stated | yes | - | std | OK |
| 59 | prose | `firstPass_4_1_ownBinders_counted` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 62 | not stated | yes | - | std | OK |
| 157 | prose | `firstPass_4_1_ownBinders_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 36 | not stated | yes | - | std | OK |
| 170 | prose | `firstPass_4_2_final` | MatedCRT/FirstPass/S4d.lean | 146 | not stated | yes | - | std | OK |
| 59 | prose | `firstPass_4_2_final_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 217 | not stated | yes | - | std | OK |
| 62 | prose | `firstPass_4_6_corrected` | MatedCRT/FirstPass/S3S4.lean | 102 | not stated | yes | - | std | OK |
| 161 | prose | `firstPass_5_4` | MatedCRT/FirstPass/S5S6S7.lean | 42 | not stated | yes | - | std | OK |
| 169 | prose | `firstPass_6_1_corrected` | MatedCRT/FirstPass/S2g/Assembly2456.lean | 31 | not stated | yes | - | std | OK |
| 91 | prose | `firstPass_6_4_uniform` | MatedCRT/FirstPass/S6p.lean | 213 | not stated | yes | - | std | OK |
| 170 | prose | `firstPass_7_1` | MatedCRT/FirstPass/S5S6S7.lean | 98 | not stated | yes | - | std | OK |
| 132 | prose | `volumeGrowthStmt_of_berestyckiGwynne` | MatedCRT/Proofs/Sec3/ConeBallMass.lean | 17 | not stated | yes | - | std | OK |
