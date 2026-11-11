# COUNTED.md declaration check

Checks every row of the Table in `docs/campaign/COUNTED.md` (lines 162–227, including the LP forms and the audit rows B6), the Appendix B rows (lines 234–237), and every declaration that COUNTED.md names only in its prose (lines 1–159). The first column is the COUNTED.md line of the row; for prose-only names it is the first line that names them. Checked 2026-11-11 (task p2-counted-ledger-check, worker z8).

## Method

1. Declaration: the file named in the row is searched for the declaration keyword line; the actual line is compared with the stated line. Prose-only names are searched under `MatedCRT/`. The fully qualified name uses the namespace in force at the declaration.
2. Tracking: `git ls-files --error-unmatch`. Hashes: each 7–40-hex token in the row is checked with `git cat-file -t` and must be a commit.
3. Axioms: one `#print axioms` per declaration in a probe outside the repository (`notes/z8-ledger-axioms.lean`, imports 44 modules, not committed), compiled with lc. "std" means exactly `propext, Classical.choice, Quot.sound`.

## Summary

- Rows checked: 99 (Table 60, Appendix B 4, prose-only 35).
- Declarations found: 96; missing: 3. Tracked by git: 96.
- Axioms: 92 std, 0 none, 3 not checkable (declaration missing); non-standard: 0.
- Commit hashes cited: 26; unknown: 1.
- Rows OK: 92 of 99. Mismatches: 7.

## Mismatches for z1 (COUNTED.md line numbers)

- COUNTED.md:189 (row 4.1, `firstPass_4_1_coneLaw_ownBinders`): WRONG-LINE; stated line 64, actual 65
- COUNTED.md:199 (row 5.3, `closed_5_3_clean`): UNKNOWN-HASH; cites 2900417 which is not a commit
- COUNTED.md:223 (row B6, `firstPassMain_1_4_full`): WRONG-LINE; stated line 114, actual 112
- COUNTED.md:224 (row B6, `firstPassMain_1_6_full`): WRONG-LINE; stated line 174, actual 172
- COUNTED.md:26 (row prose, `closed_3_1_countable`): MISSING-DECLARATION; no declaration `closed_3_1_countable` found
- COUNTED.md:26 (row prose, `closed_3_1_faithful`): MISSING-DECLARATION; no declaration `closed_3_1_faithful` found
- COUNTED.md:136 (row prose, `firstPass_6_1`): MISSING-DECLARATION; no declaration `firstPass_6_1` found

## Notes

- COUNTED.md:199 (row 5.3): `2900417` is the suffix of the build log `logs/lb/093821-2900417.log` cited in the same note, not a commit. The same row names the commit `bb7e129`; `bb7e1297` exists. Replace the log id by the commit or drop it.
- COUNTED.md:189 (row 4.1): `firstPass_4_1_coneLaw_ownBinders` is at HLsRewire53.lean:65; line 64 is the last line of its docstring (`-/`).
- COUNTED.md:223, :224 (rows B6): `firstPassMain_1_4_full` is at MatedCRT/FirstPass/Main.lean:112 and `firstPassMain_1_6_full` at :172 (the row states 114 and 174).
- COUNTED.md:26 and :136 name `closed_3_1_countable`, `closed_3_1_faithful` and `firstPass_6_1` in prose. No declaration of these names exists under `MatedCRT/`; the table's row 3.1 declares `firstPass_3_1_faithful`.
- `closed_5_3_clean` was at line 110 in the first pass and at 109 in the second; a hygiene commit changed the file during the check. Re-run the line check after the next landing.

## Full table

| COUNTED.md line | Row | Declaration | file | declared at | stated line | tracked | commit hashes (type) | #print axioms | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 167 | 1.4 | `closed_1_4_full` | MatedCRT/FirstPass/Closure/Final14Full.lean | 21 | 21 | yes | - | std | OK |
| 168 | 1.4n | `closed_1_4_full_noSC` | MatedCRT/FirstPass/Closure/HSCRewire.lean | 30 | 30 | yes | - | std | OK |
| 169 | 1.6 | `closed_1_6_full` | MatedCRT/FirstPass/Closure/Final14Full.lean | 89 | 89 | yes | - | std | OK |
| 170 | 1.6n | `closed_1_6_full_noSC` | MatedCRT/FirstPass/Closure/HSCRewire.lean | 98 | 98 | yes | - | std | OK |
| 171 | 2.3 | `closed_2_3_lit` | MatedCRT/FirstPass/Closure/Final23.lean | 43 | 43 | yes | - | std | OK |
| 172 | 2.3n | `closed_2_3_lit_noSC` | MatedCRT/FirstPass/Closure/HSCRewire.lean | 166 | 166 | yes | - | std | OK |
| 173 | 2.4 | `firstPass_2_4_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 133 | 133 | yes | - | std | OK |
| 174 | 2.5 | `firstPass_2_5_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 153 | 153 | yes | - | std | OK |
| 175 | 2.6 | `firstPass_2_6_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 174 | 174 | yes | - | std | OK |
| 176 | 2.3lp | `closed_2_3_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 37 | 37 | yes | 8a716fde (commit) | std | OK |
| 177 | 2.4lp | `closed_2_4_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 77 | 77 | yes | 8a716fde (commit) | std | OK |
| 178 | 2.5lp | `closed_2_5_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 99 | 99 | yes | 8a716fde (commit) | std | OK |
| 179 | 2.6lp | `closed_2_6_lp` | MatedCRT/FirstPass/Closure/Clean2xLP.lean | 122 | 122 | yes | 8a716fde (commit) | std | OK |
| 180 | 2.13 | `closed_2_13_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean | 21 | 21 | yes | - | std | OK |
| 181 | 2.17 | `firstPass_2_17_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 85 | 85 | yes | - | std | OK |
| 182 | 2.19 | `closed_2_19_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 39 | 39 | yes | - | std | OK |
| 183 | 3.1 | `firstPass_3_1_faithful` | MatedCRT/FirstPass/S3c.lean | 125 | 125 | yes | - | std | OK |
| 184 | 3.3 | `closed_3_3_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 45 | 45 | yes | - | std | OK |
| 185 | 3.4 | `closed_3_4_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 51 | 51 | yes | - | std | OK |
| 186 | 3.5 | `closed_3_5_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 45 | 45 | yes | - | std | OK |
| 187 | 3.6 | `closed_3_6_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 53 | 53 | yes | - | std | OK |
| 188 | 3.7 | `closed_3_7_lp` | MatedCRT/FirstPass/Closure/CleanSec23LP.lean | 61 | 61 | yes | - | std | OK |
| 189 | 4.1 | `firstPass_4_1_coneLaw_ownBinders` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 65 | 64 | yes | e7a5833 (commit) | std | MISMATCH WRONG-LINE |
| 190 | 4.2 | `closed_4_2_clean` | MatedCRT/FirstPass/Closure/Chain42ConeLaw.lean | 116 | 116 | yes | - | std | OK |
| 191 | 4.3 | `closed_4_3` | MatedCRT/FirstPass/Closure/Section4.lean | 18 | 18 | yes | - | std | OK |
| 192 | 4.4 | `closed_4_4` | MatedCRT/FirstPass/Closure/Section4.lean | 22 | 22 | yes | - | std | OK |
| 193 | 4.5 | `closed_4_5` | MatedCRT/FirstPass/Closure/Section4.lean | 27 | 27 | yes | - | std | OK |
| 194 | 4.6 | `firstPass_4_6_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 74 | 74 | yes | e7a5833 (commit) | std | OK |
| 195 | 4.7 | `closed_4_7_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 65 | 65 | yes | - | std | OK |
| 196 | 4.8 | `closed_4_8_corrected_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 71 | 71 | yes | - | std | OK |
| 197 | 5.1 | `closed_5_1_clean` | MatedCRT/FirstPass/Closure/Clean51And54.lean | 40 | 40 | yes | a1339bd (commit) | std | OK |
| 198 | 5.2 | `closed_5_2_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 79 | 79 | yes | - | std | OK |
| 199 | 5.3 | `closed_5_3_clean` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 109 | 109 | yes | 2900417 (UNKNOWN), bb7e129 (commit), ecfbc55 (commit) | std | MISMATCH UNKNOWN-HASH |
| 200 | 5.4 | `closed_5_4_clean` | MatedCRT/FirstPass/Closure/Clean51And54.lean | 73 | 73 | yes | a1339bd (commit) | std | OK |
| 201 | 6.1 | `closed_6_1_clean` | MatedCRT/FirstPass/Closure/Clean61And81.lean | 31 | 31 | yes | 2fb105c (commit) | std | OK |
| 202 | 6.1lp | `closed_6_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean | 43 | 43 | yes | 7b19a40a (commit) | std | OK |
| 203 | 6.4 | `firstPass_6_4_uniform` | MatedCRT/FirstPass/S6p.lean | 213 | 213 | yes | - | std | OK |
| 204 | 6.5 | `firstPass_6_5_uniform` | MatedCRT/FirstPass/S6q.lean | 26 | 26 | yes | - | std | OK |
| 205 | 6.7 | `firstPass_6_7` | MatedCRT/FirstPass/LIClosed68Y.lean | 30 | 30 | yes | - | std | OK |
| 206 | 6.8 | `firstPass_6_8` | MatedCRT/FirstPass/LIClosed68Y.lean | 40 | 40 | yes | - | std | OK |
| 207 | 6.9 | `firstPass_6_9` | MatedCRT/FirstPass/LIClosed68Y.lean | 51 | 51 | yes | - | std | OK |
| 208 | 6.10 | `closed_6_10_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 123 | 123 | yes | - | std | OK |
| 209 | 7.1 | `closed_7_1_clean` | MatedCRT/FirstPass/Closure/Clean71.lean | 42 | 42 | yes | 84ed358 (commit) | std | OK |
| 210 | 7.1lp | `closed_7_1_lp` | MatedCRT/FirstPass/Closure/Clean61And71LP.lean | 84 | 84 | yes | 7b19a40a (commit) | std | OK |
| 211 | 7.2 | `closed_7_2` | MatedCRT/FirstPass/Closure/Section7.lean | 18 | 18 | yes | - | std | OK |
| 212 | 7.3 | `closed_7_3` | MatedCRT/FirstPass/Closure/Section7.lean | 23 | 23 | yes | - | std | OK |
| 213 | 8.1 | `closed_8_1_full` | MatedCRT/FirstPass/Closure/Clean81Full.lean | 19 | 19 | yes | a9bd0055 (commit) | std | OK |
| 214 | 8.1lp | `closed_8_1_lp` | MatedCRT/FirstPass/Closure/Clean81LP.lean | 43 | 43 | yes | a04b0cb4 (commit) | std | OK |
| 215 | 4.2lp | `closed_4_2_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 47 | 47 | yes | e2d3bf22 (commit) | std | OK |
| 216 | 5.1lp | `closed_5_1_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 79 | 79 | yes | e2d3bf22 (commit) | std | OK |
| 217 | 5.3lp | `closed_5_3_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 108 | 108 | yes | e2d3bf22 (commit) | std | OK |
| 218 | 5.4lp | `closed_5_4_lp` | MatedCRT/FirstPass/Closure/Clean42And5LP.lean | 130 | 130 | yes | e2d3bf22 (commit) | std | OK |
| 219 | A.1 | `discreteDivergenceTheorem` | MatedCRT/Proofs/SecA/DiscreteDivergence.lean | 54 | 54 | yes | - | std | OK |
| 220 | A.2 | `discreteBasicPropertiesGeneral` | MatedCRT/Proofs/SecA/Statements.lean | 62 | 62 | yes | - | std | OK |
| 221 | A.3 | `discreteLaplacianBoundGeneral` | MatedCRT/Proofs/SecA/Statements.lean | 66 | 66 | yes | - | std | OK |
| 222 | A.4 | `discreteConservationOfMassGeneral` | MatedCRT/Proofs/SecA/Statements.lean | 71 | 71 | yes | - | std | OK |
| 223 | B6 | `firstPassMain_1_4_full` | MatedCRT/FirstPass/Main.lean | 112 | 114 | yes | - | std | MISMATCH WRONG-LINE |
| 224 | B6 | `firstPassMain_1_6_full` | MatedCRT/FirstPass/Main.lean | 172 | 174 | yes | - | std | MISMATCH WRONG-LINE |
| 225 | m1 | `closed_2_13_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean | 21 | 21 | yes | - | std | OK |
| 226 | m1 | `closed_5_1_cellRewire` | MatedCRT/FirstPass/Closure/CellRewire.lean | 30 | 30 | yes | - | std | OK |
| 234 | AppB | `frozenLBMGreenOccupationRescaled_closed` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure.lean | 35 | 35 | yes | 7a508a1 (commit) | - | OK |
| 235 | AppB | `frozenLBMGreenOccupationRescaled_closed2` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure2.lean | 32 | 32 | yes | 582e360 (commit), 6675b36 (commit) | - | OK |
| 236 | AppB | `frozenLBMGreenOccupationRescaled_closed3` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure3.lean | 68 | 68 | yes | 23f4c7e6 (commit) | - | OK |
| 237 | AppB | `frozenLBMGreenOccupationRescaled_closed4` | MatedCRT/Proofs/Sec3/KilledOccupation/OccupationClosure4.lean | 76 | 76 | yes | d90cbe4e (commit) | - | OK |
| 84 | prose | `MatedCRT.GFFExistence.exists_harmonicBalls_isWholePlaneGFF` | MatedCRT/FirstPass/LPBridge/GFFExistence.lean | 22 | not stated | yes | - | std | OK |
| 36 | prose | `closed_2_13` | MatedCRT/FirstPass/Closure/Section2.lean | 33 | not stated | yes | - | std | OK |
| 112 | prose | `closed_2_2_lit` | MatedCRT/FirstPass/Closure/Final22.lean | 37 | not stated | yes | - | std | OK |
| 107 | prose | `closed_2_2_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 116 | not stated | yes | - | std | OK |
| 25 | prose | `closed_3_1` | MatedCRT/FirstPass/Closure/Section3.lean | 31 | not stated | yes | - | std | OK |
| 26 | prose | `closed_3_1_countable` | NONE | - | not stated | NO | - | MISSING | MISMATCH MISSING-DECLARATION |
| 26 | prose | `closed_3_1_faithful` | NONE | - | not stated | NO | - | MISSING | MISMATCH MISSING-DECLARATION |
| 64 | prose | `closed_3_5` | MatedCRT/FirstPass/Closure/Section3.lean | 66 | not stated | yes | - | std | OK |
| 107 | prose | `closed_3_5_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 57 | not stated | yes | - | std | OK |
| 34 | prose | `closed_5_1` | MatedCRT/FirstPass/Closure/Prop51.lean | 44 | not stated | yes | - | std | OK |
| 107 | prose | `closed_6_10` | MatedCRT/FirstPass/Closure/Section6.lean | 30 | not stated | yes | - | std | OK |
| 131 | prose | `coneGlobalFamilyFactor_ownBinders` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 41 | not stated | yes | - | std | OK |
| 131 | prose | `coneGlobalFamilyFactor_proved` | MatedCRT/FirstPass/S2i/GlobalFactor.lean | 519 | not stated | yes | - | std | OK |
| 129 | prose | `coneScaleInvarianceCoded_ownBinders` | MatedCRT/FirstPass/Closure/HLsRewire53.lean | 52 | not stated | yes | - | std | OK |
| 5 | prose | `firstPassMain_1_4` | MatedCRT/FirstPass/Main.lean | 50 | not stated | yes | - | std | OK |
| 6 | prose | `firstPassMain_1_6` | MatedCRT/FirstPass/Main.lean | 80 | not stated | yes | - | std | OK |
| 140 | prose | `firstPass_2_5_canonical_p2` | MatedCRT/FirstPass/Phase2Rewire.lean | 229 | not stated | yes | - | std | OK |
| 130 | prose | `firstPass_2_6_coded_of_globalFamilyFactor` | MatedCRT/FirstPass/S2g/LawCoded.lean | 33 | not stated | yes | - | std | OK |
| 140 | prose | `firstPass_2_6_corrected_p2` | MatedCRT/FirstPass/Phase2Rewire.lean | 264 | not stated | yes | - | std | OK |
| 28 | prose | `firstPass_3_1_countable` | MatedCRT/FirstPass/S3c/CountableFamilies.lean | 97 | not stated | yes | - | std | OK |
| 107 | prose | `firstPass_3_1_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 92 | not stated | yes | - | std | OK |
| 107 | prose | `firstPass_3_6_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 197 | not stated | yes | - | std | OK |
| 107 | prose | `firstPass_3_7_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 103 | not stated | yes | - | std | OK |
| 58 | prose | `firstPass_4_1` | MatedCRT/FirstPass/S3S4.lean | 115 | not stated | yes | - | std | OK |
| 59 | prose | `firstPass_4_1_coneLaw_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 48 | not stated | yes | - | std | OK |
| 58 | prose | `firstPass_4_1_ownBinders` | MatedCRT/FirstPass/Closure/OwnBinderRewire.lean | 211 | not stated | yes | - | std | OK |
| 58 | prose | `firstPass_4_1_ownBinders_counted` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 62 | not stated | yes | - | std | OK |
| 124 | prose | `firstPass_4_1_ownBinders_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 36 | not stated | yes | - | std | OK |
| 58 | prose | `firstPass_4_2_final` | MatedCRT/FirstPass/S4d.lean | 146 | not stated | yes | - | std | OK |
| 58 | prose | `firstPass_4_2_final_h35c` | MatedCRT/FirstPass/Closure/H35CorrectedRewire.lean | 217 | not stated | yes | - | std | OK |
| 61 | prose | `firstPass_4_6_corrected` | MatedCRT/FirstPass/S3S4.lean | 102 | not stated | yes | - | std | OK |
| 128 | prose | `firstPass_5_4` | MatedCRT/FirstPass/S5S6S7.lean | 42 | not stated | yes | - | std | OK |
| 136 | prose | `firstPass_6_1` | NONE | - | not stated | NO | - | MISSING | MISMATCH MISSING-DECLARATION |
| 137 | prose | `firstPass_7_1` | MatedCRT/FirstPass/S5S6S7.lean | 98 | not stated | yes | - | std | OK |
| 99 | prose | `volumeGrowthStmt_of_berestyckiGwynne` | MatedCRT/Proofs/Sec3/ConeBallMass.lean | 17 | not stated | yes | - | std | OK |
