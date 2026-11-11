# Archive recheck: unreachable MatedCRT modules

Campaign-internal. Report only: this file moves nothing. Rule: `docs/campaign/ARCHIVE.md` lines 1-12 (operator decision 89b). Computed at HEAD `689539f8` (2026-11-11) from tracked files; import lines are parsed from the HEAD contents.

## Roots (as stated by the task)

| Root class | Lean files |
|---|---:|
| every `MatedCRT/FirstPass/Closure/*.lean` | 47 |
| every tracked file containing `closed_`: 70 `.lean` files, plus 11 non-Lean files (`README.md`, `docs/campaign/ARCHIVE.md`, `AUDIT-R1-RESPONSES.md`, `AUDIT-R2-RESPONSES.md`, `CORRECTED-FORMS.md`, `COUNTED-CHECK.md`, `COUNTED.md`, `DUPLICATES.md`, `FROZEN-PROVENANCE.md`, `LP-STAGING-SYNC.md`, `PHASE2-INVENTORY.md`) | 70 |
| `MatedCRT/Audit/CountedAxioms.lean`, `MatedCRT/Assembly/Main.lean` | 2 |
| files named in the `README.md` table | 36 |
| kept by rule: `MatedCRT/Draft` 14, `External` 2, `Defs` 9, `Steps` 63, `Proposed` 12, `LPStaging` 37, `FirstPass/Frozen` 25 | 162 |
| **union of the roots (unique `.lean` files)** | **242** |

`MatedCRT.lean` (repository root) is **not** a root. It is reached from the closure through `import MatedCRT` at `MatedCRT/Assembly/Hypotheses.lean:1` (a closure file), so it is a closure member. It imports 26 modules: `MatedCRT.Basic`, `Defs.{Notation,Map,RandomWalk,QuantumCone,Setting,Sandpile}`, `Draft.{Section1..8,SectionA}`, `External.{SLE,QuantumCone}`, `Proofs.Infra.{DiscretePotential,RandomWalk}`, `Steps.SecA.DiscreteObstacle`, `Proofs.SecA.{DiscreteObstacle,DiscreteDivergence,Statements}`, `Proofs.Sec4.Prop42Closure.{HalfBallClosure,Assembly}`. None of these 26 is a candidate, so no candidate move requires an edit to `MatedCRT.lean`.

## Method

1. Every tracked `.lean` file is read at HEAD; `import` lines (including `public`/`private import`) are parsed after stripping block comments. A module `MatedCRT.X.Y` maps to `MatedCRT/X/Y.lean`; `MatedCRT` maps to `MatedCRT.lean`.
2. Closure = forward reachability from the roots over those edges. Candidate = tracked `MatedCRT/**/*.lean` outside the closure.
3. Per candidate: number of tracked importers (all tracked `.lean` files, including `archive/`); how many of them lie in the closure (must be 0); named in a file of `/home/nitro/paper-fleets/mcrt/tasks/*.md` (path, short path, or module name, word-boundary matched); last commit (`git log -1 --format=%cI`); uncommitted edits (`git diff --name-only HEAD`).
4. Status under the rule as written: a candidate moves only if it is not named in tasks/, has no uncommitted edit, and was not committed after 2026-11-11 00:05:14 UTC (ARCHIVE.md line 4). A candidate that is imported by a file that stays is also kept (a stayer pins its imports, because `lakefile.lean:15-16` builds `andSubmodules MatedCRT`, so a dangling import breaks `lb`).
5. Batches: layer = longest chain of movable importers; sort by (layer, directory, path); chunks of 40. Every importer therefore sits in an earlier or the same batch, listed earlier (git mv in listed order). Checked: 0 order violations.

## Counts

- Tracked MatedCRT `.lean` files: 2090. Import closure: 1819 `.lean` files (1818 under `MatedCRT/` plus `MatedCRT.lean`).
- Candidates: 272 (= 2090 − 1818). Tracked importers inside the closure: 0 for every candidate.
- Dangling `MatedCRT` imports from `MatedCRT/` files: 0. Dangling imports from `archive/` files: 87 (already moved earlier; `archive/` is not built).

| Status under the rule as written | Candidates |
|---|---:|
| named in a file of tasks/ (not a candidate by the task rule) | 16 |
| last commit after 2026-11-11 00:05:14 UTC (not named) | 155 |
| uncommitted edits | 0 |
| kept because a file that stays imports it | 97 |
| **movable under the rule as written** | **4** |

Plan B (for the operator decision only): waive the 00:05:14 UTC condition, keep the named and uncommitted exclusions. Movable: 167; batches: 5 (sizes 40, 40, 40, 40, 7). This is not the ARCHIVE.md rule; it is shown because the date condition is what limits the rule-compliant plan.

## Batch plan under the rule as written (Plan A)

| Batch | Files (order = git mv order) |
|---|---|
| B01 | `MatedCRT/FirstPass/LPBridge/LQGExistence.lean`<br>`MatedCRT/FirstPass/S2x/ConeScaleRadiusPos.lean`<br>`MatedCRT/FirstPass/S3S4b/TruncatedLawsBridge.lean`<br>`MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroWeakLimit.lean` |

Archive importers of Plan A files (not built; each import dangles after the move; lead decision): `archive/MatedCRT/FirstPass/S2x/ConeScaleRadiusPosLimit.lean` imports `MatedCRT/FirstPass/S2x/ConeScaleRadiusPos.lean`.

## Batch plan if the date condition is waived (Plan B)

| Batch | Files | Directories (count) |
|---|---:|---|
| B01 | 40 | `MatedCRT/FirstPass/S4S6c` 15, `MatedCRT/FirstPass` 13, `MatedCRT/FirstPass/S2g` 7, `MatedCRT/FirstPass/LPBridge` 2, `MatedCRT/FirstPass/S2x` 1, `MatedCRT/FirstPass/S3S4b` 1, `MatedCRT/FirstPass/S3t` 1 |
| B02 | 40 | `MatedCRT/FirstPass/S4S6c` 10, `MatedCRT/Proofs/Sec1/EnvironmentScaling` 10, `MatedCRT/FirstPass/S5c` 9, `MatedCRT/FirstPass/S5d` 3, `MatedCRT/FirstPass/S4d` 1, `MatedCRT/FirstPass/S6j` 1, `MatedCRT/FirstPass/S6m` 1, `MatedCRT/FirstPass/S6r` 1, `MatedCRT/FirstPass/SLERef` 1, `MatedCRT/Proofs/MatingOfTrees` 1, `MatedCRT/Proofs/Sec4/Prop42Closure` 1, `MatedCRT/Proofs/Sec5` 1 |
| B03 | 40 | `MatedCRT/FirstPass/S4S6c` 13, `MatedCRT/Proofs/Sec5` 7, `MatedCRT/FirstPass/S5c` 4, `MatedCRT/FirstPass/S2h` 3, `MatedCRT/Proofs/Sec1/EnvironmentScaling` 3, `MatedCRT/FirstPass` 2, `MatedCRT/FirstPass/S6e` 2, `MatedCRT/Audit` 1, `MatedCRT/FirstPass/S2g` 1, `MatedCRT/FirstPass/S6j` 1, `MatedCRT/FirstPass/S7y` 1, `MatedCRT/Proofs/MatingOfTrees` 1, `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions` 1 |
| B04 | 40 | `MatedCRT/Proofs/Sec4/Prop42Closure` 8, `MatedCRT/Proofs/Sec5` 7, `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions` 6, `MatedCRT/FirstPass/S5c` 4, `MatedCRT/FirstPass/S7y` 4, `MatedCRT/FirstPass/S2h` 4, `MatedCRT/FirstPass/S4S6c` 3, `MatedCRT/Proofs/MatingOfTrees` 2, `MatedCRT/Proofs/Sec1/EnvironmentScaling` 2 |
| B05 | 7 | `MatedCRT/FirstPass/S2h` 7 |

The plan B column of the candidate table gives each file batch. Inside a batch, files are ordered by layer, directory, path; importers always come first.

## Candidates (272)

Columns: importers = all tracked importers; in closure = importers inside the closure (0 everywhere); outside = importers that are not candidates (all in `archive/`); named = named in tasks/; last commit (UTC); dirty = uncommitted edits; rule = status under ARCHIVE.md; plan B = batch if the date condition is waived.

| path | importers | in closure | outside | named | last commit | dirty | rule | plan B |
|---|---:|---:|---:|---|---|---|---|---|
| `MatedCRT/Audit/LocalDirichletProjectionComponents.lean` | 1 | 0 | 0 | no | 2026-11-11T10:30:35+00:00 | no | HOLD date | B03 |
| `MatedCRT/Audit/Main.lean` | 0 | 0 | 0 | yes | 2026-11-08T08:28:59+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Audit/PlateauScalingResiduals.lean` | 0 | 0 | 0 | yes | 2026-11-11T10:24:18+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Audit/Reductions.lean` | 0 | 0 | 0 | yes | 2026-11-11T10:30:35+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Audit/Sec3PointwiseRates.lean` | 0 | 0 | 0 | yes | 2026-11-08T08:26:21+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/FirstPass/LICGRCXLe68.lean` | 2 | 0 | 0 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/LPBridge/GFFInterface.lean` | 0 | 0 | 0 | no | 2026-11-11T06:03:06+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/LPBridge/LQGExistence.lean` | 0 | 0 | 0 | no | 2026-11-10T23:27:50+00:00 | no | MOVE B01 | B01 |
| `MatedCRT/FirstPass/S1c/Composition.lean` | 1 | 0 | 1 | yes | 2026-11-10T03:30:34+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/FirstPass/S2g/Assembly24.lean` | 1 | 0 | 1 | no | 2026-11-11T02:34:08+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2g/FamilyLocal.lean` | 0 | 0 | 0 | no | 2026-11-11T02:34:08+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2g/HVGood.lean` | 1 | 0 | 1 | no | 2026-11-11T02:34:08+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2g/LawCoded25.lean` | 1 | 0 | 1 | no | 2026-11-11T02:34:08+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2g/Locality.lean` | 0 | 0 | 0 | no | 2026-11-11T02:34:08+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2g/PlateauZero.lean` | 4 | 0 | 3 | no | 2026-11-11T02:34:08+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S2g/Section6CanonicalAxioms.lean` | 0 | 0 | 0 | no | 2026-11-11T02:34:08+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2g/Transfer.lean` | 1 | 0 | 1 | no | 2026-11-11T02:34:08+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2h.lean` | 1 | 0 | 1 | no | 2026-11-11T11:08:45+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2h/CertBack.lean` | 1 | 0 | 0 | no | 2026-11-11T10:29:12+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S2h/CertCharged.lean` | 1 | 0 | 0 | no | 2026-11-11T10:29:12+00:00 | no | HOLD date | B05 |
| `MatedCRT/FirstPass/S2h/CertCode.lean` | 4 | 0 | 2 | no | 2026-11-11T10:29:12+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S2h/CertDense.lean` | 1 | 0 | 0 | no | 2026-11-11T10:29:12+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S2h/CertForward.lean` | 1 | 0 | 0 | no | 2026-11-11T10:29:12+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S2h/CertForward2.lean` | 1 | 0 | 0 | no | 2026-11-11T10:29:12+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S2h/CertMoment.lean` | 2 | 0 | 0 | no | 2026-11-11T10:29:12+00:00 | no | HOLD date | B05 |
| `MatedCRT/FirstPass/S2h/CertRel.lean` | 2 | 0 | 0 | no | 2026-11-11T10:29:12+00:00 | no | HOLD date | B05 |
| `MatedCRT/FirstPass/S2h/CertSets.lean` | 1 | 0 | 0 | no | 2026-11-11T10:30:43+00:00 | no | HOLD date | B05 |
| `MatedCRT/FirstPass/S2h/CertSuperBack.lean` | 1 | 0 | 0 | no | 2026-11-11T10:30:43+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S2h/Cutoff.lean` | 1 | 0 | 0 | no | 2026-11-11T10:30:43+00:00 | no | HOLD date | B05 |
| `MatedCRT/FirstPass/S2h/CutoffUnion.lean` | 1 | 0 | 0 | no | 2026-11-11T10:30:43+00:00 | no | HOLD date | B05 |
| `MatedCRT/FirstPass/S2h/LeastSuper.lean` | 1 | 0 | 0 | no | 2026-11-11T10:30:43+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S2h/MeasurableIntegral.lean` | 3 | 0 | 1 | no | 2026-11-11T10:30:43+00:00 | no | HOLD date | B05 |
| `MatedCRT/FirstPass/S2i.lean` | 0 | 0 | 0 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2l.lean` | 1 | 0 | 1 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2x/BrownianNegativeDrift.lean` | 1 | 0 | 1 | yes | 2026-11-11T10:30:43+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/FirstPass/S2x/ConeScaleRadiusPos.lean` | 1 | 0 | 1 | no | 2026-11-10T08:53:03+00:00 | no | MOVE B01 | B01 |
| `MatedCRT/FirstPass/S2y.lean` | 0 | 0 | 0 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S2z.lean` | 1 | 0 | 0 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S34d.lean` | 0 | 0 | 0 | no | 2026-11-11T10:31:53+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S3S4b/TruncatedLawsBridge.lean` | 0 | 0 | 0 | no | 2026-11-10T08:13:58+00:00 | no | MOVE B01 | B01 |
| `MatedCRT/FirstPass/S3h.lean` | 0 | 0 | 0 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S3t/PathMeasurability.lean` | 0 | 0 | 0 | no | 2026-11-11T10:31:53+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/AbsorbedChernoff69.lean` | 1 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/AbsorbedChernoffTail.lean` | 0 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/Amplification68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/AmplifiedBound.lean` | 1 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/B1GoodEnvSplitG68.lean` | 0 | 0 | 0 | yes | 2026-11-11T10:32:57+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/FirstPass/S4S6c/CGRCXLeCore68.lean` | 1 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/CGRCYInst68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/CGRCYK2Inst68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/CGResVol68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:30:59+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/CellSize68.lean` | 1 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/Closed6x68Le.lean` | 0 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/CountingExitAlphaCore68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:30:59+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/CoverMinorant.lean` | 1 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/CoverMinorantAE.lean` | 0 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/CoverMinorantMeasurable.lean` | 1 | 0 | 0 | no | 2026-11-11T11:08:45+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/Exponents.lean` | 0 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/GoodRadii.lean` | 0 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/HoneCover68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:20:37+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/LayerCrossing68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:31+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/LocalWindow68.lean` | 0 | 0 | 0 | no | 2026-11-11T10:32:57+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/MeshExitPw68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:31+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/NextExitTime.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:31+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S4S6c/Redesign68S9.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:31+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4S6c/ShellBallLoc68.lean` | 1 | 0 | 0 | no | 2026-11-11T04:30:59+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/ShellChainCGRCXLe68.lean` | 1 | 0 | 0 | no | 2026-11-11T04:23:31+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/ShellOrderLoc68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4S6c/ShellSmallR68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4S6c/Uniform68Band.lean` | 1 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/Uniform68Events.lean` | 2 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S4S6c/Uniform68Inputs.lean` | 2 | 0 | 0 | no | 2026-11-11T04:24:41+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S4S6c/Uniform68Local.lean` | 4 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S4S6c/Uniform68LogRadius.lean` | 1 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/Uniform68LogRadius2.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4S6c/Uniform68Monotone.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4S6c/Uniform68Params.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4S6c/Uniform68Point.lean` | 1 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/Uniform68PointEvents.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4S6c/Uniform68Radius.lean` | 1 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/UniformLayer68.lean` | 1 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S4S6c/VolumeCountable68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4S6c/WalkExitW.lean` | 0 | 0 | 0 | no | 2026-11-11T04:23:34+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4S6c/WindowUniform68.lean` | 0 | 0 | 0 | no | 2026-11-11T04:30:59+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4d/Final42e.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S4e.lean` | 0 | 0 | 0 | yes | 2026-11-11T10:32:57+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/FirstPass/S4e/RescaledDecode.lean` | 1 | 0 | 0 | no | 2026-11-11T10:32:57+00:00 | no | HOLD date | STAY (importer stays) |
| `MatedCRT/FirstPass/S5c/B2Bad.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5c/DensityFloor.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5c/EntranceAtoms.lean` | 1 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S5c/EntranceLevel.lean` | 1 | 0 | 0 | no | 2026-11-11T11:12:26+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S5c/FloorEventually.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5c/FloorMono.lean` | 1 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S5c/HmemCell.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5c/MassEvent.lean` | 0 | 0 | 0 | no | 2026-11-11T10:32:57+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5c/NewMass.lean` | 1 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S5c/NullContainment.lean` | 1 | 0 | 1 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5c/ProbLimit.lean` | 1 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S5c/ProbLocalize.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5c/ScaleNull.lean` | 1 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S5c/Scaling.lean` | 2 | 0 | 1 | no | 2026-11-09T18:03:12+00:00 | no | STAY (importer stays) | B04 |
| `MatedCRT/FirstPass/S5c/StoppedInterior.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5c/SubseqCriterion.lean` | 2 | 0 | 1 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S5c/TendsOneOnOfSubseq.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:51+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5d/ClusterFromPoint.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:52+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5d/KillingComponent.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:52+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5d/StoppedSecondGreen.lean` | 0 | 0 | 0 | no | 2026-11-11T02:29:52+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S5e.lean` | 0 | 0 | 0 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S5n.lean` | 0 | 0 | 0 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S5p.lean` | 0 | 0 | 0 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S6b.lean` | 1 | 0 | 1 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S6e.lean` | 0 | 0 | 0 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S6e/DdSources.lean` | 1 | 0 | 0 | no | 2026-11-11T02:35:57+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S6e/UniversalEvent.lean` | 1 | 0 | 0 | no | 2026-11-11T02:35:57+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S6g.lean` | 0 | 0 | 0 | no | 2026-11-11T02:33:56+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S6j/Radius.lean` | 0 | 0 | 0 | no | 2026-11-11T02:35:57+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S6j/StateGood.lean` | 2 | 0 | 1 | no | 2026-11-11T02:35:57+00:00 | no | HOLD date | B03 |
| `MatedCRT/FirstPass/S6m/State.lean` | 1 | 0 | 1 | no | 2026-11-11T02:35:57+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S6r/GoodAnnulusMeas.lean` | 0 | 0 | 0 | no | 2026-11-11T02:41:50+00:00 | no | HOLD date | B02 |
| `MatedCRT/FirstPass/S7y.lean` | 0 | 0 | 0 | no | 2026-11-11T10:32:42+00:00 | no | HOLD date | B01 |
| `MatedCRT/FirstPass/S7y/Core.lean` | 1 | 0 | 0 | no | 2026-11-10T09:53:43+00:00 | no | STAY (importer stays) | B04 |
| `MatedCRT/FirstPass/S7y/Final.lean` | 1 | 0 | 0 | no | 2026-11-10T10:11:45+00:00 | no | STAY (importer stays) | B03 |
| `MatedCRT/FirstPass/S7y/OfSteps.lean` | 1 | 0 | 0 | no | 2026-11-10T10:11:04+00:00 | no | STAY (importer stays) | B04 |
| `MatedCRT/FirstPass/S7y/Stmt.lean` | 1 | 0 | 0 | no | 2026-11-11T10:32:42+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/S7y/Vertex.lean` | 1 | 0 | 0 | no | 2026-11-11T10:32:42+00:00 | no | HOLD date | B04 |
| `MatedCRT/FirstPass/SLERef/Corrected.lean` | 1 | 0 | 1 | no | 2026-11-11T10:32:42+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/MatingOfTrees/AdjacentContactWitnesses.lean` | 1 | 0 | 0 | no | 2026-11-11T02:37:52+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/MatingOfTrees/BrownianAdjacencyExcursions.lean` | 1 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/MatingOfTrees/ConnectedCellTraces.lean` | 1 | 0 | 0 | no | 2026-11-11T02:37:52+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/MatingOfTrees/CountableMeshContactTraces.lean` | 0 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/AllStartsClock.lean` | 1 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/AreaScaling.lean` | 2 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/BrownianContinuousVersion.lean` | 1 | 0 | 0 | yes | 2026-11-11T10:24:18+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/CanonicalEntranceKernels.lean` | 0 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/Clock.lean` | 1 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/ClockLimitBorel.lean` | 0 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/ConeAreaLimit.lean` | 0 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/CountableObservableIdentification.lean` | 1 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/CouplingLift.lean` | 0 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/CurveAreaRecovery.lean` | 0 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/FieldCircleScaling.lean` | 1 | 0 | 0 | yes | 2026-11-08T16:04:20+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/FieldVersionTransport.lean` | 0 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/IGUniformShift.lean` | 0 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/MeasurableRadialIntegrals.lean` | 0 | 0 | 0 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroShiftedLaw.lean` | 2 | 0 | 0 | no | 2026-11-09T05:26:31+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroTransfer.lean` | 0 | 0 | 0 | yes | 2026-11-09T15:02:51+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/PostLastZeroWeakLimit.lean` | 0 | 0 | 0 | no | 2026-11-09T05:47:06+00:00 | no | MOVE B01 | B02 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/PrestonPolishTransfer.lean` | 2 | 0 | 0 | no | 2026-11-08T17:44:47+00:00 | no | STAY (importer stays) | B04 |
| `MatedCRT/Proofs/Sec1/EnvironmentScaling/RepresentedCircleCodeLaw.lean` | 1 | 0 | 1 | no | 2026-11-11T02:56:39+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec2/CellSizeHalf/CellModel.lean` | 1 | 0 | 0 | no | 2026-11-05T00:33:35+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec2/CellSizeHalf/Main.lean` | 1 | 0 | 0 | no | 2026-11-05T00:45:03+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec2/VolumeGrowthHalf/Domination.lean` | 2 | 0 | 0 | no | 2026-11-05T00:45:03+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec2/VolumeGrowthHalf/Main.lean` | 1 | 0 | 0 | no | 2026-11-05T00:45:03+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec2/VolumeGrowthHalf/WholePlane.lean` | 1 | 0 | 0 | no | 2026-11-05T00:33:35+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AdmissibleAnnulusScales.lean` | 2 | 0 | 1 | no | 2026-11-07T22:39:31+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnealedTail.lean` | 1 | 0 | 0 | no | 2026-11-08T02:48:38+00:00 | no | STAY (importer stays) | B04 |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnealedTailAE.lean` | 1 | 0 | 0 | no | 2026-11-08T02:49:56+00:00 | no | STAY (importer stays) | B04 |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnealedTailRate.lean` | 2 | 0 | 1 | no | 2026-11-08T02:50:56+00:00 | no | STAY (importer stays) | B04 |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnulusEnvelopeProof.lean` | 1 | 0 | 1 | yes | 2026-11-08T16:54:33+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnulusPolynomialBound.lean` | 1 | 0 | 0 | no | 2026-11-07T09:28:05+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/AnnulusPowerDecay.lean` | 1 | 0 | 0 | no | 2026-11-07T09:22:12+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BoundaryCellAnnulusGeometry.lean` | 2 | 0 | 1 | no | 2026-11-07T22:43:02+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BoundaryCellGeometry.lean` | 3 | 0 | 0 | no | 2026-11-07T14:33:06+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BoundarySurvival.lean` | 4 | 0 | 2 | no | 2026-11-07T13:59:48+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BrownianMinimum.lean` | 1 | 0 | 0 | no | 2026-11-08T19:44:56+00:00 | no | STAY (importer stays) | B04 |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/BrownianMinimumUnique.lean` | 1 | 0 | 0 | no | 2026-11-09T01:10:25+00:00 | no | STAY (importer stays) | B04 |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/CorrectedFromAssembly.lean` | 1 | 0 | 0 | no | 2026-11-08T08:14:57+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DiscrepancyBound.lean` | 1 | 0 | 0 | no | 2026-11-08T03:01:21+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DiscreteExitExcursion.lean` | 3 | 0 | 1 | no | 2026-11-07T15:40:29+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/DyadicAnnulusScales.lean` | 1 | 0 | 0 | no | 2026-11-07T22:37:17+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnlargedBoundaryExit.lean` | 2 | 0 | 0 | no | 2026-11-07T15:17:10+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnteringEdge.lean` | 1 | 0 | 0 | no | 2026-11-07T14:47:14+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnteringEdgeAlternative.lean` | 1 | 0 | 0 | no | 2026-11-07T15:35:17+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/EnteringEdgeExit.lean` | 2 | 0 | 0 | no | 2026-11-07T14:50:42+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ExcursionHitOrder.lean` | 1 | 0 | 0 | no | 2026-11-07T15:19:50+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ExcursionInterpolation.lean` | 2 | 0 | 0 | no | 2026-11-07T14:42:21+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ExcursionRestartReduction.lean` | 1 | 0 | 0 | no | 2026-11-07T15:12:30+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/FiniteCircleHit.lean` | 1 | 0 | 0 | no | 2026-11-07T15:26:14+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/FirstBoundaryEdge.lean` | 1 | 0 | 0 | no | 2026-11-07T15:36:47+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/FirstBoundaryExcursion.lean` | 1 | 0 | 0 | no | 2026-11-07T15:39:27+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSAnnulusSurvival.lean` | 2 | 0 | 0 | no | 2026-11-07T09:34:33+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSBoundaryCellHit.lean` | 1 | 0 | 0 | no | 2026-11-07T22:44:02+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSBoundaryHit.lean` | 2 | 0 | 0 | no | 2026-11-07T14:27:46+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCellAnnulusEvent.lean` | 4 | 0 | 3 | no | 2026-11-08T02:56:16+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCellSizeEvent.lean` | 2 | 0 | 0 | no | 2026-11-07T22:57:27+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCellSizeMeasurable.lean` | 1 | 0 | 0 | no | 2026-11-07T23:01:02+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCutoffMean.lean` | 1 | 0 | 0 | no | 2026-11-08T06:43:48+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSCutoffTail.lean` | 1 | 0 | 0 | no | 2026-11-08T03:11:54+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSDiskMargin.lean` | 3 | 0 | 1 | no | 2026-11-07T22:53:41+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSDyadicBoundaryHit.lean` | 1 | 0 | 0 | no | 2026-11-07T22:40:32+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSEventualRate.lean` | 3 | 0 | 1 | no | 2026-11-08T07:13:07+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSFixedScale.lean` | 1 | 0 | 0 | no | 2026-11-08T06:50:20+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSJointGoodEvent.lean` | 1 | 0 | 0 | no | 2026-11-08T07:14:47+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMeanEventual.lean` | 3 | 0 | 1 | no | 2026-11-08T07:08:43+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMeanRates.lean` | 1 | 0 | 0 | no | 2026-11-08T06:47:52+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMesoscopicHit.lean` | 2 | 0 | 0 | no | 2026-11-07T22:45:41+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSMesoscopicRate.lean` | 1 | 0 | 0 | no | 2026-11-07T22:46:54+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSRateAtDistance.lean` | 1 | 0 | 0 | no | 2026-11-08T02:45:22+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSSafeSurvival.lean` | 1 | 0 | 0 | no | 2026-11-07T13:55:48+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSUniformDistance.lean` | 1 | 0 | 0 | no | 2026-11-08T02:46:28+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSUniformGeometry.lean` | 2 | 0 | 0 | no | 2026-11-07T22:50:31+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/GMSUniformRate.lean` | 3 | 0 | 1 | no | 2026-11-07T22:50:31+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/MesoscopicCutoff.lean` | 5 | 0 | 1 | no | 2026-11-07T07:59:05+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/MesoscopicMeanRates.lean` | 1 | 0 | 0 | no | 2026-11-08T06:46:11+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/MesoscopicMeanScale.lean` | 1 | 0 | 0 | no | 2026-11-08T06:44:45+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PointwiseEnvelopeMean.lean` | 1 | 0 | 0 | yes | 2026-11-08T16:54:33+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PointwiseEnvelopeTail.lean` | 1 | 0 | 0 | yes | 2026-11-08T16:54:33+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/PrehitInterior.lean` | 2 | 0 | 0 | no | 2026-11-07T15:21:37+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateAtDistance.lean` | 1 | 0 | 0 | no | 2026-11-08T02:44:19+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateDiscrepancy.lean` | 3 | 0 | 0 | no | 2026-11-07T04:09:21+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateFromAnnulus.lean` | 1 | 0 | 0 | no | 2026-11-07T16:08:41+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RateTailReduction.lean` | 5 | 0 | 1 | no | 2026-11-07T07:59:59+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartCellInterior.lean` | 3 | 0 | 1 | no | 2026-11-07T15:24:54+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartDependentEvent.lean` | 2 | 0 | 0 | no | 2026-11-07T14:39:05+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartEnlargedDisk.lean` | 1 | 0 | 0 | no | 2026-11-07T15:30:04+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartExcursionOrder.lean` | 1 | 0 | 0 | no | 2026-11-07T15:31:59+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartExcursionProbability.lean` | 1 | 0 | 0 | no | 2026-11-07T15:33:01+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartFiniteCircleHit.lean` | 1 | 0 | 0 | no | 2026-11-07T15:29:05+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/RestartSphereOrder.lean` | 2 | 0 | 0 | no | 2026-11-07T14:43:22+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SafeRadialWalk.lean` | 1 | 0 | 0 | no | 2026-11-07T13:55:48+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SameWalkAssemblyAe.lean` | 1 | 0 | 0 | no | 2026-11-08T18:47:30+00:00 | no | STAY (importer stays) | B03 |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/SameWalkRatesAe.lean` | 1 | 0 | 0 | no | 2026-11-08T19:27:14+00:00 | no | STAY (importer stays) | B04 |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/ShiftInterpolation.lean` | 1 | 0 | 0 | no | 2026-11-07T14:59:42+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/UniformCellSizeMeasurable.lean` | 2 | 0 | 0 | no | 2026-11-08T08:14:57+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyBound.lean` | 2 | 0 | 0 | no | 2026-11-08T03:02:41+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyMeasurable.lean` | 1 | 0 | 0 | no | 2026-11-08T03:05:32+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyMoment.lean` | 1 | 0 | 0 | no | 2026-11-08T03:09:03+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/ConvergenceHarmonicFunctions/WalkDiscrepancyZero.lean` | 1 | 0 | 0 | no | 2026-11-08T03:09:57+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/ApproxClockOccupation.lean` | 3 | 0 | 2 | no | 2026-11-07T10:34:10+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/ClockOccupationSubstitution.lean` | 1 | 0 | 0 | no | 2026-11-07T10:20:27+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/DirichletClockTransfer.lean` | 2 | 0 | 0 | no | 2026-11-08T08:14:57+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/DirichletStoppedClockRepair.lean` | 0 | 0 | 0 | yes | 2026-11-09T07:25:24+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/KilledInverseConvergence.lean` | 1 | 0 | 0 | no | 2026-11-07T14:16:54+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/LocalKilledInverseConvergence.lean` | 1 | 0 | 0 | no | 2026-11-07T14:20:56+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/StoppedClockDenseLimit.lean` | 1 | 0 | 0 | yes | 2026-11-09T07:25:24+00:00 | no | EXCL named | EXCL named |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/CorrectedInputs.lean` | 1 | 0 | 0 | no | 2026-11-11T10:25:59+00:00 | no | HOLD date | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/EnvSigmaDeviation.lean` | 1 | 0 | 0 | no | 2026-11-06T17:50:24+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/Final.lean` | 1 | 0 | 0 | no | 2026-11-11T10:25:59+00:00 | no | HOLD date | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/HolderNets.lean` | 1 | 0 | 0 | no | 2026-11-06T18:00:23+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelection.lean` | 1 | 0 | 0 | no | 2026-11-08T00:52:52+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionDetLimit.lean` | 1 | 0 | 0 | no | 2026-11-08T00:52:52+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionDetStage.lean` | 1 | 0 | 0 | no | 2026-11-08T00:52:52+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionHolder.lean` | 1 | 0 | 0 | no | 2026-11-08T00:42:57+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionMeasurable.lean` | 1 | 0 | 0 | no | 2026-11-08T00:42:57+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionProxy.lean` | 1 | 0 | 0 | no | 2026-11-08T00:42:57+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/ConvergenceDivisible/OdometerSelectionRecursion.lean` | 1 | 0 | 0 | no | 2026-11-08T00:42:57+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec4/Prop42Closure/InsertionAffineCircleLaw.lean` | 2 | 0 | 0 | no | 2026-11-11T03:56:04+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec4/Prop42Closure/InsertionAffineMeasureTransport.lean` | 1 | 0 | 0 | no | 2026-11-11T03:56:04+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec4/Prop42Closure/InsertionCoordinateExtensionProof.lean` | 1 | 0 | 0 | no | 2026-11-11T03:45:21+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec4/Prop42Closure/InsertionDirichletProjection.lean` | 1 | 0 | 0 | no | 2026-11-11T03:45:21+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec4/Prop42Closure/InsertionDyadicDecoder.lean` | 2 | 0 | 0 | no | 2026-11-11T03:45:21+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec4/Prop42Closure/InsertionHarmonicRemainder.lean` | 0 | 0 | 0 | no | 2026-11-11T11:14:36+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec4/Prop42Closure/InsertionLocalCircleRecovery.lean` | 1 | 0 | 0 | no | 2026-11-11T03:45:21+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec4/Prop42Closure/InsertionNormalizedCircleLaw.lean` | 1 | 0 | 0 | no | 2026-11-11T03:45:21+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec4/Prop42Closure/InsertionScalingLawAssembly.lean` | 2 | 0 | 1 | no | 2026-11-11T03:56:04+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec4/SubsequentialConvergence/PreparedSelection.lean` | 1 | 0 | 0 | no | 2026-11-06T23:34:28+00:00 | no | STAY (importer stays) | STAY (importer stays) |
| `MatedCRT/Proofs/Sec5/EarlierTimeCover.lean` | 0 | 0 | 0 | no | 2026-11-11T02:58:40+00:00 | no | HOLD date | B02 |
| `MatedCRT/Proofs/Sec5/FieldCircleVersionProof.lean` | 1 | 0 | 0 | no | 2026-11-11T02:58:40+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/Sec5/StoppedActualMarginCode.lean` | 2 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec5/StoppedActualSurplus.lean` | 1 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec5/StoppedActualValueVersions.lean` | 1 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec5/StoppedCompactCode.lean` | 1 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec5/StoppedInteriorGeometryMeasurable.lean` | 0 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/Sec5/StoppedInteriorGeometryProof.lean` | 1 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/Sec5/StoppedLayerPotentialReduction.lean` | 0 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/Sec5/StoppedMarginContinuousDecoder.lean` | 2 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec5/StoppedMarginProducerAssembly.lean` | 0 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/Sec5/StoppedMarginStepAssembly.lean` | 1 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/Sec5/StoppedMarginValueVersions.lean` | 1 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec5/StoppedPoleInnerDegreeMoments.lean` | 0 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B03 |
| `MatedCRT/Proofs/Sec5/StoppedRationalMembership.lean` | 1 | 0 | 0 | no | 2026-11-11T03:25:57+00:00 | no | HOLD date | B04 |
| `MatedCRT/Proofs/Sec6/ChanceOfBeingAbsorbed/Statement.lean` | 1 | 0 | 0 | no | 2026-11-11T03:04:08+00:00 | no | HOLD date | STAY (importer stays) |

## Hazards and notes

- `archive/` importers: 31 files under `archive/` import candidates that are still under `MatedCRT/`. They are not built, so they do not block a move, but each move makes that archived import dangle. Listed by the `outside` column.
- A candidate with importers is never moved before them; a candidate imported by a stayer stays.
- The date condition is the binding constraint: 171 of 272 candidates were committed after 2026-11-11 00:05:14 UTC, the most recent at 2026-11-11T11:14:36+00:00 (HEAD 689539f8).
- No candidate has uncommitted edits (`git diff --name-only HEAD` does not list any candidate).


## Update after rule R2 (2026-11-11)

Rule R2 (`docs/campaign/ARCHIVE.md`, section "Rule R2 (2026-11-11), batches B13 onward") replaces the 00:05:14 UTC condition used for the table above. The closure and the roots are unchanged; the moved modules were not reachable from them.

- Moved under R2: 202 modules in six batches: B13 `46f75d04` (40), B14 `fbd1f17d` (40), B15 `5c48639e` (40), B16 `b005d22e` (40), B17 `21dc7c40` (40), B18 `1ae21b45` (2). Each batch: 0 imports of its own modules from files under `MatedCRT/`.
- Still in `MatedCRT/` (70 candidates, at the last batch):
  - e: 38, listed in `notes/hyg-A.txt`, `hyg-B.txt`, `hyg-C.txt`, `stale-1.txt` or `stale-1b.txt` while z9 and z10 report IN_PROGRESS (`MatedCRT/FirstPass/S4e.lean` is also named, see b);
  - d: 30, imported by a file that stays under `MatedCRT/`;
  - b: 1, `MatedCRT/FirstPass/S1c/Composition.lean` (named in a tasks file modified on 2026-11-11);
  - a: 1, `MatedCRT/FirstPass/LPBridge/GFFInterface.lean` (its commit f5419921, after the cutoff, adds code);
  - uncommitted edits: 0.
- If z9 and z10 read DONE, 66 of the 70 are movable (two batches, 40 and 26); the 4 still held would be `S1c/Composition.lean`, `S4e.lean`, `LPBridge/GFFInterface.lean` and `S4e/RescaledDecode.lean` (imported by `S4e.lean`).
- Not from these batches: 11 dangling imports from 8 untracked files under `MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/` (e.g. `JointL1AxiomsY5.lean`) import modules archived earlier. Their owner must act before those files are committed.

## Final update (rule R2, batches B19 and B20, 2026-11-11)

After z9 and z10 reported DONE (z11 was DONE), the 38 hygiene/stale files of the pinned list became movable. Batches B19 `f3352f00` (40 modules) and B20 `1c285f95` (26 modules) moved them. Total moved under rule R2 in this round: 268 modules (B13 to B20).

Still in `MatedCRT/` (4 candidates, at the commit of B20):
- a: `MatedCRT/FirstPass/LPBridge/GFFInterface.lean` (its commit f5419921, after the cutoff, adds code);
- b: `MatedCRT/FirstPass/S1c/Composition.lean` and `MatedCRT/FirstPass/S4e.lean` (named in a tasks file modified on 2026-11-11);
- d: `MatedCRT/FirstPass/S4e/RescaledDecode.lean` (imported by `S4e.lean`, which stays).

The closure is unchanged: 1819 lean files (1818 under `MatedCRT/` plus `MatedCRT.lean`). The moved modules were not reachable from the roots. The 11 pre-existing dangling imports from untracked files (see the update above) are still open.
