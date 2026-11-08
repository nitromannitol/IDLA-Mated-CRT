# Proposition 4.2 closure: campaign notes (z5 and m6)

Written argument: `notes/prop42-proof/prop42-proof.tex` (fleet directory; draft lines = its line numbers; audit `AUDIT.md`,
verdict CORRECT). Claims: `notes/prop42-claims.md`.

## Closure step (z5)

- Target: `ConeHalfBallClosureInsideStep` (`MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18`), frozen
  statement, not edited.
- Proved (commit 00a5dd4, `MatedCRT/Proofs/Sec4/Prop42Closure/HalfBallClosure.lean`):
  - `closure_subset_ball_of_not_halfBallPrematureContact` (draft lines 291-304): if the raw `3/4`-clusters of `ν` have no
    premature contact (`halfBallPrematureContact`, `HorizonContact.lean:11`), every family stopped at `T` satisfies
    `closure (Λ t) ⊆ B_{1/2}` for `0 < t < T`.
  - `coneHalfBallClosureInsideStep_of_prematureContactNull`: the target from `ConePrematureContactNullStep`.
- Open input: `ConePrematureContactNullStep` (draft lines 275-289 with the plateau lemma of lines 230-274). Not proved.
  Route and blockers in `reports/z5.md`.
- Not used: `ConeHarmonicBallsUpToFixedTimeStmt` (Lemma 2.4, `Draft/Section2.lean:62-70`) to derive the closure step.
  Its stopped-pair clause `T' = T` is the content that the closure step supplies (see Findings, F1).

## Proposition 4.2 assembly (z5)

- Commit 9c6ad35, `MatedCRT/Proofs/Sec4/Prop42Closure/Assembly.lean`: `divSandpileLowerBound_prop42` (the printed
  Proposition 4.2, `DivSandpileLowerBoundStmt`) and `discreteClusterInnerBound_prop42` (`DiscreteClusterInnerBoundStep`),
  delegating to `Final.lean`.
- Hypotheses: `h41` (Thm 4.1), `h23` (Thm 2.3), `h24` (Lemma 2.4), `h27` (Lemma 2.7), `h28` (Lemma 2.8), `h33` (Lemma 3.3),
  `hfam` (`ConeFamilyAEMeasurableStep`), and `hgap` (`HarmonicBallStrictObstacleGapStep`, the only Prop 4.2-specific one).

## Strict gap (m6)

(m6 to write.)

## Findings

- F1 (Lemma 2.4, `T' = T`). The corrected paper's proof of Lemma 2.4 (`idla_mated_crt-corrected.tex:533-545`) cites
  [HB] Prop. 5.6 for uniqueness of the family. That covers the family, not the stopping time. The Lean statement
  `ConeHarmonicBallsUpToFixedTimeStmt` also asserts `T' = T` for any stopped pair. Given family uniqueness and monotonicity,
  `T' = T` follows from the closure step (closure containment at `T'` or `T` would contradict the other stopping
  property), so the clause is not an independent input and assuming it to prove the closure step would be circular.
- F2 (Harmonic-Balls Lemma 5.7). The Lean `ClusterScaleInvarianceStmt` (`Harmonic-Balls-LQG/HarmonicBalls/Draft/Section5.lean:226`)
  relates the radius-1 clusters `cluster μ 1 z t` to rescaled radius-`k` clusters. Its docstring describes the printed
  `Λ^z_t`, which is the global whole-plane family in the Section 5 docstring but `cluster μ 1 z t` in Section 6
  (`Section6.lean:20`). The plateau argument needs the scaling of the global family, so the reading matters.
