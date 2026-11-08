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
  Route (operator ruling 2026-11-08; task `z5-prop42-premature-contact`):
  - Fact (1), `PlateauScaleInvarianceStep`, and fact (2), `ConeWholePlaneLocalLawStep`, are Step Props in
    `MatedCRT/Proofs/Sec4/Prop42Closure/HalfBallPlateau.lean`. Fact (2) is stated for the LQG measures restricted to
    `B_1`: this is the form of [IDLA] eq. (2.4) (`eq:gff`, paper line 443), and the `B_{3/4}` event is determined by the
    measure on `B_1` (F5).
  - Proved there: `plateauValues_countable` (draft line 243), and `plateau_measure_zero` (draft lines 245-268: `p` is
    constant by (1), Tonelli on `[1,2]`, countable sections), with the measurability of the radii at rational times
    (draft lines 259-263) as the explicit premise `hR`.
  - Proved in `MatedCRT/Proofs/Sec4/Prop42Closure/HalfBallPremature.lean`: `plateau_of_prematureContact` (pointwise:
    premature contact of the raw `3/4`-clusters forces `1/2 ∈ plateauValues` of the global family, from monotonicity,
    [HB] Lemma 5.8 at `z = 0`, `U = B_{3/4}` (`ClusterStrongCompatibilityStmt`), and openness of the clusters), and
    `clusterOn_ball_eq_cluster`. Only standard axioms.
  - Not yet built: the locality of the `3/4`-clusters under restriction to `B_1` (provable from `LaplacianLE`), the a.e.
    version of `plateau_measure_zero`, and the transfer from the cone to the whole-plane field by (2). The transfer
    needs blockers B1 and B2 (Findings F3, F4). Blockers and decisions in `reports/z5.md`.
- Option B (deriving (1) from `ClusterScaleInvarianceStmt`, `ClusterStrongCompatibilityStmt`, `UniquenessHarmonicBallsStmt`):
  recorded as a candidate for a later audited task; not built (operator ruling).
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
- F3 (measurability, not in the draft's argument). The draft's events are "measurable" (lines 277-279) and the plateau
  indicator is measurable (lines 259-263). In Lean the premature-contact set is measurable only through
  `exists_measurable_halfBallPrematureContact` (`ContactEvent.lean:11`), which needs `IsLocallyFiniteMeasure` and
  `VolumeGrowth (ν) (3/4) βm βp` for the measure `ν`. So the transfer from the cone needs a.s. `VolumeGrowth (μ ω) (3/4)`
  for the cone LQG measure and for the whole-plane LQG measure: blocker B1. The repo's `volumeGrowth` input is open
  (`VolumeGrowthStmt`, `MatedCRT/Draft/Section2.lean:121`).
  The whole-plane radii are measurable by `aemeasurable_wholePlaneHarmonicBall_family`
  (`WholePlaneFamily.lean:12`, needs `HarmonicBallLocalSetStmt`), but only almost everywhere; the a.e. version of
  `plateau_measure_zero` is still to write.
- F4 (existence of the whole-plane model). Fact (2) quantifies over whole-plane fields, so applying it needs one whole-plane
  GFF with its `γ`-LQG measure on a probability space. `wholePlaneGFF_exists` (`MatedCRT/Proofs/Field/WholePlaneExistence.lean:46`)
  gives the GFF only; I found no Lean existence statement for `IsLQGMeasureOfField P' γ γ hcirc' μ'`: blocker B2.
- F5 (domain of eq. (2.4)). Eq. (2.4) is `h|_{B_1} =_d (h^ℂ − γ log|·|)|_{B_1}`, on `B_1`, not `B_{3/4}`. The draft
  uses it on `B_{3/4}` (lines 275-289). Fact (2) is stated on `B_1` (the paper's form); the `B_{3/4}` statement follows
  by restriction, and the cluster locality needed for the transfer is provable.
