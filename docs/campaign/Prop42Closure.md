# Proposition 4.2 closure: campaign notes (z5 and m6)

Written argument: `notes/prop42-proof/prop42-proof.tex` (fleet directory; draft lines = its line numbers; audit `AUDIT.md`,
verdict CORRECT). Claims: `notes/prop42-claims.md`. Status and blockers: `reports/z5.md`.

## Closure step (z5)

- Targets: `ConePrematureContactNullStep` (`MatedCRT/Proofs/Sec4/Prop42Closure/HalfBallClosure.lean:59`) and the frozen
  `ConeHalfBallClosureInsideStep` (`MatedCRT/Proofs/Sec2/ConeFamilyMeasurable/StoppedClosure.lean:18`, not edited).
- Proved (commit 00a5dd4, `HalfBallClosure.lean`): `closure_subset_ball_of_not_halfBallPrematureContact` (draft lines 291-304)
  and `coneHalfBallClosureInsideStep_of_prematureContactNull`.
- Transfer chain (commit d4373bd, `Prop42Closure/ConePrematureNull.lean`): `conePrematureContactNullStep_of_inputs` and
  `coneHalfBallClosureInsideStep_of_inputs`. Both targets are proved CONDITIONALLY on the named inputs listed below.
  The chain: (A) a.s. `μ ∈ E` iff premature contact of `μ` (`E` from `exists_measurable_halfBallPrematureContact`,
  `ContactEvent.lean:11`); (B) restriction to `B_1` does not change the event (`RestrictionLocality.lean`); (C) fact (2) for
  restricted LQG measures and `IdentDistrib.measure_mem_eq`; (D) on the whole plane the premature event is null (plateau
  argument: `plateau_of_prematureContact`, `plateau_measure_zero_of_ae_radii_family`).
- Named inputs of the chain: `VolumeGrowthStmt` (IDLA Lemma 2.7; its cone a.s. consequence is proved in
  `ConeVolumeGrowth.lean`, commit 87fdfc4); `WholePlaneVolumeGrowthAeStep` (B1, whole-plane side, named); `WholePlaneLQGModelStep`
  (B2, named, see F4); `ConeWholePlaneRestrictedLQGLawStep` (G1, named, not derived, see F6); `PlateauScaleInvarianceStep`
  (fact (1), `HalfBallPlateau.lean`, HB Lemma 5.7); `HarmonicBallLocalSetStmt`; `ExistenceHarmonicBallsStmt` and
  `ClusterStrongCompatibilityStmt` (components of `HarmonicBallsDraftInputs`, `MatedCRT/Proofs/Sec2/Final.lean:40`).
- Fact (2) as stated: `ConeWholePlaneFieldLawStep` (fields on `B_1`, IdentDistrib of restricted pairings and circle averages,
  `ConeWholePlaneSteps.lean`), and the LQG-level form `ConeWholePlaneRestrictedLQGLawStep` (see F6).

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
- F3 (blocker B1, now split). The premature-contact set is measurable only through `exists_measurable_halfBallPrematureContact`
  (`ContactEvent.lean:11`), which needs local finiteness and `VolumeGrowth (ν) (3/4) βm βp`. Status: the cone a.s. volume growth
  is PROVED from `VolumeGrowthStmt` (`ConeVolumeGrowth.lean`, 87fdfc4); the whole-plane a.s. volume growth is the named input
  `WholePlaneVolumeGrowthAeStep`. The a.e. measurability of the whole-plane radii is PROVED (`PlateauRadii.lean`, 19e2edd, from
  `HarmonicBallLocalSetStmt` and the regularized-to-harmonic bridge), and the a.e. version of `plateau_measure_zero` is PROVED
  (`PlateauAE.lean`, 26e44d5).
- F4 (blocker B2). Fact (2) quantifies over whole-plane fields, so the transfer needs one whole-plane GFF with its `γ`-LQG
  measure. `wholePlaneGFF_exists` (`MatedCRT/Proofs/Field/WholePlaneExistence.lean:46`) gives the GFF only. Harmonic-Balls
  `LQGMeasureExistence` (`HarmonicBalls/Proposed/LQG.lean:66`) is a Proposed statement, and `MatedCRT/Proposed/Berestycki2017.lean`
  is in-probability GMC on a bounded domain, not the a.s. dyadic vague limit of `IsLQGMeasureOfField`. So B2 stays a named input.
- F5 (domain of eq. (2.4)). Eq. (2.4) is `h|_{B_1} =_d (h^ℂ − γ log|·|)|_{B_1}`, on `B_1`, not `B_{3/4}`. The draft
  uses it on `B_{3/4}` (lines 275-289). Fact (2) is stated on `B_1` (the paper's form); the `B_{3/4}` statement follows
  by restriction, and the cluster locality needed for the transfer is proved (`RestrictionLocality.lean`).
- F6 (gap G1: LQG-level restricted law). `ConeWholePlaneRestrictedLQGLawStep` is not derived from the field law. Decomposition
  of what a derivation needs:
  (i) Paper Fact (LQG measure) II, "Locality" (`idla_mated_crt-corrected.tex`, around lines 478-480; repo
  `Steps/Sec2/LQGMeasureProperties.lean`, `LQGMeasureLocalityPart`): for each deterministic open `U`, `μ_h(U)` is a measurable
  function of `h|_U`. It is stated for the quantum cone `h` (Definition 2.1). The paper's sentence before the Fact (lines
  ~470-473) gives the construction of `μ_{h+f}` for the whole-plane GFF, not a locality statement for `h^ℂ − γ log|·|`. So the
  whole-plane locality needed for the whole-plane side is not stated in the paper: a gap to route.
  (ii) From locality on open sets to the law of the restricted measure on `B_1`: a countable ring of finite unions of differences
  of rational balls inside `B_1` generates the Borel sets, and the law of a random finite measure is determined by the joint
  laws of its values on that ring (monotone class and π-λ). Not in Mathlib in usable form; not written in the paper.
  (iii) Doob-Dynkin for `μ(U)` measurable w.r.t. `σ(h|_U)`, with `σ(h|_U) ⊆ σ(h|_{B_1})`.
  Decision for the operator: accept `ConeWholePlaneRestrictedLQGLawStep` as a named input, or route (i) and (ii).
- F7 (possible reduction of B1w). Volume growth at radius `3/4` depends only on the restriction to `B_1` (balls of radius `< 1/4`
  centred in `B_{3/4}` lie in `B_1`). So B1w might follow from B1c and G1 if the volume-growth event is measurable on the
  space of measures. Not done; the measurability of that event is open.
- Option B (deriving (1) from `ClusterScaleInvarianceStmt`, `ClusterStrongCompatibilityStmt`, `UniquenessHarmonicBallsStmt`):
  recorded as a candidate for a later audited task; not built (operator ruling).
- Not used: `ConeHarmonicBallsUpToFixedTimeStmt` (Lemma 2.4, `Draft/Section2.lean:62-70`) to derive the closure step.
  Its stopped-pair clause `T' = T` is the content that the closure step supplies (see F1).
