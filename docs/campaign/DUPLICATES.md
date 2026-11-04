# Duplicate infrastructure (for the final cleanup)

Worker A, 2026-11-04 (task defs-consistency). One entry per mathematical fact: the declarations proving it, their users
(files, as of the working tree of 2026-11-04 14:35 UTC), and the CANONICAL declaration the others should be replaced
by. Nothing has been edited in the owners' files. Paths are relative to MatedCRT/. "Same statement" means equal up to
unfolding `IsLocallyFiniteMult m := ∀ a, {b | m a b ≠ 0}.Finite` (Proofs/Infra/DiscretePotential.lean:23).

## D1. `Δ G_A(·, b) = -δ_b` on a finite `A` (eq:discrete-green-laplacian, l.797)
- `MatedCRT.greenFn_laplacian_fst` — Proofs/Sec4/ObstacleSpecialization/GreenMarkov.lean:57 (x1, from c1's abstract
  `laplacian_toReal_of_recursion`, Proofs/Sec4/GreenRecursion.lean:108). Users: GreenMarkov.lean (the proved steps
  `greenKernelLaplacianStep` :72, `normExitTimeLaplacianStep` :77, hence Proofs/Sec3/UniformConvergenceGreenKernel/
  {BoundaryMaximum,HarmonicAwayFromPole}.lean, Proofs/Sec4/DivSandpileLowerBound/OdometerComparison.lean,
  Audit/Reductions.lean), Proofs/Sec5/LLowerBound/GreenSum.lean, Proofs/Sec5/MeanValueInequality/GreenReversibility.lean.
- `MatedCRT.WalkPotential.mLaplacian_greenFn` — Proofs/WalkPotential/GreenFirstStep.lean:210 (c3, self-contained
  first-step analysis). Same statement. Users: Proofs/Sec3/DiscreteDirichletProblem/GreenRepresentation.lean,
  Steps/Sec7/MassBoundOdometer.lean, Steps/Sec7/OdometerBoundMass.lean.
- CANONICAL: `MatedCRT.greenFn_laplacian_fst` (it carries the two proved Steps). Cleanup: move GreenRecursion.lean,
  Proofs/Sec4/GreenFirstStep.lean and GreenMarkov.lean:1-70 to Proofs/Infra/ (they are not Section 4 specific);
  replace c3's theorem by the canonical one (same explicit arguments `hlf hcons hA b`), then delete the lemmas of
  WalkPotential/GreenFirstStep.lean:65-224 which have no other user (D2, D3 below; check each name first).

## D2. Truncated visit counts `∑_{n < N} 1{n < τ_A, x_n = b}`
- `MatedCRT.visitsTrunc` — Proofs/Sec4/GreenFirstStep.lean:46 (c1), with `visitsTrunc_mono` :53, `_zero` :65,
  `_succ` :69, `_of_not_mem` :62, `measurable_visitsTrunc` :89, `visitsBeforeExit_eq_iSup` :49.
- `MatedCRT.WalkPotential.visitsUpTo` — Proofs/WalkPotential/GreenFirstStep.lean:73 (c3): IDENTICAL body; with
  `measurable_visitsUpTo` :76, `visitsUpTo_eq_zero` :84, `visitsUpTo_pathCons` :90, `visitsBeforeExit_eq_iSup` :108
  (same name as c1's, other namespace), `lintegral_visitsBeforeExit_eq_iSup` :113.
- CANONICAL: `visitsTrunc` and its lemmas (c1). `visitsUpTo` is used only inside c3's file.

## D3. First-step decomposition `E^a[F] = ∫ E^c[F((a, ·))] p(a, dc)`
- `MatedCRT.lintegral_srwLaw_firstStep` — Proofs/Sec4/ObstacleSpecialization/GreenMarkov.lean:24 (x1).
- `MatedCRT.WalkPotential.lintegral_srwLaw_eq_pathCons` — Proofs/WalkPotential/GreenFirstStep.lean:123 (c3): identical
  statement and proof; `lintegral_firstStep` :135 is its corollary for `F((a, y)) = k + H(y)`.
- CANONICAL: one lemma in Proofs/WalkPotential/Markov.lean next to `srwLaw_eq_srwFirstStepLaw` (:234), the fact both
  unfold; name `lintegral_srwLaw_eq_firstStep` (either existing name is acceptable). Users: only the two files above.

## D4. Finitely many cells meet a bounded set (continuous proper `η`)
- `MatedCRT.cellVertices_finite_of_isBounded` — Proofs/Sec4/ObstacleSpecialization.lean:24 (c1). Users: same file
  (:53, :63, :70), Proofs/Sec4/ConvergenceDivisible/MatedLeastMeasurable.lean:47.
- `MatedCRT.Tightness.cellVertices_finite` — Proofs/Sec3/DiscretePotentialTightness/Cells.lean:34 (c1, untracked):
  same statement.
- `MatedCRT.cellVertices_finite_of_isCompact` — Proofs/Infra/LocallyFinite.lean:19 (A): weaker (compact `K`). Users:
  LocallyFinite.lean:52, Proofs/Sec4/DivSandpileLowerBound/OdometerComparison.lean, Steps/Sec7/OdometerBoundMass.lean.
- CANONICAL: `cellVertices_finite_of_isBounded`, moved to Proofs/Infra/LocallyFinite.lean (owner A) at the cleanup;
  `cellVertices_finite_of_isCompact hη hp hε hK` becomes `cellVertices_finite_of_isBounded hη hp hε hK.isBounded`.
  (Not moved now: both names in namespace `MatedCRT` would clash in modules importing both files.)

## D5. Local finiteness when adjacent vertices have intersecting cells
- `MatedCRT.isLocallyFiniteMult_of_cells_meet` — Proofs/Infra/LocallyFinite.lean:46 (A), concludes
  `IsLocallyFiniteMult m`. Users: LocallyFinite.lean:63 (`MatedCRTEnv.IsValid.ae_isLocallyFiniteMult` :57, used in
  Sec3/ConvergenceNormalizedExitTime, Sec4/DivSandpileLowerBound/OdometerComparison, Sec5/LLowerBound/OfEvents,
  Steps/Sec2/MaximumPrinciple), Steps/Sec7/OdometerBoundMass.lean:62.
- `MatedCRT.locallyFinite_of_cells_meet` — Proofs/Sec4/ObstacleSpecialization.lean:59 (c1), the same fact at one vertex
  `a`. Users: same file :83, Proofs/Sec4/ConvergenceDivisible/MatedLeastMeasurable.lean:98.
- CANONICAL: `isLocallyFiniteMult_of_cells_meet` (c1's is `isLocallyFiniteMult_of_cells_meet hη hp hε hcell a`), and
  for random environments `MatedCRTEnv.IsValid.ae_isLocallyFiniteMult`.

## D6. A vertex with an edge has positive degree (locally finite `m`)
- `MatedCRT.mdeg_pos_of_ne_zero` — Steps/Sec4/ObstacleSpecialization.lean:63 (c1; a theorem in a Steps file).
  Users: Proofs/Sec3/ConvergenceNormalizedExitTime/GreenSumBump, Proofs/Sec4/{ConvergenceDivisible/
  MatedLeastMeasurable, DivSandpileLowerBound/OdometerComparison, GreenLaplacian, GreenRecursion,
  ObstacleSpecialization/GreenMarkov}, Proofs/Sec5/{LLowerBound/GreenSum, MeanValueInequality/GreenReversibility,
  MeanValueInequality/ObstacleComparison}.
- `MatedCRT.mdeg_ne_zero_of_ne_zero` — Proofs/WalkPotential/MaximumPrinciple.lean:53 (c3): the `≠ 0` form. Users:
  Proofs/Sec7/CrudeUpperBound/GreedyPath, Proofs/WalkPotential/{Comparison, GreenFirstStep}, Steps/Sec7/CrudeUpperBound.
- CANONICAL: `mdeg_pos_of_ne_zero`, moved to Proofs/Infra/DiscretePotential.lean (owner A) at the cleanup;
  `mdeg_ne_zero_of_ne_zero hlf h = (mdeg_pos_of_ne_zero hlf h).ne'`.

## D7. `a^ε_0 = 0` when `η` does not visit `0` at negative times (E-x3-3, CORRECTIONS (R1))
- `MatedCRT.vertexOf_zero_eq_zero_of_no_earlier_visit` — Proofs/Sec4/DivSandpileLowerBound/SourceVertex.lean:32 (x3),
  with the a.s. forms `MatedCRTEnv.IsValid.ae_no_earlier_origin_visit` :98 and `...ae_vertexOf_zero_eq_zero` :125.
- `MatedCRT.vertexOf_zero_of_no_earlier_visit` — Proofs/Sec5/MeanValueInequality/CellRepresentative.lean:113 (x1).
- CANONICAL: x3's three lemmas (move SourceVertex.lean to Proofs/Infra/ at the cleanup: Sections 3-6 use it).

## D8. Local finiteness hypothesis written out
`IsLocallyFiniteMult m` (Proofs/Infra/DiscretePotential.lean:23; 28 files) and the unfolded
`∀ a, {b | m a b ≠ 0}.Finite` (32 files, e.g. Proofs/Sec4/GreenLaplacian.lean throughout, Sec5, Sec7) are the same
Prop by definition, so mixing them costs nothing at use sites. CANONICAL for new proofs: `IsLocallyFiniteMult m`; the
Defs field `IsObstacleSetting.locallyFinite` (Defs/Sandpile.lean) keeps the unfolded form.

## Related, not duplicates (checked)
- `greenFn_eq_zero_of_not_mem` (Proofs/Infra/RandomWalk.lean:44, start outside `A`) vs
  `greenFn_eq_zero_of_not_mem_right` (Proofs/Sec7/OdometerBoundMass/Laplacian.lean:30, target outside `A`).
- `kernel_symm_of_laplacian` (Proofs/Sec4/GreenLaplacian.lean:189) vs `greenKernel_symm_of_firstStep`
  (Proofs/Sec5/MeanValueInequality/Reversibility.lean:30): both give symmetry of the Green kernel; compare at cleanup.
