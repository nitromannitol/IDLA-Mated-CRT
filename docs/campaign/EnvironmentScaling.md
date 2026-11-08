# Environment scaling proof obligations

The conditional reduction is `MatedCRT.coneEnvironmentScalingStep_of_inputs` in
`MatedCRT/Proofs/Sec1/EnvironmentScaling.lean`. Its three new hypotheses are
proof steps, not literature axioms. Their complete Lean types are their named
`Prop` declarations in that file. Paper line references below refer to
`paper/idla_mated_crt-corrected.tex`.

## Update: audited written proofs available (2026-11-08 09:45 UTC)

**WRITTEN-PROOF-AVAILABLE / LEAN-PENDING.** The operator supplied and
independently audited all three arguments below. See
[exact proof routing and source locators](ENV-STEPS-ROUTING-20261108.md).
The pinned proof is fleet `notes/env-steps/env-steps.tex`: field 299-335,
clock 449-487, mating 942-981, with supporting lemmas listed in that note.
m1 owns the field proof, z1 the all-start clock proof, and m5 the same-space
mating infrastructure. These Steps remain hypotheses until their Lean proofs
are checked. The stopped-clock gap has a separate existential repair; arbitrary
supplied `G` is not justified. No frozen declarations were changed.

## Historical requests (written-proof need superseded by the update)

The descriptions and earlier source observations below record the original
requests. The new pinned DMS source is arXiv:1409.7055v4, as audited.

1. `MatedCRT.RescaledConeFieldStep : SpaceFillingSLEModel → Prop`: for a valid
   environment and an a.s. equal measurable circle version, construct measurable
   rescaled pairings with the stated a.s. equality to `rescaledPairing`, radial
   and lateral independence, lateral law, and field-sigma inclusion. The paper
   uses the transformed field at lines 3617–3625 and its equality in law at
   lines 452–459. DMS14 Proposition 4.13(i), arXiv:1409.7055v5 p. 80, gives
   field equality in law; `QuantumConeScalingInput` records the circle-process
   part, but the repository's pairing, lateral and sigma bridges require proof.
2. `MatedCRT.RescaledConeClockStep : SpaceFillingSLEModel → Prop`: for the
   rescaled circle version, construct one clock satisfying `IsLQGClock` and
   `IsTimeChangeClock` simultaneously for every starting point, with the exact
   quantifier order in the declaration. The paper uses the cone and LBM at
   lines 705–712 and scaling at 3617–3625. GRV16 Theorem 2.7 and Berestycki
   2015 Theorem 1.4 do not state this full whole-plane, all-starting-points
   representation for the repository's clock definition.
3. `MatedCRT.RescaledMatingOfTreesStep : SpaceFillingSLEModel → Prop`: given
   the rescaled cone and its actual transformed pairings, construct the complete
   `IsMatingOfTreesCoupling` with rescaled boundary pair, curve and pairings, as
   quantified in the declaration. The paper uses the mated-CRT coupling in its
   setup and scaling at lines 3617–3625. DMS14 Theorem 1.9, pp. 26–27, gives
   the boundary Brownian motion and translation invariance, not the full
   repository-specific coupling representation; covariance beyond κ′ ≤ 8 also
   needs the corresponding extension.

The measurable circle modification and field-measurable version of the cone
scale radius are proved in Lean; neither is an additional step hypothesis.
`RescaledEnvironmentInput` is retained only as a legacy declaration: its exact
raw-circle measurability requirement has the null-set defect explained in its
docstring, and the new reduction does not use it.


## Operator19:35 final circle-recovery return

Operator19:35 released the final three written-proof requests: fleet `notes/wpn-steps3/steps3.tex`, sha256 `d34cf930706e195c09ec2eb14c8999a6a1d64cc6b69938b6e227d2ddf9619d9d`, independent `AUDIT-steps3.md` VERDICT CORRECT for all three outcomes. This is written proof availability, not Lean closure. No further prover rounds will occur under operator18:55. The original representative and raw-circle Steps are false; only the specified bounded/represented repairs may be implemented. The insertion extension is internal mathematics, never a literature hypothesis presented as DS11.

The raw ConeDilationCircleApproximationStep is refuted. Its represented replacement is exactly RescaledConeDistributionCircleGridStep, with the measurable simultaneous distribution representation already in that declaration. The current canonical m1 task is preserved and its successor implements this direct route; see [final audited routing](STEPS3-ROUTING-20261108.md). This does not close RescaledConeFieldStep, clock or mating.
