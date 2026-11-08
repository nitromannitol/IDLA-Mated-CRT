# Environment scaling proof obligations

The conditional reduction is `MatedCRT.coneEnvironmentScalingStep_of_inputs` in
`MatedCRT/Proofs/Sec1/EnvironmentScaling.lean`. Its three new hypotheses are
proof steps, not literature axioms. Their complete Lean types are their named
`Prop` declarations in that file. Paper line references below refer to
`paper/idla_mated_crt-corrected.tex`.

## NOT IN SOURCES: needs a written proof

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
