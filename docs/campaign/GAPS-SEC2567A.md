# Section 2, 4–7 and Appendix A triage

## E-A4 — FINE-AS-PRINTED in the corrected draft

The preserved arXiv version is false for infinite sets: take A to be the entire graph and u ≡ 1; the exterior boundary is empty. The corrected draft already replaces the hypothesis by “nonempty finite subset” in [C2] (corrected.tex:826–832).

Proof of the corrected form: the mated-CRT graph is connected and infinite (successive integer vertices are adjacent). Every vertex of finite A has a path to Aᶜ. Choose a maximum M of u on A. If M exceeds every exterior boundary value, subharmonicity at any maximizer forces all its neighbors to have value M: their weighted average is at least M while none exceeds M. Following a path from a maximizer to Aᶜ gives a boundary vertex of value M, a contradiction. The argument does not require A to be connected. Empty A is excluded because the maximum is undefined.

Downstream checks: the discrete applications at corrected.tex:1042–1048, 1227, 1346–1351, 1382, 1516, 1640, 1817, 2124, 3002, 3062 and 3207–3211 use vertex sets inside a bounded ball or a finite discrete cluster, hence finite by local finiteness; empty domains make the comparison vacuous. The analogous Appendix A applications at 3460 and 3529 use its finite V. The continuum maximum principle at 1957 is independent. Thus [C2] suffices for these uses; this verdict does not establish unrelated hypotheses in those arguments.

## E-x2-2 — FALSE

At corrected.tex:1558–1564 the second equality asserts that the cluster is the graph closure of the positive odometer set. Take any 0 < t ≤ ε. The initial mass M = t/ε is in (0,1], so the initial configuration is already stable: no vertex topples, the odometer is identically zero, and the final positive-mass set is {0}. The closure of the positive odometer set is empty. This is a counterexample on every graph, independent of the random environment. The same issue affects the displayed identity at 1703–1705 and 2947–2951.

A proposed replacement for the cluster identity, for M > 0, is Dε(M) = {0} ∪ cl{v > 0}. Every toppled vertex retains positive mass and each neighbor receives positive mass; conversely each positive-mass vertex other than the source must have received mass from a toppled neighbor. For M > 1, the source topples, so it is already in the positive odometer set. Consequently the unmodified identity is valid in the fixed-t, ε → 0 applications once ε < t; this observation does not justify the displayed claim for all t and ε, nor the separate equality of stopped and unstopped odometers. These identities are formalized as `Sandpile.cluster_eq_insert_closure` and the counterexample as `Sandpile.cluster_of_mass_le_one`.
