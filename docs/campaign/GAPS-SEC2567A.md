# Section 2, 4–7 and Appendix A triage

## E-A4 — FINE-AS-PRINTED in the corrected draft

The preserved arXiv version is false for infinite sets: take A to be the entire graph and u ≡ 1; the exterior boundary is empty. The corrected draft already replaces the hypothesis by “nonempty finite subset” in [C2] (corrected.tex:826–832).

Proof of the corrected form: the mated-CRT graph is connected and infinite (successive integer vertices are adjacent). Every vertex of finite A has a path to Aᶜ. Choose a maximum M of u on A. If M exceeds every exterior boundary value, subharmonicity at any maximizer forces all its neighbors to have value M: their weighted average is at least M while none exceeds M. Following a path from a maximizer to Aᶜ gives a boundary vertex of value M, a contradiction. The argument does not require A to be connected. Empty A is excluded because the maximum is undefined.

Downstream checks: the discrete applications at corrected.tex:1042–1048, 1227, 1346–1351, 1382, 1516, 1640, 1817, 2124, 3002, 3062 and 3207–3211 use vertex sets inside a bounded ball or a finite discrete cluster, hence finite by local finiteness; empty domains make the comparison vacuous. The analogous Appendix A applications at 3460 and 3529 use its finite V. The continuum maximum principle at 1957 is independent. Thus [C2] suffices for these uses; this verdict does not establish unrelated hypotheses in those arguments.

## E-x2-2 — FALSE

At corrected.tex:1558–1564 the second equality asserts that the cluster is the graph closure of the positive odometer set. Take any 0 < t ≤ ε. The initial mass M = t/ε is in (0,1], so the initial configuration is already stable: no vertex topples, the odometer is identically zero, and the final positive-mass set is {0}. The closure of the positive odometer set is empty. This is a counterexample on every graph, independent of the random environment. The same issue affects the displayed identity at 1703–1705 and 2947–2951.

A proposed replacement for the cluster identity, for M > 0, is Dε(M) = {0} ∪ cl{v > 0}. Every toppled vertex retains positive mass and each neighbor receives positive mass; conversely each positive-mass vertex other than the source must have received mass from a toppled neighbor. For M > 1, the source topples, so it is already in the positive odometer set. Consequently the unmodified identity is valid in the fixed-t, ε → 0 applications once ε < t; this observation does not justify the displayed claim for all t and ε, nor the separate equality of stopped and unstopped odometers. These identities are formalized as `Sandpile.cluster_eq_insert_closure` and the counterexample as `Sandpile.cluster_of_mass_le_one`.

## E-c1-1 — FALSE

The last clause of Lemma 4.4 and the mass identity of Lemma 4.5 quantify over every t, ε > 0 (corrected.tex:1707–1723). Fix a realization with μh(Bρ) finite and η parametrized by μh area, and choose ε > μh(Bρ). The cell η([-ε,0]) contains 0 and has μh-mass ε, so it cannot be contained in Bρ; by continuity it meets ∂Bρ. Thus the source vertex 0 is outside the killed domain V = Vε(Bρ) \ Vε(∂Bρ). The killed Green function with source 0 is zero. The zero function is the least admissible supersolution for the resulting zero obstacle, and the discrete cluster and Laplacian are zero. Taking t = 2ε gives t/ε > 1 but 0 is not in the cluster; the mass sum is 0 rather than 2, even though the empty cluster satisfies the stated containment hypothesis. These realizations have probability one under the standing area parametrization and local finiteness assumptions.

A candidate correction is to require 0 ∈ V for these two conclusions. Continuity of η at 0 gives this for every sufficiently small ε, so the fixed-t small-mesh uses are compatible with the additional hypothesis. This candidate does not resolve the separate connectedness issue in Appendix A.
