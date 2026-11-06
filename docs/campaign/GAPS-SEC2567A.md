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

## E-x1-1 — MINIMAL-CORRECTION to the boundary argument

At corrected.tex:2117–2124 replace the assertion that the ambient Green function and w̃ vanish individually on ∂Λεt by: “w̃ + (t/ε) ḡBρ(·,0) vanishes on ∂Λεt by obstacle contact, while ḡΛεt and q̄Λεt vanish there by killing.” No change to the lemma statement is proposed by this item.

Proof: the obstacle is φ = −(t/ε)ḡBρ(·,0), and the least supersolution w̃ satisfies w̃ ≥ φ. On vertices of the obstacle domain outside Λεt, the definition of Λεt excludes strict inequality, so w̃ = φ. On its exterior boundary both terms vanish under the obstacle boundary conditions, and outside the closure both are zero. Therefore v = w̃ − φ vanishes at every vertex outside the cluster, including ∂Λεt. The killed Green function and exit-time function defining ṽ vanish outside Λεt, so v − ṽ has zero boundary values. The displayed calculation in 2110–2116 gives Δ(v − ṽ) = 0 in the cluster. The finite-graph maximum principle applied to both signs gives v = ṽ there, hence the weaker comparison used at 2124. This contact calculation is checked in `mated_surplus_zero_off_cluster` (Proofs/Sec5/MeanValueInequality/BoundaryContact.lean:45).

Downstream, the comparison is used in the immediately following surplus estimate and nowhere else as a separate result. The correction supplies that comparison but does not prove the subsequent uniform positive surplus at 2128–2134, which is the independent E-c2-5/E-x3-1 issue.

## E-c2-2 — FINE-AS-PRINTED, with the omitted counting argument

At corrected.tex:2168–2171 the random constant C may be chosen as μh(BR), for fixed ρ < R < 1. By Lemma 2.8 (:669–675), with polynomially high probability every ε-cell meeting Bρ has diameter less than R−ρ and is therefore contained in BR. The area parametrization gives mass ε to each cell and zero μh-mass to the intersection of two distinct cells. Hence for every finite subset F of Vε(Bρ),

    ε |F| = μh(⋃a∈F Hεa) ≤ μh(BR).

Local finiteness of μh makes μh(BR) finite almost surely. The same inequality for all finite F proves the vertex set finite and yields |Vε(Bρ)| ≤ μh(BR)/ε. The finite-subset inequality, including the zero-overlap argument, is formalized in `cellVerticesBallFiniteStep` (Proofs/Sec6/ConstantOrderLowerBound/Model.lean:112); local finiteness is also obtainable from the cited volume growth bound by covering a fixed compact ball with finitely many smaller balls.

For the only downstream use, the union bound in the proof of Lemma 5.2, this random coefficient is sufficient: on the good event, C ε⁻¹ exp(−c ε⁻q) tends to zero for every finite C and positive c, q, even if c and C are random and independent of ε. Add the probability of the complementary cell-size event and use convergence in probability. This supplies the count; it does not address the other hypotheses of Lemma 5.2.

## E-c2-4 — FALSE as a Lean step

`GoodScaleEventMeasurableStep` (Steps/Sec6/ConstantOrderLowerBoundDiv.lean:68) requires a pointwise σ(h)-measurable inner set F ⊆ E with P(Fᶜ) ≤ P*(Eᶜ), for the volume-growth event E. Form a product of a valid model with an independent uniform U on [0,1], retaining the original field and curve, and replace μ by zero on the null slice {U = 1/2}. The validity assumptions are unchanged because the replacement is on a measurable null set.

Choose 0 < δ < 1 and positive exponents. On the null slice E fails at z = 0, since its positive lower bound for μ(Bδ(0)) fails. Every σ(h)-measurable set on the product is a union of complete U-fibres. Any such set contained in E must therefore be empty, since each fibre meets the bad slice. But the original E has probability tending to one as δ ↓ 0 by Lemma 2.7; select δ with P*(Eᶜ) < 1. Then F = ∅ has P(Fᶜ) = 1, contradicting the required inequality. Thus the proposed pointwise inner approximation is false even though the change to μ is almost surely invisible.

The weaker condition P(F \ E) = 0 suffices for the countable Borel–Cantelli application, provided the needed field-measurable modification of μ exists. That modification is a separate remaining hypothesis; the counterexample does not refute the paper's probabilistic estimate.

## E-A8 — MINIMAL-CORRECTION to the remaining proof notation

The statements of Lemmas 5.3 and 5.4 and the definition of O₁ in Proposition 5.1 already use ∂Λ̄εt, with [C4] (corrected.tex:2011–2012, 2023–2024, 2032–2033). Four proof occurrences still use ∂η(Λεt), at 2062, 2067, 2095 and 2132. Proposed marked change: replace ∂η(Λεt) by ∂Λ̄εt at each of those four locations. This continues [C4]; it does not change either lemma's statement.

The distinction matters. By local finiteness Λεt is finite; η(Λεt) is therefore a finite planar point set, whose boundary is itself. For a ∈ Λεt, η(a) lies in that boundary and its distance from it is zero. Thus the original positive-distance condition selects no vertices and cannot furnish the interior covering used at 2034–2045. The overline instead denotes the union of the cells, by the definition at `eq:vertex-scaling`. Replacing the four proof predicates makes them exactly the predicates in the corrected lemma statements, and the O₁ predicate at the Proposition 5.1 application agrees with those statements after replacing δ by δ/4. A search for the literal old boundary expression finds no other live occurrences beyond the four just listed (the remaining matches are [C4] comments).

This resolves the notational mismatch only. It does not supply the substantive estimates of Lemmas 5.3 and 5.4 or the other steps of Proposition 5.1; in particular, the surplus and stopped-domain issues E-c2-5 and E-c1-5 remain independent.

## E-c5-2 — MINIMAL-CORRECTION to Definition 6.2 and Lemma 6.3

At corrected.tex:2290 and 2306, allow arbitrary starting vertices a₁,…,aₖ ∈ Vε in place of a₁,…,aₖ ∈ Θ. Interpret P as the list or multiset of stopped walkers, preserving multiplicity. In particular, a walker started outside Θ settles immediately if its site is available, or is stopped immediately if the site is outside Θ′. The original statement is a special case; the generalization is used because the first starts in Lemma 6.10 are in cl Θ and subsequent starts are on the exterior stopping boundary.

Proof of the stronger stopped/restarted identity, conditional on the environment: let F(A,L) be the law of the final unstopped aggregate from occupied A and the list L of starting sites. IDLA has F(A,L) = F(A,L′) when L′ is a permutation of L: for two walkers, condition on their independent first exit sites from A. If those sites differ, both are added; if they coincide at b, one is added at b and the other continues with the transition law of a fresh walk from b, by the strong Markov property. The resulting kernel is symmetric in the two first exit sites; integrate and use adjacent transpositions. This exchangeability is proved as `aggValue_perm` in `MatedCRT/Proofs/Sec6/AbelianIDLA/Exchange.lean`.

Now let A ⊆ Θ′ be the current occupied set, P the list of walkers already stopped outside Θ′, and L the list still to release. Induct on L. At the end, releasing P has law F(A,P). For the next walker, if its first unoccupied site b lies in Θ′, both the unstopped process and the stopped process add b, and the induction applies to A ∪ {b}. If b lies outside Θ′, it is appended to P. Since b ∉ A, a fresh walker started at b is absorbed immediately; permutation invariance permits moving it to the front of P followed by the remaining starts. The strong Markov property gives the correct conditional law for each fresh continuation. Thus completing the stopped process and restarting P has law F(A,P ++ L). Starting with A = Θ and P empty proves the claimed identity. This induction, including arbitrary lists and multiplicities, is formalized by `runValue_stopped` and `isAbelianIDLA` in `MatedCRT/Proofs/Sec6/AbelianIDLA/Statement.lean:29` and `:83`.

Downstream check: the initial starts and every restart in Lemma 6.10 are now covered, as is the restarted expression in Lemma 6.3 itself. The additional radius containment needed to apply Lemma 6.9 during iteration is handled by using parameter (1+ρ)/2 and choosing the total radial expansion below (1−ρ)/4; this does not assert that the separate rate and shell estimates are proved.

## E-c3-1 — MINIMAL-CORRECTION to Lemma 7.4

At corrected.tex:3077–3082 replace “a ∈ Dε(t/ε) \ {0}” and “path … in Dε(t/ε)” by “a ∈ Λεt \ {0}” and “path … in Λεt”. Here Λεt is the positive set of the stopped odometer uεt. This removes the unsupported first step from a boundary site of the unstopped cluster, where the displayed equality Δu = 1/deg need not hold. The corrected Lean statement is `CrudeUpperBoundStmt` (Draft/Section7.lean); the printed paper still has the larger domain.

Proof on the degree-bound event: for any a ∈ Λεt distinct from 0, Δu(a) = 1/deg(a), so a neighboring vertex b has u(b) ≥ u(a) + 1/deg(a) ≥ u(a) + log(ε⁻¹)⁻². In particular u(b) > 0, so b ∈ Λεt. Repeat. The discrete cluster is finite, and the strict increases rule out revisiting vertices; therefore the procedure must reach 0. The degree bound holds with polynomially high probability by the cited result used at corrected.tex:3090–3094. This argument is formalized by `crudeUpperBound_of_mapSteps` in Steps/Sec7/CrudeUpperBound.lean:47, using the finite-cluster and stopped-odometer Laplacian hypotheses explicitly.

Downstream, the sole invocation is Proposition 7.1 Step 3 at 3253–3263. Starting from any positive-odometer vertex outside Θτ₂, follow the increasing path toward 0 ∈ Θτ₂ until it first reaches the boundary of Θτ₂. The odometer there is at most the boundary maximum Oτ₂ ≤ ε⁻ω₀, so there are at most log(ε⁻¹)² ε⁻ω₀ increments. The cell diameter bound converts this to the needed Euclidean distance. If “boundary of the support” is taken to mean the exterior boundary, add one adjacent cell; this changes the bound by only one cell diameter. The other iteration estimates and the equality between stopped and unstopped odometers are separate issues and are not established by this repair.
