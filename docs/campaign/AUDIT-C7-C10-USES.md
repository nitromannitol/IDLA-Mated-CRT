# Audit of corrections C7–C10

Line references below are to the pre-edit corrected draft; labels are stable. The C9 stopped-cluster use in Proposition 5.1 remains open. This audit does not claim that unrelated gaps in the paper are resolved.

## C7: source in the killed domain

Put V = Vε(Bρ) \ Vε(∂Bρ). The final clause of Lemma 4.4 now assumes 0 ∈ V; Lemma 4.5 assumes this only for its mass identity. Since η(0)=0 and η is continuous, η([-ε,0]) ⊂ Bρ for all sufficiently small ε, so 0 ∈ V. The counterexample without it is E-c1-1 in GAPS-SEC2567A.md.

For the origin claim, the appendix proof of Lemma A.3, Step 4 (3531–3540), applies with t_general = t/(ε deg(0)) and r(0)=1/deg(0): if the cluster is empty then t/ε ≤ 1; its Step 3 shows a nonempty cluster contains 0. For the identity, Lemma A.4 (3544–3580) takes v=w−φ, sums Δv deg over V using discrete Green's identity, and the interior containment makes the flux vanish. With Δφ = (t/ε)/deg(0) at 0 the sum is t/ε. For disconnected V, this uses the componentwise extension recorded in GAPS-SEC2567A.md E-c1-2; the printed appendix assumes connected V, which is not established for the cell domain. The first cardinality estimate and the other clauses are unchanged.

Uses: the explicit Lemma 4.4 calls at 1762, 1816, 1874, 1904 and 2110 use its Laplacian conclusions, unchanged; the section 7 display 2980 and Lemma 7.2 use the same Laplacian bounds. The source membership used in Section 7 holds for sufficiently small ε uniformly in t with t/ε > 1. The explicit Lemma 4.5 citation at 3101 uses finiteness and origin containment, not its mass identity; the identity has no other explicit citation. Fixed-t uses in Sections 4–7 can take ε < t and ε small enough for 0 ∈ V. These checks do not repair the separate Lemma 7.4 issue E-c3-1.

## C8: Lemma 7.2 above scale

Let ωG be the exponent in Lemma 2.16 and q=1/(2+γ)². Set β=½ min(q,ωG) and c₀=exp(−3C₁/2)/36, where C₁ is the constant in Lemma 2.16. Lemma 2.8 with ζ=q bounds cell diameters by ε^q. For ε sufficiently small and s ≥ ε^β, diameters are at most c₀s, ε^ωG ≤ s/4, and ε⁻¹ ≥ (16c₀)⁻¹, uniformly over s.

If the counted set K is empty the bound is immediate. Otherwise choose a∈K and compare the stopped odometer with the sum of killed Green kernels for b∈K in the ball centred at η(a) of radius s/4. The cell diameter bound places all these cells in its interior, and Lemma 2.16 gives each Green kernel at (a,b) at least 1/2. Off Θ, the maximum principle bounds the nonnegative stopped odometer by sup∂Θ u; another maximum-principle comparison of u plus the Green sum bounds that sum by the same quantity. Hence |K| ≤ 2 sup∂Θ u. This supplies the centred-ball and boundary details omitted from the printed proof; the deterministic argument is `ncard_cellVertices_inter_cluster_le` (MatedCRT/Proofs/Sec7/MassBoundOdometer/Count.lean:111), and the scale and probability assembly is `massBoundOdometerAboveScale_of_steps` (MatedCRT/Steps/Sec7/MassBoundOdometer.lean:64), conditional on the listed map, adjacent-cell and stopped-Laplacian inputs.

The only use is Proposition 7.1, Step 1 (3167–3192). Decrease its ω from Lemma 6.8 so that 0 < ω < β; shrinking ω only raises that lemma's minimum radius. Choose 0 < ω₀ < ω as already required. The application has s=r_k/4 and r_k ≥ 40 c₀⁻¹ ε^ω₀, hence s ≥ 10 c₀⁻¹ ε^ω₀ ≥ ε^β for ε<1. The displayed universal intermediate estimate is restricted accordingly. This verifies the scale only; shell geometry, rate and other independent iteration gaps are not established here.

## C9: cluster identities and consistency

For mass M=t/ε>1 the source topples. Every toppled vertex retains positive mass, and each neighbor receives positive mass; conversely a positive-mass vertex other than the source must receive mass from a toppled neighbor. Thus Dε(M)=cl{vε_t>0}. For 0<M≤1, no vertex topples and Dε(M)={0}; the general identity is Dε(M)={0}∪cl{vε_t>0}. This is formalized in `Sandpile.cluster_eq_insert_closure`.

All named uses have fixed t>0 and ε→0, so ε<t eventually: the use at 1679, the display 1703–1705 and its use at 2042, and the display 2947–2951 with its use at 3267. None needs t≤ε. However, Λε_t is the positive set of the **stopped** odometer; the global identity alone does not prove Dε=cl Λε_t. The two displays now state the additionally necessary stopped/unstopped consistency condition. The original pre-edit displays omitted it. A finite path graph with a sink at the boundary and M>1 illustrates the distinction: for large enough M, mass crosses the sink in the global sandpile while the stopped odometer is zero there.

At 3267 consistency is invoked after the intended stopped-cluster confinement via (7.3), so this use is conditional on that confinement argument. At 2042, Proposition 5.1 uses the equality before the upper-bound proof establishes consistency; t<T is a continuum stopping condition, not by itself a proof of discrete consistency. This use is **not established** by C9. The implication needed there is the lower inclusion for the stopped cluster; it could follow from a separate direct stopped-odometer lower-bound argument, but none is supplied by the printed global cluster identity. This is a separate obstruction from the ε<t correction and is not silently assumed solved.

## C10: scaled boundary modulus

Replace C' by C'ε⁻¹ in (3.1). For ε<1 this includes the printed hypothesis. On a sequence of scales where Lemma 3.2 and the cell-size estimate eventually hold, put vε=εuε. Then vε is harmonic, |vε|≤C, and its boundary modulus is ≤C'(ε∨|η(a)−η(b)|)^χ. Lemma 3.2 yields a uniform modulus with exponent ξ′. Since εmε is bounded below, the same holds up to a constant for mε⁻¹uε; vanishing cell diameters, boundedness and a finite-net diagonal give a uniformly convergent subsequence on the closure. Integer localization handles random bounds. The interior proof is unchanged. This is conditional on the good-scale sequence: N3 remains open for a prescribed random sequence, and the independent non-open-domain issue in CORRECTED-FORMS.md remains.

Uses: Lemma 3.3 (1197), Lemma 3.7 (1427) and Lemma 4.6 (1762) use interior compactness; C10 adds no restriction. Lemma 3.5 (1353) uses boundary data mεφ; εmε is uniformly bounded and φ is Hölder, giving the revised modulus. Lemma 4.8 uses Lemma 3.5 for Hölder data, including φδ+δ and polynomials, so the same calculation applies. Lemma 3.7's later use of 3.5 has zero boundary data. These are the N1 checks from GAPS-SEC3.md; they do not settle N2 or N3.
