# Proof repairs G1–G4

These repairs refer to `paper/idla_mated_crt-corrected.tex` and use the
N3 deterministic preparation and zero-boundary compactness in the audit.
They do not assert that unrelated dependencies of the paper have been proved.

## G1 — Lemma 3.7, Step 2: REPAIRED

Work on the prepared probability-one event for a fixed deterministic ball
D = B_r(z) and rational pole x. In addition prepare weak convergence of
λ_ε = ε Σ_b δ_{η(b)} to μ_h on compact subsets of an ambient ball containing
D, and the vanishing maximal diameter of cells meeting that ball. The former
follows from Lemma 2.9 applied to each member of a countable dense family of
nonnegative compactly supported Lipschitz functions, plus local boundedness of
mass; finite deterministic thinning gives simultaneous almost-sure convergence.
Choose in advance a countable dense set of positive cutoff radii δ with
B_δ(x) compactly contained in D and μ_h(∂B_δ(x)) = 0 almost surely. Such a set
exists: for every realization, a locally finite measure charges at most
countably many concentric circles, so Fubini gives a full-Lebesgue-measure set
of deterministic radii with this property. Do this for every rational x.
Use these cutoffs in the countable extraction in place of all rational radii.

Write v_ε(b) = m_ε⁻¹ ε⁻¹ gr_D^ε(a_x^ε,b). Lemma 3.3, including its
boundary conclusion, yields uniformly on D̄ \ B_δ(x)

    v_ε(b) → (c₀/6) G_D(x,η(b)),

where evaluation at representatives and boundary vertices uses the vanishing
cell diameters; values of killed vertices are zero. More precisely, this
uniform estimate applies to all cells meeting any fixed closed set away from x,
after a harmless enlargement, because their representatives and their points
are o(1) apart. The normalized truncated sum is exactly ε times the sum of
v_ε(b) over interior vertices whose cells do not meet B_δ(x). The indicators
of this set differ from 1_{D \ B_δ(x)}(η(b)) only in o(1)-neighborhoods of
∂B_δ(x) and ∂D. On the inner layer weak convergence and the zero circle mass
make the contribution vanish. At the outer layer the limiting Green function
vanishes continuously, so its contribution is bounded by its small supremum
there times a uniformly bounded local mass; no assumption on μ_h(∂D) is
needed. Local weak convergence, continuity of G_D(x,·) off x, and a continuous
cutoff approximation therefore imply

    q̄^{*,δ−}_D(x) = (c₀/6) ∫_{D \ B_δ(x)} G_D(x,y) dμ_h(y).

The limit function and the cutoff, rather than the discontinuous cell
interpolation, are the test functions. This does not use the boundary estimate
on an annulus or a random-mesh probability estimate. Cutoffs in the prepared
set can tend to zero, which is all Step 3 needs.

## G2 — Lemma 3.7, Step 3: REPAIRED

For each prepared cutoff δ choose a deterministic smooth φ_δ with values in
[0,1], equal to 1 on B_{3δ/2}(x), and supported in B_{2δ}(x); restrict to
sufficiently small δ. Include these countably many Dirichlet problems in the
deterministic preparation. For sufficiently small ε every cell meeting
B_δ(x) has its representative in the plateau. Let f_δ^ε be the zero-boundary
solution of Δ^ε f_δ^ε = φ_δ(η(·)). Then f_δ^ε ≤ 0 and the finite graph
maximum principle, using deg ≥ 1, gives

    0 ≤ q_D^{ε,δ+} ≤ −f_δ^ε.

Indeed Δ^ε(q_D^{ε,δ+}+f_δ^ε) = φ_δ − 1_A/deg ≥ 0,
where A is the set of interior cells meeting B_δ(x), and the sum is zero on
the boundary. The interpolation preserves the comparison up to the standard
boundary-cell convention. By Lemma 3.5 and ΔG_D = −δ, the normalized f_δ^ε
converges uniformly to

    F_δ(v) = −c₀ ∫_D G_D(v,y) φ_δ(y) dμ_h(y).

The N3 spatial mass bound μ_h(B_s(v)) ≤ C s^b, uniformly for centers in
an ambient disk and small s, and the disk Green bound
G_D(v,y) ≤ C_D(1+log⁺(1/|v−y|)) give

    ‖F_δ‖∞ ≤ C' δ^b (1+|log δ|) → 0.

For the last estimate, if |v−x| ≤ 4δ cover B_{2δ}(x) by B_{6δ}(v)
and sum dyadic annuli around v; otherwise bound the logarithm on the support
and use its mass. Thus the comparison yields the required uniform absolute
bound on every extracted q̄^{*,δ+}. Together with G1 and monotone convergence
as δ ↓ 0, this identifies the total limit at every rational pole; continuity
and density identify it everywhere. The statement remains unchanged.

## G3 — Lemma 4.8, Steps 2–3: REPAIRED

Let u_ε = w_t^ε/m_ε and u its uniform cluster limit, and work on the
countably prepared event. On each rational ball D compactly contained in
B_ρ, choose a rational polynomial p with ‖p−u‖_{D̄}<δ/4, with δ positive
and rational. Take the discrete harmonic comparison with boundary data
m_ε(p+δ), rather than m_ε p+δ. Uniform convergence of u_ε to u and shrinking
boundary cells imply u_ε ≤ p+δ on the discrete boundary for small ε. The
discrete maximum principle and Lemma 3.5 give u ≤ H_D(p+δ), where H_D denotes
ordinary harmonic extension. Letting δ ↓ 0 gives u ≤ H_D(u|∂D). These rational
balls suffice for subharmonicity: approximate an arbitrary compactly contained
ball in center and radius and use continuity and continuity of circular means.

For the reverse comparison, use m_ε(p−δ): if a discrete function v_ε is
superharmonic on D and its normalized interpolation converges uniformly to v,
the minimum principle yields v ≥ H_D(p−δ), hence v ≥ H_D(v|∂D). The same
proof gives harmonicity when v_ε is harmonic. Rational polynomials and rational
constant shifts form a countable prepared family, so choosing p after seeing v
is legitimate. It is equally valid to approximate the normalized sum
(w_t^ε+q_D^ε)/m_ε by p when applying this argument in Step 3.

The inequality Δ^ε(w_t^ε+q_D^ε) ≤ 0 then yields Δu ≤ (c₀/6)μ_h by
Lemma 3.7. For equality on the open set {u > −t(c₀/6)G_{B_ρ}(0,·)}, take
rational balls with closures contained in that set and away from 0. Uniform
convergence of the Green function and odometer gives a strictly positive
margin on each closed ball, so the discrete equality holds there eventually.
Both comparisons make u+q_D harmonic there. Such balls cover the noncontact
set away from 0; equality extends across 0 because both sides are locally
finite measures and μ_h({0}) = 0, while Δu is nonnegative by Step 2 and is
bounded above by (c₀/6)μ_h. No statement change is needed for this step.

## G4 — Continuum equations, normalization, and killing: REPAIRED

Set k=c₀/6 throughout, with ΔG_D(x,·)=−δ_x. Make the following proof
replacements; all referenced statement constants already have these values.

1. **Lemma 3.4 and the exit functional (lines 1101–1182).** Let I_ε be the
   interior vertex set V^ε(D) \ V^ε(∂D), and let τ_ε be the first exit from
   I_ε. Kill the walk at τ_ε, rather than retaining its terminal value in an
   infinite occupation integral. For fixed T the discrete occupation is
   m_ε⁻¹ Σ_{0≤j<τ_ε, j/m_ε<T} f(η(X_j)); extend f bounded continuously to
   the ambient ball for evaluating interpolated paths. The limiting functional
   is ∫_0^{T∧τ_D} f(X_s) ds. A continuous path's exit time from a disk is
   continuous under local uniform convergence when it exits in finite time
   and visits the exterior immediately after exit. The LBM path has this
   property: its strictly increasing continuous clock preserves the usual
   Brownian immediate crossing of a smooth circle. Vanishing cell diameters
   sandwich the discrete exit between exits from disks of radii r−o(1) and
   r+o(1), giving the same convergence. Boundary-cell discrepancies and the
   linear interpolation cost vanish for fixed T. Thus the quenched invariance
   principle and bounded convergence give the killed finite-time limit in
   probability, also for bounded environment-measurable Hölder f by the
   stated joint/quenched formulation.

   The N3 prepared exit-time moment estimate gives, on events of probability
   tending to one, E[(τ_ε/m_ε)² | h,η] ≤ C with finite random C. Consequently
   the conditional expected absolute tail after T is at most ‖f‖∞ C/T.
   Localizing C and sending T to infinity proves convergence of the full
   killed occupation. Its limit is c₀∫_D G_D(y,x)f(x)dμ_h(x), by the
   Liouville clock and the Brownian occupation kernel 2G_D. This also repairs
   the corresponding exit-location argument in Lemma 3.6, using the same
   path crossing and cell diameter sandwich. Do not integrate a stopped path
   after its exit.

2. **Lemmas 3.3 and 3.5 (lines 1219–1222 and 1339–1383).** Replace every
   m₀/6 in the proof of Lemma 3.3 by k. In Lemma 3.5 the zero-boundary
   forcing limit is −c₀∫_D G_D(v,y)ψ(y)dμ_h(y), satisfying Δf=c₀ψμ_h.
   The normalized expected-exit barrier Q̄_ε=Q_ε/m_ε converges to
   Q(v)=c₀∫_D G_D(v,y)dμ_h(y), satisfying ΔQ=−c₀μ_h and zero boundary
   values, not ΔQ=−1. This follows from the corrected killed occupation
   limit for ψ=1 and the N3 compactness. Alternatively, the N3 direct
   zero-boundary comparison already supplies the boundary compactness needed
   here. Apply the maximum principle to |f₂^ε| ≤ ‖ψ‖∞Q_ε, with all
   quantities normalized before passing to limits. Replace m₀ by c₀ in the
   forcing equation. Lemma 3.7 uses the barred interpolation and k as in G1–G2.

3. **Theorem 4.1 (lines 1924–1967).** Replace m₀/6 by k, 6/m₀ by 1/k,
   and retain t in every obstacle −tkG. A direct comparison also avoids the
   paper's unjustified passage from a noncontact set to its regularization.
   Let u be any cluster limit, w=w_t^{B_ρ}, and set v=u−kw. Lemma 4.8
   makes u/k admissible for the obstacle problem, so v≥0; both vanish on
   ∂B_ρ. Let O={v>0}. Since w≥−tG, O lies in the noncontact set of u;
   Lemma 4.8 gives Δu=kμ_h on O, while Δw≤μ_h by admissibility. Thus
   Δv≥0 distributionally on O. A continuous subharmonic function on each
   component of O, zero on its relative boundary and at ∂B_ρ, cannot have
   a positive maximum: for any a>0 the compact set {v≥a} lies in B_ρ, and
   the maximum principle on {v>a} gives a contradiction. Hence v=0.
   This proves u=kw, including the factor, without requiring μ_h-nullness
   of the difference between an open noncontact set and its regularization.
   The N3 all-cluster-limits criterion gives convergence on the prepared
   deterministic sequence, hence convergence in probability by the usual
   subsequence criterion.

These corrections do not change the numbered statements. They use the
N3-patched compactness and its moment preparation, in addition to the stated
literature inputs; they do not resolve independent gaps elsewhere.
