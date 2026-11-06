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
