import MatedCRT.Defs.Notation
import HarmonicBalls.Defs.Geometry
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The mated-CRT map (Definitions 1.1 and 1.2, lines 169-205; Section 2.5, lines 625-653)

## Multigraphs and their potential theory

A multigraph on a vertex type `V` is given by its *edge multiplicity* `m : V → V → ℕ` (`m a b` = number of edges
joining `a` and `b`; symmetric, zero on the diagonal). The mated-CRT map is a multigraph: two vertices can be joined
by two edges (Definition 1.1, line 177). Its *degree* is the number of incident edges, `deg a = ∑_b m a b`, and its
*degree normalized Laplacian* is the generator of the simple random walk which jumps along a uniformly chosen incident
edge:
`Δ u(a) = deg(a)⁻¹ ∑_b m(a,b) (u(b) - u(a))` (eq:degree-normalized-laplacian, line 776).
The printed formula sums over the sites `b ∼ a` joined to `a` by an edge, each once; with the edges counted with
multiplicity, as here, `Δ` is the generator of the simple random walk, which is how the paper uses it
(lines 784-785; ESCALATIONS, entry "multigraph Laplacian"). For a simple graph (`m ∈ {0, 1}`) both readings agree,
and this is the graph Laplacian of Appendix A (line 3341).

For `A ⊆ V`: `∂A` = vertices outside `A` joined by an edge to `A`, `cl(A) = A ∪ ∂A`, `int(A)` = vertices of `A` with
no edge to `Aᶜ` (Section 1.5, lines 375-377). Connectedness of `A` is connectedness of the induced subgraph.

## The Brownian motion description (Definition 1.1)

Vertices `a ∈ εℤ` are written `a = ε k` with `k ∈ ℤ`. For a real path `X` and `j < k`, the adjacency condition
(eq:edge-map, line 175) is
`(inf_{[εj-ε, εj]} X) ∨ (inf_{[εk-ε, εk]} X) ≤ inf_{[εj, εk-ε]} X`.

## The SLE/LQG embedding (Definition 1.2)

The vertex `a = εk` corresponds to the *cell* `H^ε_a = η([a - ε, a])` (eq:sle-cell, line 200) of a space-filling curve
`η : ℝ → ℂ`, and two distinct vertices are joined by as many edges as `H^ε_a ∩ H^ε_b` has connected components which
are not singletons (line 202). For `x ∈ ℂ`, `a^ε_x` is the smallest vertex whose cell contains `x`
(eq:plane-to-embedding, line 637); `V^ε(D)` is the set of vertices whose cells meet `D`
(eq:cells-domain-restriction, line 641); a vertex set `A` is mapped to the union `Ā` of its cells
(eq:vertex-scaling, line 248).
-/

namespace MatedCRT

open MeasureTheory Set
open scoped ENNReal NNReal

section Multigraph

variable {V : Type*}

/-- The *degree* `deg(a) = ∑_b m(a,b)` of a vertex of the multigraph with edge multiplicity `m`: the number of edges
incident to `a` (line 635). It is `0` (junk) if `a` has infinitely many neighbours. -/
noncomputable def mdeg (m : V → V → ℕ) (a : V) : ℕ :=
  ∑ᶠ b, m a b

/-- The *degree normalized Laplacian* `Δu(a) = deg(a)⁻¹ ∑_b m(a,b) (u(b) - u(a))`
(eq:degree-normalized-laplacian, line 776; Appendix A, line 3341), the generator of simple random walk. -/
noncomputable def mLaplacian (m : V → V → ℕ) (u : V → ℝ) (a : V) : ℝ :=
  ((mdeg m a : ℕ) : ℝ)⁻¹ * ∑ᶠ b, (m a b : ℝ) * (u b - u a)

/-- The *boundary* `∂A`: the vertices outside `A` joined by an edge to a vertex of `A` (line 375). -/
def vBoundary (m : V → V → ℕ) (A : Set V) : Set V :=
  {b | b ∉ A ∧ ∃ a ∈ A, m a b ≠ 0}

/-- The *closure* `cl(A) = A ∪ ∂A` (line 376). -/
def vClosure (m : V → V → ℕ) (A : Set V) : Set V :=
  A ∪ vBoundary m A

/-- The *interior* `int(A)`: the vertices of `A` which do not share an edge with a vertex of `Aᶜ` (line 377). -/
def vInterior (m : V → V → ℕ) (A : Set V) : Set V :=
  {a ∈ A | ∀ b, m a b ≠ 0 → b ∈ A}

/-- The simple graph underlying the multigraph: `a ≠ b` are adjacent iff they are joined by at least one edge. -/
def adjGraph (m : V → V → ℕ) : SimpleGraph V :=
  SimpleGraph.fromRel fun a b => m a b ≠ 0

/-- `A` is *connected*: the subgraph induced by `A` is connected (in particular `A` is nonempty). -/
def IsVConnected (m : V → V → ℕ) (A : Set V) : Prop :=
  ((adjGraph m).induce A).Connected

/-- `u` is *subharmonic* on `A`: `Δu ≥ 0` on `A` (line 818). -/
def IsSubharmonicOn (m : V → V → ℕ) (u : V → ℝ) (A : Set V) : Prop :=
  ∀ a ∈ A, 0 ≤ mLaplacian m u a

/-- `u` is *superharmonic* on `A`: `Δu ≤ 0` on `A` (line 819). -/
def IsSuperharmonicOn (m : V → V → ℕ) (u : V → ℝ) (A : Set V) : Prop :=
  ∀ a ∈ A, mLaplacian m u a ≤ 0

/-- `u` is *harmonic* on `A`: `Δu = 0` on `A` (line 819). -/
def IsHarmonicOn (m : V → V → ℕ) (u : V → ℝ) (A : Set V) : Prop :=
  ∀ a ∈ A, mLaplacian m u a = 0

/-- A *path* `a = a₀ ∼ a₁ ∼ ⋯ ∼ a_n = b` in `A`: a list of consecutive vertices of `A`, each joined to the next by an
edge, starting at `a` and ending at `b` (Lemma 7.4, line 3060). -/
def IsVPathIn (m : V → V → ℕ) (A : Set V) (p : List V) (a b : V) : Prop :=
  p.head? = some a ∧ p.getLast? = some b ∧ (∀ c ∈ p, c ∈ A) ∧ p.IsChain fun c d => m c d ≠ 0

end Multigraph

/-! ## Definition 1.1: the Brownian motion description -/

/-- The adjacency condition (eq:edge-map, line 175) for the vertices `a = εj < b = εk` and the real path `X`:
`(inf_{[a-ε,a]} X) ∨ (inf_{[b-ε,b]} X) ≤ inf_{[a,b-ε]} X`. -/
def bmAdjacent (ε : ℝ) (X : ℝ → ℝ) (j k : ℤ) : Prop :=
  max (sInf (X '' Icc (ε * j - ε) (ε * j))) (sInf (X '' Icc (ε * k - ε) (ε * k))) ≤
    sInf (X '' Icc (ε * j) (ε * k - ε))

open Classical in
/-- The number of edges joining the vertices `εj` and `εk` of the `γ`-mated-CRT map with cell size `ε` associated to
the pair of paths `(L, R)` (Definition 1.1, lines 173-177): one edge if (eq:edge-map) holds for `X = L` or `X = R`,
and two edges if moreover `|k - j| > 1` (i.e. `|b - a| > ε`) and it holds for both. No loops. -/
noncomputable def bmEdgeCount (ε : ℝ) (L R : ℝ → ℝ) (j k : ℤ) : ℕ :=
  if j = k then 0
  else
    let lo := min j k
    let hi := max j k
    if bmAdjacent ε L lo hi ∨ bmAdjacent ε R lo hi then
      (if 1 < hi - lo ∧ bmAdjacent ε L lo hi ∧ bmAdjacent ε R lo hi then 2 else 1)
    else 0

/-- `(L_t, R_t)_{t ∈ ℝ}` is a *two-sided two-dimensional Brownian motion started at the origin with correlation
coefficient `ρ`* (Definition 1.1, line 170): the forward process `(L_t, R_t)_{t ≥ 0}` and the backward process
`(L_{-t}, R_{-t})_{t ≥ 0}` are independent, and each has the law of `(W¹, ρ W¹ + √(1-ρ²) W²)` with `W¹, W²`
independent standard Brownian motions started at `0` (MarkovProcess's `brownianMotion`). The laws are compared as
measures on pairs of paths `ℝ≥0 → ℝ` with the product σ-algebra (equality of all finite dimensional distributions).
The variances are normalized to `1`; the graph of Definition 1.1 does not depend on this normalization. -/
def IsCorrelatedTwoSidedBM {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ρ : ℝ) (L R : Ω → ℝ → ℝ) : Prop :=
  let ν : Measure ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) :=
    ((MarkovProcess.brownianMotion 0).prod (MarkovProcess.brownianMotion 0)).map
      fun w => (fun t => w.1 t, fun t => ρ * w.1 t + Real.sqrt (1 - ρ ^ 2) * w.2 t)
  P.map (fun ω => ((fun t : ℝ≥0 => L ω t, fun t : ℝ≥0 => R ω t),
      (fun t : ℝ≥0 => L ω (-(t : ℝ)), fun t : ℝ≥0 => R ω (-(t : ℝ))))) = ν.prod ν

/-- The correlation coefficient `-cos(πγ²/4)` of the Brownian motions of the `γ`-mated-CRT map (line 170). -/
noncomputable def matedCRTCorrelation (γ : ℝ) : ℝ :=
  -Real.cos (Real.pi * γ ^ 2 / 4)

/-! ## Definition 1.2: the SLE/LQG embedding -/

/-- The *cell* `H^ε_a = η([a - ε, a])` of the vertex `a = εk` (eq:sle-cell, line 200). -/
def cell (ε : ℝ) (η : ℝ → ℂ) (k : ℤ) : Set ℂ :=
  η '' Icc (ε * (k - 1)) (ε * k)

/-- The number of edges joining the vertices `εj` and `εk` in the SLE/LQG embedding (Definition 1.2, line 202): for
`j ≠ k`, the number of connected components of `H^ε_{εj} ∩ H^ε_{εk}` which are not singletons (`Set.ncard`, junk `0`
if there are infinitely many); `0` for `j = k`. -/
noncomputable def cellMult (ε : ℝ) (η : ℝ → ℂ) (j k : ℤ) : ℕ :=
  open Classical in
  if j = k then 0
  else {C ∈ HarmonicBalls.connectedComponentsIn (cell ε η j ∩ cell ε η k) | ¬ C.Subsingleton}.ncard

/-- The degree `deg^ε(a)` of the vertex `a = εk` of the mated-CRT map `𝒢^ε` (line 635). -/
noncomputable def matedDeg (ε : ℝ) (η : ℝ → ℂ) (k : ℤ) : ℕ :=
  mdeg (cellMult ε η) k

/-- The degree normalized Laplacian `Δ^ε` of the mated-CRT map (eq:degree-normalized-laplacian, line 776). -/
noncomputable def matedLaplacian (ε : ℝ) (η : ℝ → ℂ) (u : ℤ → ℝ) (k : ℤ) : ℝ :=
  mLaplacian (cellMult ε η) u k

/-- The embedded position `η(a)` of the vertex `a = εk` (Definition 1.2, line 204). -/
def vertexPoint (ε : ℝ) (η : ℝ → ℂ) (k : ℤ) : ℂ :=
  η (ε * k)

/-- `a^ε_x`: the smallest vertex whose cell contains `x` (eq:plane-to-embedding, line 637), as an index `k`
(`a^ε_x = ε k`). Junk value `0` if no cell contains `x` or there is no smallest one. -/
noncomputable def vertexOf (ε : ℝ) (η : ℝ → ℂ) (x : ℂ) : ℤ :=
  sInf {k : ℤ | x ∈ cell ε η k}

/-- `V^ε(D)`: the vertices whose cells meet `D`, the vertex set of the induced subgraph `𝒢^ε(D)`
(eq:cells-domain-restriction, line 641). -/
def cellVertices (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) : Set ℤ :=
  {k | (cell ε η k ∩ D).Nonempty}

/-- `V^ε(D) \ V^ε(∂D)`: the vertices whose cells meet `D` but not its boundary (line 645). -/
def interiorCellVertices (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) : Set ℤ :=
  cellVertices ε η D \ cellVertices ε η (frontier D)

/-- `Ā = ⋃_{a ∈ A} H^ε_a`: the union of the cells of the vertices of `A` (eq:vertex-scaling, line 248). -/
def fillCells (ε : ℝ) (η : ℝ → ℂ) (A : Set ℤ) : Set ℂ :=
  ⋃ k ∈ A, cell ε η k

/-- The *rescaled* function `ū^ε(x) = m_ε⁻¹ u^ε(a^ε_x)`, constant on cells (eq:discrete-scaling, line 961), for a
scaling factor `mε` (the median exit time `m_ε` of eq:meps). -/
noncomputable def rescale (mε ε : ℝ) (η : ℝ → ℂ) (u : ℤ → ℝ) (x : ℂ) : ℝ :=
  mε⁻¹ * u (vertexOf ε η x)

end MatedCRT
