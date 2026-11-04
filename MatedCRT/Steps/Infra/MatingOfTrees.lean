import MatedCRT.Defs.Setting

/-!
# Steps: the map of Definition 1.1 and the cells of the SLE/LQG embedding

After the graph switch (operator decision (L1), inbox 2026-11-03 16:20 UTC) the edges of the map are those of
Definition 1.1 (`MatedCRTEnv.mult`, the boundary-length pair `bm`), while the embedding uses the cells
`η([a - ε, a])` of Definition 1.2. Proofs which used that adjacent cells of `cellMult` meet need the same fact for the
map of Definition 1.1; it holds almost surely under the mating-of-trees coupling of `MatedCRTEnv.IsValid` (Leo's
`MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling`, Lattice-Probability module
`LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling`, adapted from Leonardo Bonanno's
lean-formalizations).

* `AdjacentCellsMeetAeStep`: a.s., vertices joined by an edge of `𝒢^ε` have intersecting cells.
-/

namespace MatedCRT

open MeasureTheory Set

/-- **Step: adjacent vertices have intersecting cells.** Almost surely, for every `ε > 0`, two vertices joined by an
edge of the map of Definition 1.1 have intersecting cells `η([a - ε, a])`, `η([b - ε, b])`. Source: DMS14 Lemma 8.8
(a direct `L`- or `R`-identification of times `s < t` gives `η(s) = η(t)`), the bundle field `merge`, together with
the path properties of the correlated Brownian motion `bm` (bundle field `boundaryLawBM`); equivalently, a consequence
of the a.s. equality of Definitions 1.1 and 1.2 (DMS14 Theorem 1.9, line 207). Leo proves it from his bundle
(MatedCRTHarmonic MoTInput/CellAdjacency, "adjacent cells intersect"); the port to Lattice-Probability is pending
(lp435 fleet), after which this step is proved, not assumed. Used for: local finiteness of `𝒢^ε`,
`cl(V^ε(B_ρ) \ V^ε(∂B_ρ)) ⊆ V^ε(cl B_ρ)` (Section 4), the crossing lemma for cells (Section 6). The local
high-probability form `AdjacentCellsMeetStep` of Lemma 6.10 (MatedCRT/Steps/Sec6/IterativeBound.lean) follows from it. -/
def AdjacentCellsMeetAeStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ∀ ε : ℝ, 0 < ε → ∀ j k : ℤ, S.mult ε ω j k ≠ 0 →
      (cell ε (S.η ω) j ∩ cell ε (S.η ω) k).Nonempty

end MatedCRT
