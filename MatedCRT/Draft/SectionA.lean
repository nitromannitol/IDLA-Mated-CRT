import MatedCRT.Defs.Sandpile

/-!
# Appendix A: statements of Lemmas A.1-A.4 (lines 3338-3556)

The discrete obstacle problem on a general graph: `G` undirected (symmetric edge multiplicity `m`, no loops), locally
finite and infinite; `V` a finite connected vertex set containing the origin `o`; a threshold `𝔯 > 0` on `V`; an
obstacle `φ ≤ 0` on `cl(V)` with `Δφ = 𝔱 δ_o` on `V`, `φ = 0` on `∂V`, `𝔱 > 0` (`IsObstacleSetting`,
MatedCRT/Defs/Sandpile.lean). The paper's graph is simple; the statements are for multigraphs (edge multiplicities),
which is how they are applied to the mated-CRT map in Section 4 (ESCALATIONS E-A2). Then
* `w = min {u : cl(V) → ℝ : Δu ≤ 𝔯 on V, u ≥ φ}` (eq:discrete-least-supersolution-general) is
  `discreteLeastSupersolution m V (vClosure m V) 𝔯 φ`;
* `𝔮` is the unique solution of `Δ𝔮 = 𝔯` on `V`, `𝔮 = 0` on `∂V` (eq:definition-of-exit-time-general): the statements
  quantify over any such function;
* `Λ = {a ∈ cl(V) : w(a) > φ(a)}` (eq:discrete-cluster-general) is `discreteCluster (vClosure m V) w φ`.
These results do not involve the mated-CRT map and take no SLE model.
-/

namespace MatedCRT

open Set

/-- **Lemma A.1** (lemma:discrete-divergence-theorem, line 3347). On an undirected locally finite graph, for
`f, g : VG → ℝ` vanishing outside a finite set, `∑_a f(a) Δg(a) deg(a) = ∑_a g(a) Δf(a) deg(a)`. -/
def DiscreteDivergenceTheoremStmt : Prop :=
  ∀ (α : Type) (m : α → α → ℕ), (∀ a b, m a b = m b a) → (∀ a, {b | m a b ≠ 0}.Finite) →
  ∀ f g : α → ℝ, (Function.support f).Finite → (Function.support g).Finite →
    ∑ᶠ a, f a * mLaplacian m g a * (mdeg m a : ℝ) = ∑ᶠ a, g a * mLaplacian m f a * (mdeg m a : ℝ)

/-- **Lemma A.2** (lemma:discrete-basic-properties-general, line 3413). In the setting of Appendix A,
`max(𝔮, φ) ≤ w ≤ 0` (on `cl(V)`) and `Δw ≤ 𝔯` on `V`. -/
def DiscreteBasicPropertiesGeneralStmt : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
  ∀ 𝔮 : α → ℝ, (∀ a ∈ V, mLaplacian m 𝔮 a = 𝔯 a) → (∀ a ∈ vBoundary m V, 𝔮 a = 0) →
    (∀ a ∈ vClosure m V, max (𝔮 a) (φ a) ≤ discreteLeastSupersolution m V (vClosure m V) 𝔯 φ a ∧
      discreteLeastSupersolution m V (vClosure m V) 𝔯 φ a ≤ 0) ∧
    ∀ a ∈ V, mLaplacian m (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) a ≤ 𝔯 a

/-- **Lemma A.3** (lemma:discrete-laplacian-bound-general, line 3448). In the setting of Appendix A, `Δw = 𝔯` on `Λ` and
`𝔯 ≥ Δw ≥ 0` on `V`. Moreover `Λ` is connected and, if `𝔱 > 𝔯(o)`, contains the origin. Connected is
`IsVPreconnected` (the empty set is connected): for `𝔱 ≤ 𝔯(o)` the obstacle `φ` is itself admissible, `w = φ` and
`Λ = ∅`. -/
def DiscreteLaplacianBoundGeneralStmt : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    (∀ a ∈ discreteCluster (vClosure m V) (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) φ,
      mLaplacian m (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) a = 𝔯 a) ∧
    (∀ a ∈ V, 0 ≤ mLaplacian m (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) a ∧
      mLaplacian m (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) a ≤ 𝔯 a) ∧
    IsVPreconnected m (discreteCluster (vClosure m V) (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) φ) ∧
    (𝔯 o < 𝔱 → o ∈ discreteCluster (vClosure m V) (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) φ)

/-- **Lemma A.4** (lemma:discrete-conservation-of-mass-general, line 3528). In the setting of Appendix A with
`𝔯 = deg⁻¹`: `|Λ| ≤ 𝔱 deg(o)`; moreover, if `Λ ⊆ int(V)`, then `∑_{a ∈ V} Δw(a) deg(a) = 𝔱 deg(o)`. -/
def DiscreteConservationOfMassGeneralStmt : Prop :=
  ∀ (α : Type) (m : α → α → ℕ) (V : Set α) (o : α) (𝔯 φ : α → ℝ) (𝔱 : ℝ), IsObstacleSetting m V o 𝔯 φ 𝔱 →
    (∀ a ∈ V, 𝔯 a = ((mdeg m a : ℕ) : ℝ)⁻¹) →
    ((discreteCluster (vClosure m V) (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) φ).ncard : ℝ) ≤
        𝔱 * (mdeg m o : ℝ) ∧
    (discreteCluster (vClosure m V) (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) φ ⊆ vInterior m V →
      ∑ᶠ a ∈ V, mLaplacian m (discreteLeastSupersolution m V (vClosure m V) 𝔯 φ) a * (mdeg m a : ℝ) =
        𝔱 * (mdeg m o : ℝ))

end MatedCRT
