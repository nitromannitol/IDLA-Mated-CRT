import Mathlib

/-!
# Published inputs of steps2-r3 Section 6: GMS invariance principle, cell configurations (carrier layer)

Source: Gwynne, Miller and Sheffield, *An invariance principle for ergodic scale-free random environments*,
arXiv:1807.07515v3 (retained printed text; printed page numbers below). Locators used here:
* Definition 1.2, conditions 4 (mass transport, (1.2)-(1.3)) and the opening "a.s. all faces are compact", pp. 4-5;
* Definition 1.3 (ergodic modulo scaling), p. 6; equation (1.5) (finite expectation), p. 8;
* Definition 1.15 (cell configuration), p. 14; (1.14)-(1.16) and the metric (1.15), p. 15;
* Theorem 1.16, p. 15, hypotheses 1-3 (condition 3 = connectedness along lines).

This file stages the carriers and the hypotheses of Theorem 1.16 only. Its conclusion (the quenched continuous-time
walk, the planar Brownian limit with covariance `Σ`, recurrence and the harmonic limit (1.17)), and Theorem 3.10, are not
staged here; they need the walk and Brownian-law carriers listed in `reports/z5.md`.

Printed-source notes, recorded and not silently corrected:
* Definition 1.15, item 1: "the intersection of any two elements of `H` has zero Lebesgue measure" is read as
  "of any two distinct elements" (a cell has nonempty interior, so `H ∩ H = H` has positive area).
* Page 15, below (1.17): `φ₀(H) := ∫_H z dz` is printed without the factor `1/Area(H)`; the words "Euclidean center"
  indicate the average. Not encoded here; see the report.
* `B_r(0)` is taken to be the open Euclidean ball (`Metric.ball`); the paper does not state the convention on p. 15.
-/

namespace MatedCRT.StoppedPoleReconstruction

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- Raw data of a cell configuration on `ℂ` (GMS Definition 1.15, p. 14): a family of cells, an adjacency relation
on cells, and a conductance on adjacent pairs. The axioms of Definition 1.15 are `IsCellConfiguration`. -/
structure CellData where
  /-- The cells `H`. -/
  cells : Set (Set ℂ)
  /-- The adjacency relation `∼`. -/
  adj : Set ℂ → Set ℂ → Prop
  /-- The conductance `𝔠(H, H')` on adjacent pairs. -/
  cond : Set ℂ → Set ℂ → ℝ

/-- Definition 1.15 (GMS p. 14) on `D = ℂ`: (1) a locally finite collection of compact connected cells with nonempty
interiors whose union is `ℂ`, with pairwise (distinct) cells meeting in a set of zero Lebesgue measure; (2) a symmetric
adjacency relation on cells, such that adjacent cells are distinct and intersect; (3) a conductance on adjacent pairs
with values in `(0, ∞)`, symmetric in its two arguments. -/
def IsCellConfiguration (K : CellData) : Prop :=
  (∀ z : ℂ, ∃ U ∈ 𝓝 z, {H ∈ K.cells | (H ∩ U).Nonempty}.Finite) ∧
  (∀ H ∈ K.cells, IsCompact H ∧ IsConnected H ∧ (interior H).Nonempty) ∧
  (⋃₀ K.cells = univ) ∧
  (∀ H ∈ K.cells, ∀ H' ∈ K.cells, H ≠ H' → volume (H ∩ H') = 0) ∧
  (∀ H H', K.adj H H' → H ∈ K.cells ∧ H' ∈ K.cells ∧ K.adj H' H ∧ (H ∩ H').Nonempty ∧ H ≠ H') ∧
  (∀ H H', K.adj H H' → 0 < K.cond H H' ∧ K.cond H H' = K.cond H' H)

/-- The cells of `K` meeting `A`, the vertex set `𝓗(A)` of (1.14) (GMS p. 15). -/
def cellsMeeting (K : CellData) (A : Set ℂ) : Set (Set ℂ) :=
  {H ∈ K.cells | (H ∩ A).Nonempty}

/-- The admissible homeomorphisms `f_r` of (1.15) (GMS p. 15): `f_r` takes each cell of `𝓗(B_r(0))` to a cell of
`𝓗'(B_r(0))` and preserves adjacency, and `f_r⁻¹` does the same with the roles of `K` and `K'` reversed. -/
def IsAdmissibleMap (r : ℝ) (K K' : CellData) (f : ℂ ≃ₜ ℂ) : Prop :=
  (∀ H ∈ cellsMeeting K (ball 0 r), f '' H ∈ cellsMeeting K' (ball 0 r)) ∧
  (∀ H ∈ cellsMeeting K (ball 0 r), ∀ H' ∈ cellsMeeting K (ball 0 r), K.adj H H' → K'.adj (f '' H) (f '' H')) ∧
  (∀ H ∈ cellsMeeting K' (ball 0 r), f.symm '' H ∈ cellsMeeting K (ball 0 r)) ∧
  (∀ H ∈ cellsMeeting K' (ball 0 r), ∀ H' ∈ cellsMeeting K' (ball 0 r),
    K'.adj H H' → K.adj (f.symm '' H) (f.symm '' H'))

/-- The metric (1.15) of GMS p. 15, with values in `[0, ∞]`:
`d^CC(H, H') := ∫₀^∞ ( e^{-r} ∧ inf_{f_r} { sup_{z ∈ ℂ} |z - f_r(z)| + max_{{H₁,H₂} ∈ E𝓗(B_r(0))} |𝔠(H₁,H₂) - 𝔠'(f_r H₁, f_r H₂)| } ) dr`.
The suprema and the infimum are taken in `ℝ≥0∞`, so unbounded expressions are `∞` rather than junk. -/
noncomputable def cellDist (K K' : CellData) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ), min (ENNReal.ofReal (Real.exp (-r)))
    (⨅ (f : ℂ ≃ₜ ℂ) (_ : IsAdmissibleMap r K K' f),
      (⨆ z : ℂ, ENNReal.ofReal (dist z (f z))) +
        ⨆ (p : Set ℂ × Set ℂ) (_ : p.1 ∈ cellsMeeting K (ball 0 r) ∧ p.2 ∈ cellsMeeting K (ball 0 r) ∧
            K.adj p.1 p.2),
          ENNReal.ofReal |K.cond p.1 p.2 - K'.cond (f '' p.1) (f '' p.2)|)

/-- A set of cell configurations is open for the topology of the metric (1.15) (balls `{K' : d(K, K') < ε}`). -/
def IsCellOpen (U : Set CellData) : Prop :=
  ∀ K ∈ U, ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ K' : CellData, cellDist K K' < ε → K' ∈ U

/-- The Borel σ-algebra of the metric (1.15) on raw cell data; random cell configurations are measurable for it. -/
instance cellMeasurableSpace : MeasurableSpace CellData :=
  MeasurableSpace.generateFrom {U | IsCellOpen U}

/-- The affine map `w ↦ C (w - z)` of `ℂ` (GMS (1.2)), applied to a set. -/
def affineImage (C : ℝ) (z : ℂ) (A : Set ℂ) : Set ℂ :=
  (fun w : ℂ => (C : ℂ) * (w - z)) '' A

/-- The inverse affine map `w ↦ z + C⁻¹ w`, applied to a set. -/
def affineImageInv (C : ℝ) (z : ℂ) (A : Set ℂ) : Set ℂ :=
  (fun w : ℂ => z + (C : ℂ)⁻¹ * w) '' A

/-- The action `K ↦ C (K - z)` of GMS (1.2): cells, adjacency and conductance are transported by the affine map. -/
def cellAct (C : ℝ) (z : ℂ) (K : CellData) : CellData where
  cells := affineImage C z '' K.cells
  adj := fun A B => K.adj (affineImageInv C z A) (affineImageInv C z B)
  cond := fun A B => K.cond (affineImageInv C z A) (affineImageInv C z B)

/-- Condition 4 of Definition 1.2 (GMS pp. 4-5), the mass-transport identity, for the law `P` of `H`:
for every measurable `F : M × ℂ × ℂ → [0, ∞]` with `F(C(M - z), C(w₀ - z), C(w₁ - z)) = C⁻² F(M, w₀, w₁)` (1.2),
`E ∫_ℂ F(M, 0, w) dw = E ∫_ℂ F(M, w, 0) dw` (1.3). The four conditions of Definition 1.2 are equivalent (printed
Appendix B), and condition 4 is used as the characterisation of translation invariance modulo scaling. -/
def MassTransport {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → CellData) : Prop :=
  ∀ F : CellData → ℂ → ℂ → ℝ≥0∞, Measurable (fun p : CellData × ℂ × ℂ => F p.1 p.2.1 p.2.2) →
    (∀ (C : ℝ), 0 < C → ∀ (z w₀ w₁ : ℂ) (K : CellData),
      F (cellAct C z K) ((C : ℂ) * (w₀ - z)) ((C : ℂ) * (w₁ - z)) = ENNReal.ofReal ((C ^ 2)⁻¹) * F K w₀ w₁) →
    ∫⁻ ω, ∫⁻ w, F (H ω) 0 w ∂volume ∂P = ∫⁻ ω, ∫⁻ w, F (H ω) w 0 ∂volume ∂P

/-- Translation invariance modulo scaling of the law of `H` (GMS Definition 1.2, p. 4): almost surely the faces are
compact configurations (`IsCellConfiguration` includes this), and the mass-transport condition holds. -/
def TranslationInvariantModScaling {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → CellData) : Prop :=
  (∀ᵐ ω ∂P, IsCellConfiguration (H ω)) ∧ MassTransport P H

/-- Ergodicity modulo scaling (GMS Definition 1.3, p. 6): translation invariance modulo scaling, and probability `0`
or `1` for every Borel event `E` invariant under `K ↦ C (K - z)` (for all `C > 0` and `z ∈ ℂ`). -/
def ErgodicModScaling {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → CellData) : Prop :=
  TranslationInvariantModScaling P H ∧
  ∀ E : Set CellData, MeasurableSet E →
    (∀ (C : ℝ), 0 < C → ∀ (z : ℂ) (K : CellData), K ∈ E ↔ cellAct C z K ∈ E) →
    P (H ⁻¹' E) = 0 ∨ P (H ⁻¹' E) = 1

/-- Axis-parallel line segments `L ⊂ ℂ` (GMS Theorem 1.16, condition 3): horizontal or vertical, of positive length. -/
def IsAxisSegment (L : Set ℂ) : Prop :=
  ∃ a b c : ℝ, a < b ∧
    (L = {z : ℂ | z.im = c ∧ z.re ∈ Icc a b} ∨ L = {z : ℂ | z.re = c ∧ z.im ∈ Icc a b})

/-- Connectedness along a line (GMS Theorem 1.16, condition 3, p. 15): the subgraph of `K` on the cells meeting `L`,
with the edges joining them, is connected. -/
def LineConnected (K : CellData) (L : Set ℂ) : Prop :=
  (cellsMeeting K L).Nonempty ∧
    ∀ H₁ ∈ cellsMeeting K L, ∀ H₂ ∈ cellsMeeting K L,
      Relation.ReflTransGen (fun A B => A ∈ cellsMeeting K L ∧ B ∈ cellsMeeting K L ∧ K.adj A B) H₁ H₂

/-- `π(H) := ∑_{H' ∼ H} 𝔠(H, H')` of (1.16), GMS p. 15. -/
noncomputable def piWeight (K : CellData) (H : Set ℂ) : ℝ :=
  ∑ᶠ (H' : Set ℂ) (_ : K.adj H H'), K.cond H H'

/-- `π*(H) := ∑_{H' ∼ H} 1 / 𝔠(H, H')` of (1.16), GMS p. 15. -/
noncomputable def piStar (K : CellData) (H : Set ℂ) : ℝ :=
  ∑ᶠ (H' : Set ℂ) (_ : K.adj H H'), (K.cond H H')⁻¹

/-- The finite expectation hypothesis (1.5), GMS p. 8, for a choice `sel K` of the cell containing `0`:
`E[ diam(H₀)² / Area(H₀) · π(H₀) ] < ∞` and `E[ diam(H₀)² / Area(H₀) · π*(H₀) ] < ∞`, with `H₀ = sel (H ω)`. -/
def FiniteExpectation {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → CellData)
    (sel : CellData → Set ℂ) : Prop :=
  ∫⁻ ω, ENNReal.ofReal (diam (sel (H ω)) ^ 2 / (volume (sel (H ω))).toReal * piWeight (H ω) (sel (H ω))) ∂P < ∞ ∧
  ∫⁻ ω, ENNReal.ofReal (diam (sel (H ω)) ^ 2 / (volume (sel (H ω))).toReal * piStar (H ω) (sel (H ω))) ∂P < ∞

/-- The hypotheses of GMS Theorem 1.16 (p. 15), except the finite expectation (1.5), which is stated for each choice
`sel` of the cell containing `0` in `GMSHarmonicCentreStmt`: `H` is a measurable random cell configuration, ergodic
modulo scaling (conditions 1-4 reduced to the mass-transport characterisation), and a.s. connected along every axis
segment (condition 3). -/
def GMSTheorem116Hyp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → CellData) : Prop :=
  IsProbabilityMeasure P ∧ Measurable H ∧ ErgodicModScaling P H ∧
    ∀ᵐ ω ∂P, ∀ L : Set ℂ, IsAxisSegment L → LineConnected (H ω) L

/-- Discrete harmonicity on the cells of `K` for the conductances `𝔠` (GMS Theorem 1.16, p. 15): at every cell `H`,
`∑_{H' ∼ H} 𝔠(H, H') (φ(H') - φ(H)) = 0`, equivalently `φ(H) = ∑_{H'∼H} 𝔠(H,H') φ(H') / π(H)`. -/
def IsDiscreteHarmonic (K : CellData) (φ : Set ℂ → ℂ) : Prop :=
  ∀ H ∈ K.cells, ∑ᶠ (H' : Set ℂ) (_ : K.adj H H'), K.cond H H' * (φ H' - φ H) = 0

/-- `φ₀(H) := ∫_H z dz` exactly as printed on GMS p. 15 (below (1.17)), without any normalisation. This is a
suspected defect: the words "Euclidean center" indicate `(1/Area(H)) ∫_H z dz`; see `phi0Centroid`. -/
noncomputable def phi0Literal (H : Set ℂ) : ℂ :=
  ∫ z in H, z

/-- The Euclidean centre `(1/Area(H)) ∫_H z dz` (the reading that the words "Euclidean center" on GMS p. 15 indicate).
Staged as an alternative; the choice is for the operator. -/
noncomputable def phi0Centroid (H : Set ℂ) : ℂ :=
  ((volume H).toReal)⁻¹ • ∫ z in H, z

/-- The harmonic-centre limit (1.17) of GMS Theorem 1.16 (p. 15), parametrised by the choice `φ₀` of the centre of a
cell (`phi0Literal` or `phi0Centroid`): for every measurable random cell configuration `H` satisfying the hypotheses
of Theorem 1.16 with the finite expectation (1.5) for the cell choice `sel`, there is a random function `Φ` on the cells
that is discrete harmonic almost surely, with `(1/r) max_{H' ∈ 𝓗(B_r(0))} |Φ(H') - φ₀(H')| → 0` almost surely.
The maximum over the finite set `𝓗(B_r(0))` is written as the uniform bound `≤ δ r` for all `δ > 0` and all large `r`.
This is one conclusion of Theorem 1.16; the recurrence and the Brownian limit are not staged here. -/
def GMSHarmonicCentreStmt (φ₀ : Set ℂ → ℂ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → CellData) (sel : CellData → Set ℂ),
    (∀ K : CellData, IsCellConfiguration K → 0 ∈ sel K ∧ sel K ∈ K.cells) →
    GMSTheorem116Hyp P H → FiniteExpectation P H sel →
    ∃ Φ : Ω → Set ℂ → ℂ,
      (∀ᵐ ω ∂P, IsDiscreteHarmonic (H ω) (Φ ω)) ∧
      ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ r : ℝ in atTop,
        ∀ H' ∈ cellsMeeting (H ω) (ball 0 r), ‖Φ ω H' - φ₀ H'‖ ≤ δ * r

/-! ### The quenched walk, the time change and the planar Brownian limit (GMS Theorem 1.16, p. 15)

Carrier decisions, recorded for the operator:
* (D1) The printed walk `X̂` is piecewise constant and is kept as printed. Its local uniform convergence is expressed
  through test functionals that are cylinder-measurable, bounded and continuous for the local uniform distance
  `locUnifDist` (`IsLocUnifTest`). No interpolation is applied.
* (D2) The centre `φ₀` is a parameter (`phi0Literal` or `phi0Centroid`).
* (D3) The walk starts at `sel K`, a cell containing `0`; the printed theorem does not name the starting cell.
The quenched law is any family of probability measures on jump paths that satisfies the Markov finite-dimensional
identities (`IsQuenchedWalkLaw`). Existence of such laws (Ionescu-Tulcea) and existence of the planar Brownian law are
standard and are not formalised here; the statements below are universal claims over them. -/

/-- The jump chain's state space carries the discrete σ-algebra: every set of cells is measurable (scoped here). -/
scoped instance discreteCellSpace : MeasurableSpace (Set ℂ) := ⊤

/-- Holding time `Area(H)/π(H)` of the continuous-time walk at a cell (GMS Theorem 1.16, p. 15). -/
noncomputable def holdingTime (K : CellData) (H : Set ℂ) : ℝ :=
  (volume H).toReal / piWeight K H

/-- Jump times `T_n = ∑_{j<n} Area(Y_j)/π(Y_j)` of a discrete path `y` of cells. -/
noncomputable def jumpTime (K : CellData) (y : ℕ → Set ℂ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, holdingTime K (y j)

/-- The index `N(t) = min {n : t < T_{n+1}}` of the jump chain in force at time `t`. -/
noncomputable def walkIndex (K : CellData) (y : ℕ → Set ℂ) (t : ℝ) : ℕ :=
  sInf {n : ℕ | t < jumpTime K y (n + 1)}

/-- `X̂_t = φ(Y_{N(t)})`: the continuous-time walk composed with a choice `φ` of a point of each cell. -/
noncomputable def walkPoint (K : CellData) (φ : CellData → Set ℂ → ℂ) (y : ℕ → Set ℂ) (t : ℝ) : ℂ :=
  φ K (y (walkIndex K y t))

/-- The scaled path `t ↦ ε X̂_{t/ε²}` on `[0, ∞)` (GMS Theorem 1.16, p. 15). -/
noncomputable def scaledWalk (K : CellData) (φ : CellData → Set ℂ → ℂ) (ε : ℝ) (y : ℕ → Set ℂ) :
    ℝ≥0 → ℂ :=
  fun t => (ε : ℂ) * walkPoint K φ y ((t : ℝ) / ε ^ 2)

open scoped Classical in
/-- Transition probabilities `𝔠(H,H')/π(H)` of the jump chain on `K` (GMS p. 15, (1.16)); `0` for nonadjacent cells. -/
noncomputable def transitionProb (K : CellData) (H H' : Set ℂ) : ℝ :=
  if K.adj H H' then K.cond H H' / piWeight K H else 0

/-- `Q` is the quenched law of the jump chain of the walk on `K` started at `sel K` (GMS Theorem 1.16, p. 15):
a probability measure on jump paths with `Q(Y_i = h_i, i ≤ n) = 1_{h_0 = sel K} ∏_{i<n} 𝔠(h_i,h_{i+1})/π(h_i)`. -/
def IsQuenchedWalkLaw (K : CellData) (sel : CellData → Set ℂ) (Q : Measure (ℕ → Set ℂ)) : Prop :=
  IsProbabilityMeasure Q ∧
    ∀ (n : ℕ) (h : ℕ → Set ℂ),
      (h 0 = sel K → Q {y | ∀ i ≤ n, y i = h i} =
        ENNReal.ofReal (∏ i ∈ Finset.range n, transitionProb K (h i) (h (i + 1)))) ∧
      (h 0 ≠ sel K → Q {y | ∀ i ≤ n, y i = h i} = 0)

/-- Local uniform distance `∑_n 2^{-(n+1)} min(1, sup_{t ≤ n} |f(t) - g(t)|)` on paths `ℝ≥0 → ℂ`, valued in `[0, ∞]`. -/
noncomputable def locUnifDist (f g : ℝ≥0 → ℂ) : ℝ≥0∞ :=
  ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) *
    min 1 (⨆ t : ℝ≥0, ⨆ (_ : (t : ℝ) ≤ (n : ℝ)), ENNReal.ofReal ‖f t - g t‖)

/-- Continuity of a path functional for the local uniform topology. -/
def IsLocUnifContinuous (F : (ℝ≥0 → ℂ) → ℝ) : Prop :=
  ∀ f : ℝ≥0 → ℂ, ∀ η : ℝ, 0 < η → ∃ δ : ℝ≥0∞, 0 < δ ∧
    ∀ g : ℝ≥0 → ℂ, locUnifDist f g < δ → |F f - F g| < η

/-- Admissible test functionals for local uniform convergence of path laws: cylinder-measurable, bounded, and locally
uniformly continuous. -/
def IsLocUnifTest (F : (ℝ≥0 → ℂ) → ℝ) : Prop :=
  Measurable F ∧ (∃ M : ℝ, ∀ f, |F f| ≤ M) ∧ IsLocUnifContinuous F

/-- The planar Brownian law with covariance `Cov`, started at `0` (GMS Theorem 1.16, p. 15), given by its
finite-dimensional distributions: for finite families of times `t_k ≥ 0` and vectors `u_k ∈ ℝ²`,
`E exp(i ∑_k ⟨u_k, B_{t_k}⟩) = exp(-½ ∑_{k,l} min(t_k, t_l) ⟨u_k, Cov u_l⟩)`, where `B = (Re, Im)`. -/
def IsPlanarBMLaw (Cov : Matrix (Fin 2) (Fin 2) ℝ) (μ : Measure (ℝ≥0 → ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ (n : ℕ) (t : Fin n → ℝ≥0) (u : Fin n → Fin 2 → ℝ),
      ∫ f, Complex.exp (Complex.I * ((∑ k, (u k 0 * (f (t k)).re + u k 1 * (f (t k)).im) : ℝ) : ℂ)) ∂μ =
        Complex.exp (((-(1 / 2 : ℝ)) * ∑ k, ∑ l, min (t k : ℝ) (t l : ℝ) *
          ∑ a, ∑ b, u k a * Cov a b * u l b : ℝ) : ℂ)

/-- GMS Theorem 1.16 (p. 15), all three printed conclusions, for the walk `X` on `H` started at `sel H` with quenched law
`Q H` and the cell choice `φ`, with the centre `φ₀` of (1.17):
(i) there is a deterministic `Cov` with `det Cov ≠ 0` such that, almost surely, the quenched laws of `t ↦ ε X̂_{t/ε²}`
converge as `ε → 0` to every planar Brownian law with covariance `Cov` (tested by `IsLocUnifTest` functionals);
(ii) almost surely the jump chain returns to `sel H` infinitely often (recurrence);
(iii) there is a random discrete harmonic `Φ` with the limit (1.17) almost surely.
Hypotheses are those of `GMSTheorem116Hyp` and the finite expectation (1.5) for the cell choice `sel`.
Existence of the quenched laws `Q` and of the Brownian laws is not asserted here. -/
def GMSTheorem116Stmt (φ₀ : Set ℂ → ℂ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (H : Ω → CellData) (sel : CellData → Set ℂ)
    (φ : CellData → Set ℂ → ℂ) (Q : CellData → Measure (ℕ → Set ℂ)),
    (∀ K : CellData, IsCellConfiguration K → ∀ h ∈ K.cells, φ K h ∈ h) →
    (∀ K : CellData, IsCellConfiguration K → 0 ∈ sel K ∧ sel K ∈ K.cells) →
    GMSTheorem116Hyp P H → (∀ᵐ ω ∂P, IsQuenchedWalkLaw (H ω) sel (Q (H ω))) →
    FiniteExpectation P H sel →
    (∃ Cov : Matrix (Fin 2) (Fin 2) ℝ, Cov.det ≠ 0 ∧ ∀ μ : Measure (ℝ≥0 → ℂ), IsPlanarBMLaw Cov μ →
      ∀ᵐ ω ∂P, ∀ F : (ℝ≥0 → ℂ) → ℝ, IsLocUnifTest F →
        Tendsto (fun ε : ℝ => ∫ y, F (scaledWalk (H ω) φ ε y) ∂(Q (H ω))) (𝓝[>] 0) (𝓝 (∫ f, F f ∂μ))) ∧
    (∀ᵐ ω ∂P, Q (H ω) {y | ∃ᶠ n in atTop, y n = sel (H ω)} = 1) ∧
    (∃ Φ : Ω → Set ℂ → ℂ, (∀ᵐ ω ∂P, IsDiscreteHarmonic (H ω) (Φ ω)) ∧
      ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ r : ℝ in atTop,
        ∀ H' ∈ cellsMeeting (H ω) (ball 0 r), ‖Φ ω H' - φ₀ H'‖ ≤ δ * r)

end MatedCRT.StoppedPoleReconstruction
