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

end MatedCRT.StoppedPoleReconstruction
