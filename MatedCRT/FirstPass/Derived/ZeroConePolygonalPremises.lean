import MatedCRT.FirstPass.Derived.ZeroConePolygonalConfig
import MatedCRT.FirstPass.Derived.GMS21ZeroConeAnnulusRepair
import MatedCRT.FirstPass.Derived.ZeroConeStandardBorelSteps

/-!
# Three statements about the law of the zero-cone polygonal configuration

For the mating-of-trees coupling `D`, `γ ∈ (0, 2)`, a measurable version `G` of the boundary-length pair of the
zero-cone curve and a default point `H₀` of the GMS space, let
`Φ_G p := polygonalConfig H₀ (phaseShiftedData η₀ G 1 p)`, `p = (ω, θ)`, be the polygonal configuration of the
unit-mesh datum of the curve `t ↦ η₀(t + θ)` and the contour edge counts of `t ↦ G(t + θ)`, the phase `θ` being
uniform on `[0, 1]` and independent of everything else. The proof of Proposition 3.1 of Gwynne–Miller–Sheffield
(arXiv:1705.11161v5, pp. 22-24) verifies the hypotheses of the invariance principle for random cell
configurations (Gwynne–Miller–Sheffield, arXiv:1807.07515v3, Theorem 1.16) for the configuration of the cells of
the zero-cone curve. This file states, as definitions only, three properties of the coupling used to transfer that
verification to the law of `Φ_G`:

* `ZeroConeCurveRotationLaw` (proof of Proposition 3.1, p. 24, lines 1211-1212): the law of the zero-cone curve
  parametrized by quantum area is invariant under the quarter turn.
* `ZeroConePolygonalPhasePeriods` (proof of Proposition 3.1, p. 23, lines 1193-1196): almost surely, a bounded
  similarity-invariant observable of `Φ_G` has arbitrarily small periods in the phase.
* `planeSquare`, `AttainableAsSquareAverage`, `ZeroConePolygonalSquareRerooting` (Lemma A.4, p. 38, and
  hypothesis 1 of Theorem 1.16 as restated on p. 11): the law of `Φ_G` is attainable as an average over increasing
  random squares exhausting the plane, in the sense of condition 2 of Definition 1.2 of arXiv:1807.07515v3.

The boundary-length pair `G` enters only through the edge counts of `Φ_G`; no joint law of the curve and `G` under
rotations is stated.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal BoundedContinuousFunction

noncomputable section

namespace MatedCRT.ZeroConePolygonal

open ReflectedGMS.GMS MatedCRTHarmonic MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4b

/-- The closed square `[a, a + ℓ] × [b, b + ℓ]` of the plane. -/
def planeSquare (a b ℓ : ℝ) : Set ReflectedGMS.Plane := {x | x 0 ∈ Icc a (a + ℓ) ∧ x 1 ∈ Icc b (b + ℓ)}

/-- **Attainability as an average over random squares, modulo scaling** (condition 2 of Definition 1.2 of
Gwynne–Miller–Sheffield, arXiv:1807.07515v3, p. 4, with random squares `U_n`): `μ` is the law of a random cell
configuration `H` on some probability space, and there are random closed squares
`U_n = [a_n, a_n + ℓ_n] × [b_n, b_n + ℓ_n]` and random scale factors `C_n = exp c_n > 0`, depending on everything
and on the sampled point, such that, with `z_n` sampled uniformly from Lebesgue measure on `U_n` given everything,
`C_n (H - z_n)` converges in law to `H`: the integral of every bounded continuous function on the GMS space
(topology of the metric `d^CC`) converges.

The printed condition asks only that the union of the `U_n` be the whole plane almost surely. Here the squares are
required to increase and to contain eventually every ball around the origin, almost surely: the exhaustion of
hypothesis 1 of Theorem 1.16 as restated in Gwynne–Miller–Sheffield, arXiv:1705.11161v5, p. 11, lines 516-524
("increasing sequence of open sets `U_j ⊂ ℂ`, each of which is either a square or a disk, whose union is all of
`ℂ`"). -/
def AttainableAsSquareAverage (μ : Measure GMSSpace) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (H : Ω → GMSSpace),
    IsProbabilityMeasure P ∧ AEMeasurable H P ∧ P.map H = μ ∧
    ∃ a b ℓ : ℕ → Ω → ℝ, (∀ n, Measurable (a n) ∧ Measurable (b n) ∧ Measurable (ℓ n)) ∧
      (∀ n ω, 0 < ℓ n ω) ∧
      (∀ᵐ ω ∂P, ∀ n, planeSquare (a n ω) (b n ω) (ℓ n ω) ⊆
        planeSquare (a (n + 1) ω) (b (n + 1) ω) (ℓ (n + 1) ω)) ∧
      (∀ᵐ ω ∂P, ∀ r : ℝ, ∀ᶠ n in atTop,
        Metric.ball (0 : ReflectedGMS.Plane) r ⊆ planeSquare (a n ω) (b n ω) (ℓ n ω)) ∧
      ∃ c : ℕ → Ω × ReflectedGMS.Plane → ℝ,
        (∀ n, AEMeasurable (fun q => similarityConfig (c n q) q.2 (H q.1)) (P.prod volume)) ∧
        ∀ φ : GMSSpace →ᵇ ℝ, Tendsto
          (fun n => ∫ ω, (⨍ z in planeSquare (a n ω) (b n ω) (ℓ n ω),
            φ (similarityConfig (c n (ω, z)) z (H ω))) ∂P)
          atTop (𝓝 (∫ ω, φ (H ω) ∂P))

section ZeroCone

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Rotation invariance of the zero-cone curve parametrized by quantum area**: the law of the zero-cone curve
`η₀` and the law of its quarter turn `t ↦ i η₀(t)` agree.

Printed source: Gwynne–Miller–Sheffield, arXiv:1705.11161v5, proof of Proposition 3.1, p. 24, lines 1211-1212:
"The covariance matrix `Σ` is a scalar multiple of the identity since the law of `(h, η)` is invariant under
rotations about the origin", where `η` is the space-filling curve parametrized by the quantum area of the zero
cone `h` (p. 22). The boundary-length pair of the curve is not part of the statement. -/
def ZeroConeCurveRotationLaw (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (_hγ : γ ∈ Ioo (0 : ℝ) 2) : Prop :=
  P.map (fun ω => GMS310Transfer.quarterTurnCurve (η₀ ω)) = P.map η₀

/-- **Arbitrarily small phase periods of the polygonal observables.** For every measurable version `G` of the
boundary-length pair of the zero-cone curve and every bounded Borel function `Φ` on the GMS space with
`Φ(C (H - z)) = Φ(H)` for all `C > 0` and `z`, almost surely there are periods `D_j > 0` tending to `0` such that,
for every `j` and almost every phase `θ ∈ [0, 1]`, `Φ` takes the same value on the polygonal configurations of the
data at the phases `(θ + D_j) mod 1` and `θ`. The phase enters both the curve `t ↦ η₀(t + θ)` and the edge counts
of `t ↦ G(t + θ)`.

Printed source: Gwynne–Miller–Sheffield, arXiv:1705.11161v5, proof of Proposition 3.1, p. 23, lines 1193-1196:
"`G` is a.s. equal to a function of only `θ`. By (3.2), we have `G([θ − τ_z]) = G(θ)` ...". The printed
inference does not follow from the independence of the phase alone: for independent uniform `X` and `θ` on the
circle, `{X + θ}` is independent of `X` and is not constant given `θ`. The periods come instead from a comparison
of two quantum clocks on finite time intervals: adding a smooth bump `λ f` to the field gives an equivalent field
law (Cameron–Martin), the new clock differs from the old one by constants `d_+` and `d_-` on the future and the past
time tails, local approximations of the observable at uniform roots of capped squares (Lemma A.4, p. 38) give
equality at the phases `{θ + d_±}`, and `D = d_+ - d_- = ∫ (e^{γ λ f} - 1) dμ_h` is a period; `λ_j = 1/(j + 1)`
gives `D_j → 0`. -/
def ZeroConePolygonalPhasePeriods (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (H₀ : GMSSpace) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G →
    ∀ Φ : GMSSpace → ℝ, Measurable Φ → (∃ M : ℝ, ∀ H, |Φ H| ≤ M) →
      (∀ (s : ℝ) (u) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' → Φ H' = Φ H) →
      ∀ᵐ ω ∂P, ∃ Dp : ℕ → ℝ, (∀ j, 0 < Dp j) ∧ Tendsto Dp atTop (𝓝 0) ∧
        ∀ j, ∀ᵐ θ ∂zeroConePhase,
          Φ (polygonalConfig H₀ (GMS310Transfer.phaseShiftedData η₀ G 1
              (ω, toIcoMod (zero_lt_one' ℝ) 0 (θ + Dp j)))) =
            Φ (polygonalConfig H₀ (GMS310Transfer.phaseShiftedData η₀ G 1 (ω, θ)))

/-- **Rerooting of the polygonal configuration at uniform points of capped squares.** For every measurable
version `G` of the boundary-length pair of the zero-cone curve, the law of `Φ_G` under `P ⊗ Unif[0, 1]` is
attainable as an average over increasing random squares exhausting the plane (`AttainableAsSquareAverage`).

The squares: take a uniform dyadic system independent of everything and let `S_m` be its largest square
containing the origin of zero-cone quantum mass at most `m`; the levels `m = n + 1` give squares that increase and
eventually contain every ball around the origin, the exhaustion of hypothesis 1 of Theorem 1.16 as restated in
Gwynne–Miller–Sheffield, arXiv:1705.11161v5, p. 11, lines 516-524. With `Z_m` uniform in `S_m`, Lemma A.4 there
(p. 38, lines 2026-2041) gives a scale `C_m` with `h(C_m · + Z_m) + Q log C_m` equal in law to `h`, and the
rerooted configuration `C_m⁻¹ (Φ_G - Z_m)` has the law of `Φ_G` at every level. -/
def ZeroConePolygonalSquareRerooting (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (H₀ : GMSSpace) : Prop :=
  ∀ G : Ω → Path2, IsZeroConeBoundaryPair D hγ G →
    AttainableAsSquareAverage
      ((P.prod zeroConePhase).map fun p => polygonalConfig H₀ (GMS310Transfer.phaseShiftedData η₀ G 1 p))

end ZeroCone

end MatedCRT.ZeroConePolygonal
