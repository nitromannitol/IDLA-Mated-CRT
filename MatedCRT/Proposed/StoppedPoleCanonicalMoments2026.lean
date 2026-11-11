import Mathlib
import MatedCRT.Defs.Setting
import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section4

/-!
# Canonical published moment inputs (GMS arXiv:1705.11161v5, Section 4)

Source: Gwynne, Miller and Sheffield, *The Tutte embedding of the mated-CRT map converges to Liouville quantum
gravity*, arXiv:1705.11161v5 (retained printed text; PDF page index = printed page number).
Locators used here:
* Section 2.3.1, p. 17: the α-quantum cone (DMS14 Definition 4.10, `(ℂ, h, 0, ∞)`), the circle average embedding and
  the cone scale radius (2.4) `R_b := sup {r > 0 : h_r(0) + Q log r = γ⁻¹ log b}`;
* Section 3.1 setting (p. 29): `(ℂ, h, 0, ∞)` a 0-quantum cone with the circle average embedding; `η` a whole-plane
  space-filling SLE_κ sampled independently from `h`, parametrized by γ-LQG mass with respect to `h`, `η(0) = 0`;
* Section 4.1, p. 30: (4.3) `h^b := h(R_b ·) + Q log R_b` (no subtraction of `γ⁻¹ log b`) and `η^b := R_b⁻¹ η`; the
  coordinate change `μ_h(X) = μ_{h^b}(R_b⁻¹ X)` (formula (2.3) as applied there); Lemma 4.3, (4.6);
* Section 4.2, pp. 31: (4.12) `DA(H₀)`; Proposition 4.4, (4.14);
* Section 4.3, pp. 32-33: (4.19) the closed ball `B̄₀`; Definition 4.5 (inner degree (4.20), outer degree); (4.21);
  Proposition 4.6, (4.23); the uniform normalized-mass beta-moment paragraph immediately before (4.25), p. 33.
* BG arXiv:2211.04891v2 (Bou-Rabee and Gwynne): Lemma 3.3, pp. 23-24, and Theorem 4.1, p. 32, in canonical scope
  (below); the SLE/LQG embedding paragraph (corrected tex lines 189-195) and the Lemma 8.8 identification (lines 207-209).

Not staged, with reasons:
* (4.5) of Lemma 4.3: not consumed by the moment route.
* (4.22) of Proposition 4.6: its printed range `p ∈ [1, 4/γ)^2` is malformed; the route derives the inner-degree
  moment from the beta-moment paragraph and (4.6), never from (4.22).
* (4.25): its printed last bound carries the positive exponent `β(1-ζ)`; it is not imported.

Outer-expectation account (source fidelity). The printed moments of the degree and mass functionals are read as
outer expectations `MatedCRT.outerLIntegral` (Defs/Notation.lean). For a measurable integrand this is the printed
Lebesgue integral (`outerLIntegral_eq_lintegral_of_measurable`, below), so the two readings agree whenever the printed
quantity is measurable. The paper does not verify measurability of `deg_in`, `deg_out`, `DA` or of the normalized masses
`C^{-ζ} μ_{h^{C^ζ}}(𝔻)`; no statement here assumes or proves it, and the outer forms need none. The printed (4.22) and
(4.25) are not imported (see above); the moment route is the Chebyshev and tail-integration step.

Canonical laws. `IsCanonicalZeroConeModel` (GMS, zero cone) and `IsCanonicalSLEDecoratedCone` (BG, `γ`-cone) are
predicates on the joint law of the environment, not hypotheses on an abstract environment. The α-cone predicate
`IsAlphaQuantumCone` is the `IsQuantumCone` of `MatedCRT/Defs/QuantumCone.lean` with the drift parameter `α` in place of
`γ`.

The `…Stmt` declarations are published inputs (explicit hypotheses, not proved here). The internal consequences of those inputs (r3:2674-2753) were moved, with their names unchanged, to
`MatedCRT/Proofs/Sec5/StoppedPoleInnerDegreeMoments.lean`, which imports this file; this file does not import it.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set HarmonicBalls MarkovProcess
open scoped ENNReal NNReal

namespace MatedCRT.StoppedCanonicalMoments

open MatedCRT

/-- Radial law of the α-quantum cone (DMS14 Definition 4.10, GMS p. 17): `A_t = B_t + α t` for `t ≥ 0` and
`A_{-s} = B̂_s - α s` for `s ≥ 0`, where `B̂` has law `ν`. For `α = γ` this is `quantumConeRadialLaw γ`. -/
noncomputable def alphaQuantumConeRadialLaw (α : ℝ) (ν : Measure (ContinuousPath ℝ)) :
    Measure ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) :=
  ((brownianMotion 0).map fun w (t : ℝ≥0) => w t + α * t).prod
    (ν.map fun w (s : ℝ≥0) => w s - α * s)

/-- `IsAlphaQuantumCone γ α P hC hcirc`: under `P`, `(hC, hcirc)` are the pairings and circle averages of the
circle average embedding of the α-quantum cone (DMS14 Definition 4.10; GMS p. 17). The conditions are those of
`IsQuantumCone` (`MatedCRT/Defs/QuantumCone.lean`) with drift `α` in the radial process and conditioning
`B̂_t + (Q - α) t > 0`. The 0-quantum cone of GMS Section 3.1 is `IsAlphaQuantumCone γ 0`. -/
structure IsAlphaQuantumCone {Ω : Type*} [MeasurableSpace Ω] (γ α : ℝ) (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop where
  /-- Each pairing with a test function is a random variable. -/
  measurable_pairing : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ
  /-- Each circle average of positive radius is a random variable. -/
  measurable_circle : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z
  /-- A.s. the circle average process is continuous in `(r, z) ∈ (0, ∞) × ℂ`. -/
  ae_continuousOn_circle :
    ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)
  /-- The radial process `t ↦ h_{e^{-t}}(0)` has the law of the α-radial process `A`. -/
  radial_law : ∃ ν : Measure (ContinuousPath ℝ), IsBMConditionedPositive (lqgQ γ - α) ν ∧
    P.map (fun ω => radialProcess (hcirc ω)) = alphaQuantumConeRadialLaw α ν
  /-- The lateral part is independent of the radial process. -/
  indep : IndepFun (fun ω => radialProcess (hcirc ω)) (fun ω => lateralProcess (hC ω) (hcirc ω)) P
  /-- The lateral part has the law of the lateral part of a whole-plane GFF. -/
  lateral_law : ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ), IsProbabilityMeasure P' ∧ IsWholePlaneGFF P' hC' hcirc' ∧
    P.map (fun ω => lateralProcess (hC ω) (hcirc ω)) = P'.map (fun ω => lateralProcess (hC' ω) (hcirc' ω))

/-- The canonical zero-cone model (GMS Section 3.1, p. 29): `(hC, hcirc)` is the circle average embedding of the
0-quantum cone; `μ = μ_h` is its γ-LQG area measure (`IsLQGMeasure`); `η` is a whole-plane space-filling SLE_{16/γ²}
(`16/γ²` as in `MatedCRTEnv.IsValid`) independent of `σ(h)` (`fieldSigmaAlgebra 0 hC univ`, as in
`MatedCRTEnv.fieldSigma`); a.s. `η` is parametrized by `μ_h`-area with `η(0) = 0` (`IsAreaParametrized`).
This is the joint law of `(h, η)` on any probability space, not an abstract environment. -/
structure IsCanonicalZeroConeModel (𝒮 : SpaceFillingSLEModel) (γ : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (η : Ω → ℝ → ℂ) : Prop where
  /-- `P` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure P
  /-- `h` is the circle average embedding of the 0-quantum cone. -/
  isZeroCone : IsAlphaQuantumCone γ 0 P hC hcirc
  /-- `μ = μ_h` is the γ-LQG area measure of `h`. -/
  isLQGMeasure : IsLQGMeasure P γ hcirc μ
  /-- `η` is a whole-plane space-filling SLE_{16/γ²} independent of `σ(h)`. -/
  isSLE : 𝒮.IsSLE P (fieldSigmaAlgebra 0 hC Set.univ) (16 / γ ^ 2) η
  /-- `η(0) = 0` and `μ_h(η([a,b])) = b - a`, a.s. -/
  isAreaParametrized : ∀ᵐ ω ∂P, IsAreaParametrized (μ ω) (η ω)

/-- `DA(H₀)` of (4.12), GMS p. 31: the supremum over `s ∈ [0, 1]` of `diam(η([s-1, s]))² / area(η([s-1, s]))`,
where area is Lebesgue measure on `ℂ` and the arithmetic is in `ℝ≥0∞`. -/
noncomputable def gmsDA (η : ℝ → ℂ) : ℝ≥0∞ :=
  ⨆ s ∈ Set.Icc (0 : ℝ) 1, (Metric.ediam (η '' Set.Icc (s - 1) s)) ^ 2 / volume (η '' Set.Icc (s - 1) s)

/-- The closed Euclidean ball `B̄₀ := B̄_{4 diam(η([-1,1]))}(0)` of (4.19), GMS p. 32. -/
noncomputable def gmsB0 (η : ℝ → ℂ) : Set ℂ :=
  Metric.closedBall 0 (4 * Metric.diam (η '' Set.Icc (-1) 1))

/-- The intervals `[a_j, b_j]`, `j ∈ [1, N]`, intersect only at their endpoints (Definition 4.5, GMS pp. 32-33): a
common point of two of them is an endpoint of each. -/
def IntervalsMeetAtEndpoints (a b : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N, j ≠ k →
    Set.Icc (a j) (b j) ∩ Set.Icc (a k) (b k) ⊆ ({a j, b j} : Set ℝ) ∩ ({a k, b k} : Set ℝ)

/-- The property of `N` in the inner degree (Definition 4.5, GMS p. 32): there are `N` intervals `[a_j, b_j]` of
length `b_j - a_j = 1` which intersect only at their endpoints, with `η([a_j, b_j]) ⊆ B̄₀` and
`η([a_j, b_j]) ∩ η([-1, 1]) ≠ ∅`. -/
def GMSInnerDegreeProp (η : ℝ → ℂ) (N : ℕ) : Prop :=
  ∃ a b : ℕ → ℝ, IntervalsMeetAtEndpoints a b N ∧
    ∀ j ∈ Finset.Icc 1 N, b j - a j = 1 ∧ η '' Set.Icc (a j) (b j) ⊆ gmsB0 η ∧
      (η '' Set.Icc (a j) (b j) ∩ η '' Set.Icc (-1) 1).Nonempty

/-- The inner degree `deg_in(H₀)` of Definition 4.5 (GMS p. 32): the largest `N ∈ ℕ` with `GMSInnerDegreeProp`
(valued in `ℕ∞`; the family of admissible `N` is downward closed). -/
noncomputable def gmsInnerDegree (η : ℝ → ℂ) : ℕ∞ :=
  ⨆ N ∈ {N : ℕ | GMSInnerDegreeProp η N}, (N : ℕ∞)

/-- The property of `N'` in the outer degree (Definition 4.5, GMS p. 33): there are `N'` intervals `[a_j, b_j]`
which intersect only at their endpoints, with `η((a_j, b_j)) ⊆ int B̄₀`, one endpoint of `η([a_j, b_j])` on
`∂B̄₀` and the other endpoint in `η([-1, 1])`. -/
def GMSOuterDegreeProp (η : ℝ → ℂ) (N : ℕ) : Prop :=
  ∃ a b : ℕ → ℝ, IntervalsMeetAtEndpoints a b N ∧
    ∀ j ∈ Finset.Icc 1 N, η '' Set.Ioo (a j) (b j) ⊆ interior (gmsB0 η) ∧
      ((η (a j) ∈ frontier (gmsB0 η) ∧ η (b j) ∈ η '' Set.Icc (-1) 1) ∨
        (η (b j) ∈ frontier (gmsB0 η) ∧ η (a j) ∈ η '' Set.Icc (-1) 1))

/-- The outer degree `deg_out(H₀)` of Definition 4.5 (GMS p. 33): the largest `N' ∈ ℕ` with `GMSOuterDegreeProp`. -/
noncomputable def gmsOuterDegree (η : ℝ → ℂ) : ℕ∞ :=
  ⨆ N ∈ {N : ℕ | GMSOuterDegreeProp η N}, (N : ℕ∞)

/-- The circle average process of `h^b := h(R ·) + Q log R` (GMS (4.3), p. 30) with `R = R_b`:
`h^b_r(z) = h_{R r}(R z) + Q log R`. The term `γ⁻¹ log b` is NOT subtracted (contrast `MatedCRT.rescaledCircle`
in `MatedCRT/Defs/QuantumCone.lean`, which does subtract it). -/
noncomputable def gmsRescaledCircle (γ : ℝ) (hcirc : ℝ → ℂ → ℝ) (R : ℝ) : ℝ → ℂ → ℝ :=
  fun r z => hcirc (R * r) ((R : ℂ) * z) + lqgQ γ * Real.log R

/-- **Lemma 4.3, (4.6)**, GMS arXiv:1705.11161v5 p. 30: `P[η([-1,1]) ⊂ B_{R_C/8}(0)] = 1 - o_C^∞(C)` as `C → ∞`,
i.e. for every `N > 0` there are `K, C₀` with `P[η([-1,1]) ⊄ B_{R_C/8}(0)] ≤ K C^{-N}` for `C ≥ C₀`. The range `N > 0`
is the printed one ("for every $N>0$"); no `N ≤ 0` case is asserted. The radii are the cone scale
radii `R_C = coneScaleRadius γ h C` of (2.4). Lemma 4.3's other display (4.5) is not staged. -/
def GMSLemma43Eq46Stmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
    ∀ N : ℝ, 0 < N → ∃ K C₀ : ℝ, 1 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) C / 8))} ≤
        ENNReal.ofReal (K * C ^ (-N))

/-- **Proposition 4.4, (4.14)**, GMS p. 31: `E[DA(H₀)^p] < ∞` for all `p ≥ 1` (outer expectation). -/
def GMSProposition44Stmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
    ∀ p : ℝ, 1 ≤ p → MatedCRT.outerLIntegral P (fun ω => gmsDA (η ω) ^ p) < ⊤

/-- **Proposition 4.6, (4.23)**, GMS p. 33: `E[deg_out(H₀)^p] < ∞` for all `p ≥ 1` (outer expectation). The inner-degree
display (4.22) is not staged; see the module docstring. -/
def GMSProposition46OuterStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
    ∀ p : ℝ, 1 ≤ p → MatedCRT.outerLIntegral P (fun ω => (gmsOuterDegree (η ω)).toENNReal ^ p) < ⊤

/-- **Uniform normalized-mass beta-moment paragraph**, GMS p. 33, immediately before (4.25) (proof of Proposition
4.6): for fixed `ζ ∈ (0, 1)` and `β ∈ (0, 4/γ²)`, the normalized masses `Y_C := C^{-ζ} μ_{h^{C^ζ}}(𝔻)` satisfy
`sup_{C > 1} E[Y_C^β] < ∞` ("finite, C-independent moments of all orders β ∈ (0, 4/γ²)", citing Rhodes-Vargas RV14
Theorem 2.11), with outer expectations. The family `μb b` is the γ-LQG area measure of `h^b` for each `b > 0`: the
statement quantifies over every family with this property. Outer reading: equal to the printed `E[·]` when the
integrand is measurable; measurability of the normalized masses is not verified in the source. -/
def GMSMassBetaMomentStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
    ∀ μb : ℝ → Ω → Measure ℂ,
      (∀ b : ℝ, 0 < b → IsLQGMeasure P γ
        (fun ω => gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)) (μb b)) →
    ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∀ β : ℝ, 0 < β → β < 4 / γ ^ 2 →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ C : ℝ, 1 < C →
        MatedCRT.outerLIntegral P
          (fun ω => (ENNReal.ofReal (C ^ (-ζ)) * μb (C ^ ζ) ω (Metric.ball 0 1)) ^ β) ≤ M

/-- **Definition 4.5, (4.20)**, GMS arXiv:1705.11161v5 p. 32: `deg_in(H₀) ≤ μ_h(B̄₀)`, almost surely, for the canonical
zero-cone model. The printed text gives its justification in one sentence ("We note that"): the unit-mass segments
`η([a_j, b_j])` have pairwise `μ_h`-null overlaps. The key input, that distinct segments of the curve have `μ_h`-null
intersection, is the area-null-overlap argument written for mesh cells. The bound is cited
as printed; its background proof is not re-opened here. -/
def GMSInnerDegreeBoundStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
    ∀ᵐ ω ∂P, (gmsInnerDegree (η ω)).toENNReal ≤ μ ω (gmsB0 (η ω))

/-- **γ-LQG coordinate change as used in (4.3)**, GMS p. 30, citing formula (2.3) (`f_* μ_{h̃} = μ_h` for `h̃` related
to `h` by a conformal map; the scaling `ψ(z) = R z` gives `h^b`): a.s., `μ_{h^b}(Y) = μ_h(R_b Y)` for every Borel `Y`,
i.e. `μ_h(X) = μ_{h^b}(R_b⁻¹ X)`. This is a transport identity, kept separate from the canonical-law inputs above. -/
def GMSCoordinateChangeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
    ∀ μb : ℝ → Ω → Measure ℂ,
      (∀ b : ℝ, 0 < b → IsLQGMeasure P γ
        (fun ω => gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)) (μb b)) →
    ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P, ∀ Y : Set ℂ, MeasurableSet Y →
      μb b ω Y = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) b : ℝ) : ℂ) * z) '' Y)

/-! ## Canonical BG inputs: arXiv:2211.04891v2 Lemma 3.3 (pp. 23-24) and Theorem 4.1 (p. 32)

Scope. The printed Lemma 3.3 and Theorem 4.1 concern the paper's standing environment: `h` a `γ`-quantum cone, `η` a
whole-plane space-filling SLE_{16/γ²} independent of `h` and parametrized by `μ_h`-area (corrected tex lines 189-195),
and the mated-CRT map of the boundary-length pair (Definition 1.1), identified with the SLE/LQG cell description by
DMS14 Lemma 8.8 (corrected tex lines 207-209). The canonical inputs below are these printed statements for the canonical
law of that environment, carried by `IsCanonicalSLEDecoratedCone`. They do not abbreviate the Draft statements
`UniformConvergenceGreenKernelStmt` and `ConvergenceDivisibleStmt`: those quantify over every `MatedCRTEnv.IsValid`
environment, whose coupling clause is existential (an abstract mating-of-trees coupling with an abstract
imaginary-geometry map `igMap`). They are not statements about the canonical law and are not used here.

Missing carrier (not staged). The canonical comparison realization is a measurable function
of the Brownian pair (DMS14 Theorem 1.9, pp. 26-27, and Theorem 1.11, p. 29; GHMS Theorem 1.1, p. 5, for `γ < √2`). The
canonical inputs apply to it only once `IsCanonicalSLEDecoratedCone 𝒮 γ` holds for that realization, which is not
established here. Exact missing type: a measurable reconstruction `Φ : Path2 → (ℝ → ℂ → ℝ) × C(ℝ, ℂ)` of the circle
averages and the curve from the pair, with `IsCanonicalSLEDecoratedCone 𝒮 γ` for the environment assembled from the pair and
`Φ` (clock and pairing included); no such carrier exists in `MatedCRT/External` or `MatedCRT/Defs`. -/

/-- **Canonical SLE-decorated `γ`-quantum cone with its Brownian boundary pair** (carrier of the canonical BG inputs;
corrected tex lines 189-195 and 207-209; DMS14 Definition 4.10 and Lemma 8.8). Under `P`, the environment `S` has the law
of the paper's standing environment:
* `S.hC`, `S.hcirc` is the circle average embedding of the `γ`-quantum cone (`IsQuantumCone`), `S.μ` is its `γ`-LQG
  measure (`IsLQGMeasure`), and `S.clock` is the LQG clock of planar Brownian motion (`IsLQGClock`);
* `S.η` is a whole-plane space-filling SLE_{16/γ²} independent of `σ(h)` (`𝒮.IsSLE` for the true model `𝒮`, as in
  `MatedCRT/External/SLE.lean`), with `η(0) = 0` and `μ_h(η([a,b])) = b - a` (`IsAreaParametrized`);
* `S.bm` is the boundary-length pair of Definition 1.1: a two-sided two-dimensional Brownian motion with correlation
  `-cos(πγ²/4)` (`IsCorrelatedBM2`), and for each `ε > 0` the Brownian multigraph `S.mult ε` equals the SLE/LQG cell
  multiplicity `cellMult ε (S.η ω)` almost surely (DMS14 Lemma 8.8; the identification stated at corrected tex 207-209).
The clauses are those of `MatedCRTEnv.IsValid` for the standing law, except that the existential mating-of-trees
coupling clause is replaced by the boundary-pair law and the cell identity. No conclusion about the discrete Green
function, the least supersolution or the odometer is included. -/
structure IsCanonicalSLEDecoratedCone (𝒮 : SpaceFillingSLEModel) (γ : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (S : MatedCRTEnv Ω) : Prop where
  /-- `P` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure S.P
  /-- `h` is the circle average embedding of the `γ`-quantum cone (Definition 2.1; DMS14 Definition 4.10). -/
  isQuantumCone : IsQuantumCone γ S.P S.hC S.hcirc
  /-- `μ = μ_h` is the `γ`-LQG measure of `h` (corrected tex eq:measure-lim). -/
  isLQGMeasure : IsLQGMeasure S.P γ S.hcirc S.μ
  /-- `clock` is the LQG clock of planar Brownian motion for `h`, as in `MatedCRTEnv.IsValid`. -/
  isLQGClock : ∀ᵐ ω ∂S.P, ∀ z : ℂ, IsLQGClock planarBrownianMotion γ (S.hcirc ω) z (S.clock ω) ∧
    ∀ᵐ b ∂planarBrownianMotion z, IsTimeChangeClock (S.clock ω b)
  /-- `η` (modulo parametrization) is a whole-plane space-filling SLE_{16/γ²} independent of `h` (corrected tex 189-193). -/
  isSLE : 𝒮.IsSLE S.P S.fieldSigma (16 / γ ^ 2) S.η
  /-- `η(0) = 0` and `μ_h(η([a,b])) = b - a`, almost surely (corrected tex 192). -/
  isAreaParametrized : ∀ᵐ ω ∂S.P, IsAreaParametrized (S.μ ω) (S.η ω)
  /-- The boundary-length pair `bm` of Definition 1.1 is a two-sided correlated Brownian motion. -/
  isBrownianBoundaryPair : MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2 γ (S.P.map S.bm)
  /-- The Brownian mated-CRT multigraph is the SLE/LQG cell multigraph, almost surely, for each cell size
  (DMS14 Lemma 8.8). -/
  isCellIdentity : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂S.P, S.mult ε ω = cellMult ε (S.η ω)

/-- **BG Lemma 3.3, canonical scope** (arXiv:2211.04891v2, Lemma 3.3, pp. 23-24; corrected tex
`lemma:uniform-convergence-of-greens-function`, line 1216; printed (3.12)). For the canonical law
`IsCanonicalSLEDecoratedCone`: for deterministic `r > 0` and `z` with `B_r(z) ⊆ B_ρ`, `y ∈ B_r(z)`, each `δ > 0` and each
`O ⊆ cl(B_r(z)) \ {y}` at positive distance from `y`, with probability tending to `1` as `ε → 0`, the rescaled Green
function `ḡ^ε` satisfies `sup_{x ∈ O} |ḡ^ε(x) - (c₀/6) G_{B_r(z)}(y, x)| ≤ δ`. CORRECTION [C1]: `c₀ = 2/m₀`
(`MatedCRTEnv.c₀`) in place of the printed `m₀`. `G_{B_r(z)}` is the Green function of standard Brownian motion killed on
exiting `B_r(z)` (`greenFunction`). Cited input; not proved here. -/
def BGLemma33CanonicalStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), IsCanonicalSLEDecoratedCone 𝒮 γ S →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → Metric.ball z r ⊆ Metric.ball 0 ρ → y ∈ Metric.ball z r →
  ∀ δ : ℝ, 0 < δ → ∀ O : Set ℂ, O ⊆ Metric.closedBall z r \ {y} → 0 < Metric.infDist y O →
    ProbTendsToOne S.P fun ε => {ω | ∀ x ∈ O,
      |rescale (S.mε ε) ε (S.η ω)
          (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (Metric.ball z r))
            (vertexOf ε (S.η ω) y) a) x -
        S.c₀ / 6 * greenFunction (Metric.ball z r) y x| ≤ δ}

/-- **BG Theorem 4.1, canonical scope** (arXiv:2211.04891v2, Theorem 4.1, p. 32; corrected tex
`theorem:convergence-divisible`, line 1855). For the canonical law `IsCanonicalSLEDecoratedCone`: for each `t > 0` and
`δ > 0`, on the event `{t < T}` (`clusterExitTime` of the cone harmonic ball family `Λ`), the rescaled least supersolution
`w̄^ε_t` of the discrete problem satisfies `P[t < T, sup_{B_ρ} |w̄^ε_t - (c₀/6) w̄^{B_ρ}_t| > δ] → 0`. CORRECTION [C1]:
`c₀ = 2/m₀` (`MatedCRTEnv.c₀`) in place of the printed `m₀`. Cited input; not proved here. -/
def BGTheorem41CanonicalStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), IsCanonicalSLEDecoratedCone 𝒮 γ S →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂S.P, IsConeHarmonicBallFamily (S.μ ω) (Λ ω)) →
  ∀ t : ℝ, 0 < t → ∀ δ : ℝ, 0 < δ →
    Tendsto (fun ε => S.P {ω | t < clusterExitTime (Λ ω) ρ ∧ ∃ x ∈ Metric.ball (0 : ℂ) ρ,
        δ < |rescaledMatedLeastSupersolution S ρ t ε ω x - S.c₀ / 6 * leastSupersolution (S.μ ω) ρ 0 t x|})
      (𝓝[>] 0) (𝓝 0)

/-! ## Internal proved fact (not a published input)

The Chebyshev, dyadic-tail and moment consequences of the Props above are not in this file: they are in
`MatedCRT/Proofs/Sec5/StoppedPoleInnerDegreeMoments.lean`, which imports this file. The lemma below is a fact about the
outer integral. -/

/-- Source-fidelity account of the outer moments: for a measurable integrand the outer integral `outerLIntegral` is the
printed Lebesgue integral. Proof: `g = f` is an admissible majorant, and every measurable majorant `g ≥ f` has
`∫⁻ f ≤ ∫⁻ g`. -/
theorem outerLIntegral_eq_lintegral_of_measurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ≥0∞}
    (hf : Measurable f) : MatedCRT.outerLIntegral P f = ∫⁻ ω, f ω ∂P := by
  unfold MatedCRT.outerLIntegral
  refine le_antisymm ?_ (le_iInf fun g => le_iInf fun _ => le_iInf fun hfg => lintegral_mono hfg)
  exact (iInf_le _ f).trans ((iInf_le _ hf).trans (iInf_le (fun _ : f ≤ f => ∫⁻ ω, f ω ∂P) le_rfl))

/-- Consistency of the α-cone carrier: at `α = γ`, `IsAlphaQuantumCone` is the γ-quantum cone `IsQuantumCone` of
`MatedCRT/Defs/QuantumCone.lean`. The radial laws agree by unfolding, and the other five fields coincide. -/
theorem isAlphaQuantumCone_gamma_iff {Ω : Type*} [MeasurableSpace Ω] (γ : ℝ) (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    IsAlphaQuantumCone γ γ P hC hcirc ↔ IsQuantumCone γ P hC hcirc :=
  ⟨fun h => ⟨h.measurable_pairing, h.measurable_circle, h.ae_continuousOn_circle, h.radial_law, h.indep,
      h.lateral_law⟩,
    fun h => ⟨h.measurable_pairing, h.measurable_circle, h.ae_continuousOn_circle, h.radial_law, h.indep,
      h.lateral_law⟩⟩

end MatedCRT.StoppedCanonicalMoments
