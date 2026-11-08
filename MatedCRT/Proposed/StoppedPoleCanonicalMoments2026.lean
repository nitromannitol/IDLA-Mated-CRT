import Mathlib
import MatedCRT.Defs.Setting
import MatedCRT.Draft.Section3
import MatedCRT.Draft.Section4

/-!
# Canonical published moment inputs of steps2-r3 (GMS arXiv:1705.11161v5, Section 4)

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

Not staged, with reasons (see the fleet report):
* (4.5) of Lemma 4.3: not consumed by the moment route.
* (4.22) of Proposition 4.6: its printed range `p ∈ [1, 4/γ)^2` is malformed; the route derives the inner-degree
  moment from the beta-moment paragraph and (4.6) (r3:2674-2753), never from (4.22).
* (4.25): its printed last bound carries the positive exponent `β(1-ζ)`; it is not imported.

Outer-expectation account (source fidelity). The printed moments of the degree and mass functionals are read as
outer expectations `MatedCRT.outerLIntegral` (Defs/Notation.lean). For a measurable integrand this is the printed
Lebesgue integral (`outerLIntegral_eq_lintegral_of_measurable`, below), so the two readings agree whenever the printed
quantity is measurable. The paper does not verify measurability of `deg_in`, `deg_out`, `DA` or of the normalized masses
`C^{-ζ} μ_{h^{C^ζ}}(𝔻)`; no statement here assumes or proves it, and the outer forms need none. The printed (4.22) and
(4.25) are not imported (see above); the moment route is r3:2674-2753.

Canonical laws. `IsCanonicalZeroConeModel` (GMS, zero cone) and `IsCanonicalSLEDecoratedCone` (BG, `γ`-cone) are
predicates on the joint law of the environment, not hypotheses on an abstract environment. The α-cone predicate
`IsAlphaQuantumCone` is the `IsQuantumCone` of `MatedCRT/Defs/QuantumCone.lean` with the drift parameter `α` in place of
`γ`.

The `…Stmt` declarations are published inputs (explicit hypotheses, not proved here). The internal lemmas at the end are
proved consequences of those inputs (r3:2674-2753); they are not literature inputs and should move to
`MatedCRT/Proofs/` on promotion.
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
i.e. for every `N` there are `K, C₀` with `P[η([-1,1]) ⊄ B_{R_C/8}(0)] ≤ K C^{-N}` for `C ≥ C₀`. The radii are the
cone scale radii `R_C = coneScaleRadius γ h C` of (2.4). Lemma 4.3's other display (4.5) is not staged. -/
def GMSLemma43Eq46Stmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
    ∀ N : ℝ, ∃ K C₀ : ℝ, 1 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
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
intersection, is the area-null-overlap argument written for mesh cells at steps2-r3.tex 1789-1812. The bound is cited
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

Missing carrier (not staged). The canonical comparison realization of steps2-r3 (r3:1912-1945) is a measurable function
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
  (DMS14 Lemma 8.8; corrected tex 207-209; INPUT-REQUESTS IR-A2). -/
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

/-! ## Internal proved consequences (not published inputs)

The lemmas below are proved from the Props above, following the written Chebyshev and tail-integration argument of
r3:2674-2753. They should move to `MatedCRT/Proofs/` on promotion. -/

/-- Source-fidelity account of the outer moments: for a measurable integrand the outer integral `outerLIntegral` is the
printed Lebesgue integral. Proof: `g = f` is an admissible majorant, and every measurable majorant `g ≥ f` has
`∫⁻ f ≤ ∫⁻ g`. -/
theorem outerLIntegral_eq_lintegral_of_measurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ≥0∞}
    (hf : Measurable f) : MatedCRT.outerLIntegral P f = ∫⁻ ω, f ω ∂P := by
  unfold MatedCRT.outerLIntegral
  refine le_antisymm ?_ (le_iInf fun g => le_iInf fun _ => le_iInf fun hfg => lintegral_mono hfg)
  exact (iInf_le _ f).trans ((iInf_le _ hf).trans (iInf_le (fun _ : f ≤ f => ∫⁻ ω, f ω ∂P) le_rfl))

/-- Markov's inequality for the outer integral: `c^β · P[c < Y] ≤ E*[Y^β]` for `β > 0`. -/
theorem outer_markov {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ≥0∞) {β : ℝ} (hβ : 0 < β)
    (c : ℝ≥0∞) :
    c ^ β * P {ω | c < Y ω} ≤ MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) := by
  unfold MatedCRT.outerLIntegral
  refine le_iInf fun G => le_iInf fun hG => le_iInf fun hYG => ?_
  have hsub : {ω | c < Y ω} ⊆ {ω | c ^ β ≤ G ω} := fun ω hω =>
    le_trans (ENNReal.rpow_le_rpow hω.le hβ.le) (hYG ω)
  calc c ^ β * P {ω | c < Y ω} ≤ c ^ β * P {ω | c ^ β ≤ G ω} := by
        gcongr
    _ ≤ ∫⁻ ω, G ω ∂P := mul_meas_ge_le_lintegral hG (c ^ β)

/-- The dyadic identity `(C₀ 2^{j+1})^p · M (C₀ 2^j)^{-q} = 2^p C₀^{p-q} M (2^{p-q})^j`. -/
theorem dyadic_identity (p q M C₀ : ℝ) (hC₀ : 0 < C₀) (j : ℕ) :
    (C₀ * 2 ^ (j + 1)) ^ p * (M * (C₀ * 2 ^ j) ^ (-q)) =
      (2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j := by
  have hx : 0 < C₀ * 2 ^ j := by positivity
  have hsplit : (C₀ * 2 ^ j) ^ (p - q) = C₀ ^ (p - q) * ((2 : ℝ) ^ (p - q)) ^ j := by
    rw [Real.mul_rpow hC₀.le (by positivity), ← Real.rpow_natCast (2 : ℝ) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast ((2 : ℝ) ^ (p - q)) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  have hpow : (C₀ * 2 ^ j) ^ p * (C₀ * 2 ^ j) ^ (-q) = (C₀ * 2 ^ j) ^ (p - q) := by
    rw [← Real.rpow_add hx]
    ring_nf
  have h2 : C₀ * 2 ^ (j + 1) = (C₀ * 2 ^ j) * 2 := by ring
  rw [h2, Real.mul_rpow hx.le (by norm_num : (0 : ℝ) ≤ 2)]
  calc (C₀ * 2 ^ j) ^ p * 2 ^ p * (M * (C₀ * 2 ^ j) ^ (-q))
      = 2 ^ p * M * ((C₀ * 2 ^ j) ^ p * (C₀ * 2 ^ j) ^ (-q)) := by ring
    _ = 2 ^ p * M * (C₀ ^ (p - q) * ((2 : ℝ) ^ (p - q)) ^ j) := by rw [hpow, hsplit]
    _ = (2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j := by ring

/-- The dyadic series `∑_j 2^{(j+1)p}·(M (C₀2^j)^{-q} + K (C₀2^j)^{-N})` is finite when `p < q` and `p < N`. -/
theorem dyadic_tail_series_lt_top {p q N C₀ M K : ℝ} (hpq : p < q) (hpN : p < N) (hC₀ : 0 < C₀)
    (hM : 0 ≤ M) (hK : 0 ≤ K) :
    ∑' j : ℕ, ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p) *
      (ENNReal.ofReal (M * (C₀ * 2 ^ j) ^ (-q)) + ENNReal.ofReal (K * (C₀ * 2 ^ j) ^ (-N))) < ⊤ := by
  have hr1 : (0 : ℝ) ≤ (2 : ℝ) ^ (p - q) := by positivity
  have hr1' : (2 : ℝ) ^ (p - q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr2 : (0 : ℝ) ≤ (2 : ℝ) ^ (p - N) := by positivity
  have hr2' : (2 : ℝ) ^ (p - N) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ j : ℕ, ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p) *
      (ENNReal.ofReal (M * (C₀ * 2 ^ j) ^ (-q)) + ENNReal.ofReal (K * (C₀ * 2 ^ j) ^ (-N))) =
      ENNReal.ofReal ((2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j) +
        ENNReal.ofReal ((2 ^ p * C₀ ^ (p - N) * K) * ((2 : ℝ) ^ (p - N)) ^ j) := by
    intro j
    have hx1 : 0 ≤ (C₀ * 2 ^ (j + 1)) ^ p := by positivity
    have hx2 : 0 ≤ M * (C₀ * 2 ^ j) ^ (-q) := by positivity
    have hx3 : 0 ≤ K * (C₀ * 2 ^ j) ^ (-N) := by positivity
    have e1 := dyadic_identity p q M C₀ hC₀ j
    have e2 := dyadic_identity p N K C₀ hC₀ j
    have n1 : 0 ≤ (2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j := by positivity
    have n2 : 0 ≤ (2 ^ p * C₀ ^ (p - N) * K) * ((2 : ℝ) ^ (p - N)) ^ j := by positivity
    rw [← ENNReal.ofReal_add hx2 hx3, ← ENNReal.ofReal_mul hx1,
      ← ENNReal.ofReal_add n1 n2]
    congr 1
    rw [mul_add, e1, e2]
  simp only [hterm]
  rw [ENNReal.tsum_add]
  have s1 : Summable (fun j : ℕ => (2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j) :=
    (summable_geometric_of_lt_one hr1 hr1').mul_left _
  have s2 : Summable (fun j : ℕ => (2 ^ p * C₀ ^ (p - N) * K) * ((2 : ℝ) ^ (p - N)) ^ j) :=
    (summable_geometric_of_lt_one hr2 hr2').mul_left _
  have p1 : ∀ j : ℕ, 0 ≤ (2 ^ p * C₀ ^ (p - q) * M) * ((2 : ℝ) ^ (p - q)) ^ j := fun j => by
    have : 0 ≤ M := hM
    positivity
  have p2 : ∀ j : ℕ, 0 ≤ (2 ^ p * C₀ ^ (p - N) * K) * ((2 : ℝ) ^ (p - N)) ^ j := fun j => by
    positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg p1 s1, ← ENNReal.ofReal_tsum_of_nonneg p2 s2]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

/-- Tail-to-moment lemma (r3:2674-2753, the Chebyshev and tail-integration step). If `P[X > C] ≤ M C^{-q} + K C^{-N}`
for all `C ≥ C₀`, with `p < q` and `p < N`, then the outer `p`-th moment of `X` is finite. The majorant uses measurable
supersets of the dyadic level sets `{X > C₀ 2^k}`, so no measurability of `X` is assumed. -/
theorem tail_moment_outer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ≥0∞) {p q N C₀ M K : ℝ} (hp : 0 < p) (hpq : p < q) (hpN : p < N) (hC₀ : 0 < C₀)
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (htail : ∀ C : ℝ, C₀ ≤ C → P {ω | ENNReal.ofReal C < X ω} ≤
      ENNReal.ofReal (M * C ^ (-q)) + ENNReal.ofReal (K * C ^ (-N))) :
    MatedCRT.outerLIntegral P (fun ω => X ω ^ p) < ⊤ := by
  classical
  have hge : ∀ k : ℕ, C₀ ≤ C₀ * 2 ^ k := fun k =>
    le_mul_of_one_le_right hC₀.le (one_le_pow₀ (by norm_num))
  have hsup : ∀ k : ℕ, ∃ B : Set Ω, MeasurableSet B ∧
      {ω | ENNReal.ofReal (C₀ * 2 ^ k) < X ω} ⊆ B ∧
      P B = P {ω | ENNReal.ofReal (C₀ * 2 ^ k) < X ω} := fun k =>
    ⟨_, measurableSet_toMeasurable _ _, subset_toMeasurable _ _, measure_toMeasurable _⟩
  choose A hAm hAsub hAeq using hsup
  have hAb : ∀ k : ℕ, P (A k) ≤ ENNReal.ofReal (M * (C₀ * 2 ^ k) ^ (-q)) +
      ENNReal.ofReal (K * (C₀ * 2 ^ k) ^ (-N)) := fun k => by
    rw [hAeq k]
    exact htail _ (hge k)
  have hbd_tend : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (M * (C₀ * 2 ^ k) ^ (-q)) +
      ENNReal.ofReal (K * (C₀ * 2 ^ k) ^ (-N))) Filter.atTop (nhds 0) := by
    have hL : Filter.Tendsto (fun k : ℕ => C₀ * 2 ^ k) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).const_mul_atTop hC₀
    have h1 : Filter.Tendsto (fun k : ℕ => M * (C₀ * 2 ^ k) ^ (-q)) Filter.atTop (nhds 0) := by
      have := ((tendsto_rpow_neg_atTop (show 0 < q by linarith)).comp hL).const_mul M
      simpa using this
    have h2 : Filter.Tendsto (fun k : ℕ => K * (C₀ * 2 ^ k) ^ (-N)) Filter.atTop (nhds 0) := by
      have := ((tendsto_rpow_neg_atTop (show 0 < N by linarith)).comp hL).const_mul K
      simpa using this
    simpa using (ENNReal.tendsto_ofReal h1).add (ENNReal.tendsto_ofReal h2)
  have hTop : P {ω | X ω = ⊤} = 0 := by
    refine le_antisymm ?_ zero_le
    refine ge_of_tendsto' hbd_tend fun k => ?_
    refine le_trans (measure_mono ?_) (hAb k)
    intro ω hω
    have hω' : ENNReal.ofReal (C₀ * 2 ^ k) < X ω := by
      rw [show X ω = ⊤ from hω]
      exact ENNReal.ofReal_lt_top
    exact hAsub k hω'
  obtain ⟨Z, hZm, hZsub, hZeq⟩ : ∃ Z : Set Ω, MeasurableSet Z ∧ {ω | X ω = ⊤} ⊆ Z ∧
      P Z = P {ω | X ω = ⊤} :=
    ⟨_, measurableSet_toMeasurable _ _, subset_toMeasurable _ _, measure_toMeasurable _⟩
  have hZ0 : P Z = 0 := by rw [hZeq, hTop]
  have hterm_m : ∀ j : ℕ, Measurable ((A j).indicator
      (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p))) := fun j =>
    measurable_const.indicator (hAm j)
  obtain ⟨H, hHdef⟩ : ∃ H : Ω → ℝ≥0∞, ∀ ω, H ω = ENNReal.ofReal (C₀ ^ p) +
      (∑' j : ℕ, (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω) +
      Z.indicator (fun _ => (⊤ : ℝ≥0∞)) ω := ⟨_, fun ω => rfl⟩
  have hHm : Measurable H := by
    have hfun : H = fun ω => (ENNReal.ofReal (C₀ ^ p) +
        ∑' j : ℕ, (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω) +
        Z.indicator (fun _ => (⊤ : ℝ≥0∞)) ω := funext hHdef
    rw [hfun]
    exact (measurable_const.add (Measurable.tsum fun j => hterm_m j)).add
      (measurable_const.indicator hZm)
  have hcore : ∀ ω, ω ∉ Z → X ω ^ p ≤ ENNReal.ofReal (C₀ ^ p) +
      ∑' j : ℕ, (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω := by
    intro ω hZω
    have hXω : X ω ≠ ⊤ := fun h => hZω (hZsub (show ω ∈ {ω | X ω = ⊤} from h))
    by_cases hc : X ω ≤ ENNReal.ofReal C₀
    · calc X ω ^ p ≤ (ENNReal.ofReal C₀) ^ p := ENNReal.rpow_le_rpow hc hp.le
        _ = ENNReal.ofReal (C₀ ^ p) := ENNReal.ofReal_rpow_of_nonneg hC₀.le hp.le
        _ ≤ _ := le_self_add
    · rw [not_le] at hc
      have hex : ∃ j : ℕ, X ω ≤ ENNReal.ofReal (C₀ * 2 ^ (j + 1)) := by
        obtain ⟨n, hn⟩ := (((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).const_mul_atTop hC₀).eventually_gt_atTop
          ((X ω).toReal)).exists
        refine ⟨n, ?_⟩
        rw [← ENNReal.ofReal_toReal hXω]
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : C₀ * 2 ^ n ≤ C₀ * 2 ^ (n + 1) := by
          apply mul_le_mul_of_nonneg_left _ hC₀.le
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      have hk := Nat.find_spec hex
      have hlt : ENNReal.ofReal (C₀ * 2 ^ Nat.find hex) < X ω := by
        rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
        · rw [h0]
          simpa using hc
        · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
          have hmin : ¬ X ω ≤ ENNReal.ofReal (C₀ * 2 ^ (j + 1)) := Nat.find_min hex (by omega)
          rw [hj]
          exact not_le.mp hmin
      have hωA : ω ∈ A (Nat.find hex) := hAsub _ hlt
      calc X ω ^ p ≤ (ENNReal.ofReal (C₀ * 2 ^ (Nat.find hex + 1))) ^ p :=
            ENNReal.rpow_le_rpow hk hp.le
        _ = ENNReal.ofReal ((C₀ * 2 ^ (Nat.find hex + 1)) ^ p) :=
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le
        _ = (A (Nat.find hex)).indicator
              (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (Nat.find hex + 1)) ^ p)) ω :=
            (Set.indicator_of_mem hωA (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (Nat.find hex + 1)) ^ p))).symm
        _ ≤ ∑' j : ℕ, (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω :=
            ENNReal.le_tsum (f := fun j => (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω) (Nat.find hex)
        _ ≤ _ := le_add_self
  have hpt : ∀ ω, X ω ^ p ≤ H ω := by
    intro ω
    by_cases hZω : ω ∈ Z
    · rw [hHdef ω, Set.indicator_of_mem hZω, add_top]
      exact le_top
    · rw [hHdef ω]
      exact le_trans (hcore ω hZω) le_self_add
  have hout : MatedCRT.outerLIntegral P (fun ω => X ω ^ p) ≤ ∫⁻ ω, H ω ∂P := by
    unfold MatedCRT.outerLIntegral
    exact iInf_le_of_le H (iInf_le_of_le hHm (iInf_le_of_le (fun ω => hpt ω) le_rfl))
  have hint : ∫⁻ ω, H ω ∂P = ENNReal.ofReal (C₀ ^ p) +
      ∑' j : ℕ, ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p) * P (A j) := by
    have hfun : H = fun ω => (ENNReal.ofReal (C₀ ^ p) +
        ∑' j : ℕ, (A j).indicator (fun _ => ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p)) ω) +
        Z.indicator (fun _ => (⊤ : ℝ≥0∞)) ω := funext fun ω => by rw [hHdef ω, add_assoc]
    rw [hfun, lintegral_add_right _ (measurable_const.indicator hZm),
      lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_tsum fun j => (hterm_m j).aemeasurable, lintegral_indicator_const hZm, hZ0,
      mul_zero, add_zero]
    congr 1
    refine tsum_congr fun j => ?_
    rw [lintegral_indicator_const (hAm j)]
  have hfin : ENNReal.ofReal (C₀ ^ p) + ∑' j : ℕ, ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p) * P (A j) < ⊤ := by
    refine ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, lt_of_le_of_lt (ENNReal.tsum_le_tsum fun j => ?_)
      (dyadic_tail_series_lt_top hpq hpN hC₀ hM hK)⟩
    gcongr
    exact hAb j
  calc MatedCRT.outerLIntegral P (fun ω => X ω ^ p) ≤ ∫⁻ ω, H ω ∂P := hout
    _ = ENNReal.ofReal (C₀ ^ p) + ∑' j : ℕ, ENNReal.ofReal ((C₀ * 2 ^ (j + 1)) ^ p) * P (A j) := hint
    _ < ⊤ := hfin

/-! ## Consequences of the published inputs: the inner-degree moment (r3:2674-2753) -/

/-- Geometry of the good event: if `η([-1,1]) ⊂ B_{R/8}(0)` and `η` is continuous, then `R > 0` and the closed ball
`B̄₀` of (4.19) lies in the open ball `B_R(0)`. A point `x₀` of maximal norm on the compact `η([-1,1])` gives
`diam η([-1,1]) ≤ 2 ‖x₀‖ < R/4`. -/
theorem gmsB0_subset_ball {η : ℝ → ℂ} (hη : Continuous η) {R : ℝ}
    (hE : η '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (R / 8)) :
    0 < R ∧ gmsB0 η ⊆ Metric.ball 0 R := by
  have hK : IsCompact (η '' Set.Icc (-1) 1) := isCompact_Icc.image hη
  have hne : (η '' Set.Icc (-1) 1).Nonempty := ⟨η 0, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
  obtain ⟨x₀, hx₀K, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have hx₀ : ‖x₀‖ < R / 8 := by
    have h := hE hx₀K
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hdiam : Metric.diam (η '' Set.Icc (-1) 1) ≤ 2 * ‖x₀‖ := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy => ?_
    have hx' : ‖x‖ ≤ ‖x₀‖ := isMaxOn_iff.mp hmax x hx
    have hy' : ‖y‖ ≤ ‖x₀‖ := isMaxOn_iff.mp hmax y hy
    rw [dist_eq_norm]
    linarith [norm_sub_le x y]
  have hR : 0 < R := by
    have := norm_nonneg x₀
    linarith
  refine ⟨hR, fun z hz => ?_⟩
  unfold gmsB0 at hz
  have hz' : dist z 0 ≤ 4 * Metric.diam (η '' Set.Icc (-1) 1) := Metric.mem_closedBall.mp hz
  rw [dist_zero_right] at hz'
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-- The image of the unit ball under multiplication by a positive real `R` is the ball of radius `R`. -/
theorem image_mul_ball_one {R : ℝ} (hR : 0 < R) :
    (fun z : ℂ => (R : ℂ) * z) '' Metric.ball 0 1 = Metric.ball 0 R := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hw
    rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact mul_lt_of_lt_one_right hR hw
  · intro hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    refine ⟨z / R, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
        div_lt_iff₀ hR]
      linarith
    · field_simp

/-- Pointwise inclusion of the level event on the good set: if `x > C` and `x ≤ μ_h(B̄₀)` with `η([-1,1]) ⊂ B_{R/8}(0)`,
then `C^{1-ζ} < C^{-ζ} μ_{h^b}(𝔻)` for `b` with `R = R_b` (the mass identity `μ_{h^b}(𝔻) = μ_h(B_R(0))` of (2.3)). -/
theorem pointwise_tail_bound {η : ℝ → ℂ} (hη : Continuous η) {R C ζ : ℝ} (hC1 : 1 < C) (_hζ0 : 0 < ζ)
    {μω : Measure ℂ} {Zω : ℝ≥0∞} (hZ : Zω = μω ((fun z : ℂ => (R : ℂ) * z) '' Metric.ball 0 1))
    {x : ℝ≥0∞} (hx : ENNReal.ofReal C < x) (hxle : x ≤ μω (gmsB0 η))
    (hE : η '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (R / 8)) :
    ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * Zω := by
  obtain ⟨hR, hsub⟩ := gmsB0_subset_ball hη hE
  have h1 : μω (gmsB0 η) ≤ μω (Metric.ball 0 R) := measure_mono hsub
  rw [← image_mul_ball_one hR] at h1
  have hmass : x ≤ Zω := by
    rw [hZ]
    exact hxle.trans h1
  have hlt : ENNReal.ofReal C < Zω := lt_of_lt_of_le hx hmass
  have hC0 : 0 < C := by linarith
  have hpos : 0 < ENNReal.ofReal (C ^ (-ζ)) := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hC0 _)
  have hfin : ENNReal.ofReal (C ^ (-ζ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsplit : ENNReal.ofReal (C ^ (1 - ζ)) = ENNReal.ofReal (C ^ (-ζ)) * ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hC0.le _)]
    congr 1
    rw [show (1 - ζ) = -ζ + 1 by ring, Real.rpow_add hC0, Real.rpow_one]
  rw [hsplit, mul_comm (ENNReal.ofReal (C ^ (-ζ))) (ENNReal.ofReal C), mul_comm (ENNReal.ofReal (C ^ (-ζ))) Zω]
  exact ENNReal.mul_lt_mul_left hpos.ne' hfin hlt

/-- The Markov step for the normalized masses: if `E*[Y^β] ≤ M < ∞`, then `P[t < Y] ≤ M · t^{-β}` (outer
probability, `t > 0`). This is the Chebyshev inequality of r3:2674-2753. -/
theorem markov_power_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ≥0∞) {β t : ℝ} (hβ : 0 < β)
    (ht : 0 < t) {M : ℝ≥0∞} (hMfin : M < ⊤) (hbd : MatedCRT.outerLIntegral P (fun ω => Y ω ^ β) ≤ M) :
    P {ω | ENNReal.ofReal t < Y ω} ≤ ENNReal.ofReal (M.toReal * t ^ (-β)) := by
  have hmk := outer_markov P Y hβ (ENNReal.ofReal t)
  rw [ENNReal.ofReal_rpow_of_nonneg ht.le hβ.le] at hmk
  have hprod : ENNReal.ofReal (t ^ (-β)) * ENNReal.ofReal (t ^ β) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht, neg_add_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  have hM' : ENNReal.ofReal M.toReal = M := ENNReal.ofReal_toReal hMfin.ne
  calc P {ω | ENNReal.ofReal t < Y ω}
      = ENNReal.ofReal (t ^ (-β)) * ENNReal.ofReal (t ^ β) * P {ω | ENNReal.ofReal t < Y ω} := by
        rw [hprod, one_mul]
    _ = ENNReal.ofReal (t ^ (-β)) * (ENNReal.ofReal (t ^ β) * P {ω | ENNReal.ofReal t < Y ω}) := by
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (t ^ (-β)) * M := by
        gcongr
        exact hmk.trans hbd
    _ = ENNReal.ofReal (t ^ (-β)) * ENNReal.ofReal M.toReal := by rw [hM']
    _ = ENNReal.ofReal (M.toReal * t ^ (-β)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_comm]

/-- The tail bound at one level `C > 1`, from the almost-sure inputs: the inner-degree bound (4.20), continuity of `η`
and the coordinate change (2.3) at `b = C^ζ`. Off the null set, `deg_in > C` forces `η([-1,1])` out of `B_{R/8}(0)`
or the mass `C^{-ζ} μ_{h^b}(𝔻)` above `C^{1-ζ}`.

Assumptions, exactly as used: `hX` (the inner-degree bound (4.20), almost surely), `hcont` (continuity of `η`, almost
surely) and `hcoord`, the transport identity at the single level `b = C^ζ` and the single ball `𝔻`: almost surely
`μbC ω 𝔻 = μ_h(R 𝔻)` with `R = coneScaleRadius γ (hcirc ω) (C^ζ)`. The measure-valued family `μbC` is an arbitrary
random measure satisfying `hcoord`; it is not assumed to be the LQG measure of `h^b`. No measurability of `X` or of
`deg_in` is assumed. -/
theorem tail_level_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ ζ C : ℝ} (hC1 : 1 < C) (hζ0 : 0 < ζ)
    {X : Ω → ℝ≥0∞} {η : Ω → ℝ → ℂ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {μbC : Ω → Measure ℂ}
    (hX : ∀ᵐ ω ∂P, X ω ≤ μ ω (gmsB0 (η ω))) (hcont : ∀ᵐ ω ∂P, Continuous (η ω))
    (hcoord : ∀ᵐ ω ∂P, μbC ω (Metric.ball 0 1) =
      μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1)) :
    P {ω | ENNReal.ofReal C < X ω} ≤
      P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} +
      P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)} := by
  have hgood : ∀ᵐ ω ∂P, (X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
      μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1) :=
    (hX.and hcont).and hcoord
  have hN0 : P {ω | ¬ ((X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
      μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1))} = 0 :=
    ae_iff.mp hgood
  have hsub : {ω | ENNReal.ofReal C < X ω} ⊆
      {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} ∪
      ({ω | ¬ ((X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
          μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1))} ∪
        {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)}) := by
    intro ω hω
    by_cases hE : η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8)
    · by_cases hg : (X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
          μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1)
      · exact Or.inr (Or.inr (pointwise_tail_bound hg.1.2 hC1 hζ0 hg.2 hω hg.1.1 hE))
      · exact Or.inr (Or.inl hg)
    · exact Or.inl hE
  calc P {ω | ENNReal.ofReal C < X ω}
      ≤ P ({ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} ∪
          ({ω | ¬ ((X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
          μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1))} ∪
        {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)})) :=
        measure_mono hsub
    _ ≤ P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} +
          P ({ω | ¬ ((X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
          μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1))} ∪
        {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)}) :=
        measure_union_le _ _
    _ ≤ P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} +
          (P {ω | ¬ ((X ω ≤ μ ω (gmsB0 (η ω)) ∧ Continuous (η ω)) ∧
          μbC ω (Metric.ball 0 1) = μ ω ((fun z : ℂ => ((coneScaleRadius γ (hcirc ω) (C ^ ζ) : ℝ) : ℂ) * z) '' Metric.ball 0 1))} +
        P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)}) :=
        add_le_add le_rfl (measure_union_le _ _)
    _ = P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} +
          P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μbC ω (Metric.ball 0 1)} := by
        rw [hN0, zero_add]

/-- **Inner-degree moment from the published inputs** (r3:2674-2753). For the canonical zero-cone model, given the
staged Lemma 4.3 (4.6), the beta-moment paragraph, the coordinate change (2.3) and the inner-degree bound (4.20), the
outer `p`-th moment of `deg_in(H₀)` is finite for `1 ≤ p < 4/γ²`. The printed (4.22) range `[1, 4/γ)^2` is not used;
the conclusion is the range the written proof derives.

Assumptions, exactly as used: `hLem`, `hBeta`, `hCoord` and `hInner` are the staged printed Props (cited, not proved);
`hM` is the canonical zero-cone predicate; `hμb` supplies the rescaled-measure family `μb`: for every `b > 0`, `μb b` is
the `γ`-LQG measure of the rescaled circle averages `gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)`,
and it is the family on which `hBeta` and `hCoord` are stated. The conclusion is an outer moment; measurability of
`deg_in(H₀)` is neither assumed nor proved. -/
theorem gms_innerDegree_moment {𝒮 : SpaceFillingSLEModel}
    (hLem : GMSLemma43Eq46Stmt 𝒮) (hBeta : GMSMassBetaMomentStmt 𝒮)
    (hCoord : GMSCoordinateChangeStmt 𝒮) (hInner : GMSInnerDegreeBoundStmt 𝒮)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {η : Ω → ℝ → ℂ}
    (hM : IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η)
    (μb : ℝ → Ω → Measure ℂ)
    (hμb : ∀ b : ℝ, 0 < b → IsLQGMeasure P γ
      (fun ω => gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)) (μb b))
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 4 / γ ^ 2) :
    MatedCRT.outerLIntegral P (fun ω => (gmsInnerDegree (η ω)).toENNReal ^ p) < ⊤ := by
  have := hM.isProbabilityMeasure
  have hInnerM := hInner γ hγ0 hγ2 Ω P hC hcirc μ η hM
  have hp0 : 0 < p := by linarith
  -- exponents: p < β < 4/γ², 0 < ζ < 1 - p/β, and q = β(1-ζ) = (β+p)/2 > p
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (p + 4 / γ ^ 2) / 2 := ⟨_, rfl⟩
  have hβp : p < β := by rw [hβdef]; linarith
  have hβ4 : β < 4 / γ ^ 2 := by rw [hβdef]; linarith
  have hβ0 : 0 < β := by linarith
  have hβne : β ≠ 0 := hβ0.ne'
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℝ, ζ = (1 - p / β) / 2 := ⟨_, rfl⟩
  have hpβ : p / β < 1 := (div_lt_one hβ0).mpr hβp
  have hpβ0 : 0 < p / β := div_pos hp0 hβ0
  have hζ0 : 0 < ζ := by rw [hζdef]; linarith
  have hζ1 : ζ < 1 := by rw [hζdef]; linarith
  have hζne : ζ ≠ 0 := hζ0.ne'
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (β + p) / 2 := ⟨_, rfl⟩
  have hq : β * (1 - ζ) = q := by
    rw [hζdef, hqdef]
    field_simp
    ring
  have hpq : p < q := by rw [hqdef]; linarith
  obtain ⟨Nt, hNtdef⟩ : ∃ Nt : ℝ, Nt = p + 1 := ⟨_, rfl⟩
  have hpNt : p < Nt := by rw [hNtdef]; linarith
  -- constants of the staged inputs
  obtain ⟨Mb, hMbfin, hMbd⟩ := hBeta γ hγ0 hγ2 Ω P hC hcirc μ η hM μb hμb ζ hζ0 hζ1 β hβ0 hβ4
  obtain ⟨K, C₁, hC₁, hLemb⟩ := hLem γ hγ0 hγ2 Ω P hC hcirc μ η hM (Nt / ζ)
  have hMr0 : 0 ≤ Mb.toReal := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  -- the threshold: `C ≥ C₀` gives `C > 1` and `C^ζ ≥ C₁`
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℝ, C₀ = max (C₁ ^ (1 / ζ)) 2 := ⟨_, rfl⟩
  have hC₀two : (2 : ℝ) ≤ C₀ := by rw [hC₀def]; exact le_max_right _ _
  have hC₀pos : 0 < C₀ := by linarith
  have hC₀root : C₁ ^ (1 / ζ) ≤ C₀ := by rw [hC₀def]; exact le_max_left _ _
  have htail : ∀ C : ℝ, C₀ ≤ C → P {ω | ENNReal.ofReal C < (gmsInnerDegree (η ω)).toENNReal} ≤
      ENNReal.ofReal (Mb.toReal * C ^ (-q)) + ENNReal.ofReal (max K 0 * C ^ (-Nt)) := by
    intro C hCC
    have hC2 : 2 ≤ C := by linarith
    have hC1' : 1 < C := by linarith
    have hC0 : 0 < C := by linarith
    have hC_ge : C₁ ^ (1 / ζ) ≤ C := by linarith
    have hCζ : C₁ ≤ C ^ ζ := by
      calc C₁ = (C₁ ^ (1 / ζ)) ^ ζ := by
            rw [← Real.rpow_mul (show (0 : ℝ) ≤ C₁ by linarith), one_div, inv_mul_cancel₀ hζne,
              Real.rpow_one]
        _ ≤ C ^ ζ := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hC_ge hζ0.le
    have hbpos : 0 < C ^ ζ := Real.rpow_pos_of_pos hC0 _
    -- almost-sure inputs at `b = C^ζ`
    have hcoord := (hCoord γ hγ0 hγ2 Ω P hC hcirc μ η hM μb hμb (C ^ ζ) hbpos).mono
      fun ω h => h (Metric.ball 0 1) measurableSet_ball
    have hcont := hM.isAreaParametrized.mono fun ω h => h.1
    have hT := tail_level_bound P hC1' hζ0 (X := fun ω => (gmsInnerDegree (η ω)).toENNReal)
      hInnerM hcont hcoord
    -- the event `η([-1,1]) ⊄ B_{R/8}` at radius `C^ζ`
    have hpow : (C ^ ζ) ^ (-(Nt / ζ)) = C ^ (-Nt) := by
      rw [← Real.rpow_mul hC0.le]
      congr 1
      field_simp
    have hE : P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} ≤
        ENNReal.ofReal (max K 0 * C ^ (-Nt)) := by
      refine (hLemb (C ^ ζ) hCζ).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hpow]
      exact mul_le_mul_of_nonneg_right (le_max_left K 0) (Real.rpow_nonneg hC0.le _)
    -- the mass event, by the Chebyshev inequality for the outer integral
    have hTm : P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μb (C ^ ζ) ω (Metric.ball 0 1)} ≤
        ENNReal.ofReal (Mb.toReal * C ^ (-q)) := by
      have h := markov_power_bound P (fun ω => ENNReal.ofReal (C ^ (-ζ)) * μb (C ^ ζ) ω (Metric.ball 0 1))
        hβ0 (Real.rpow_pos_of_pos hC0 (1 - ζ)) hMbfin (hMbd C hC1')
      have hpow2 : (C ^ (1 - ζ)) ^ (-β) = C ^ (-q) := by
        rw [← Real.rpow_mul hC0.le, ← hq]
        congr 1
        ring
      rw [hpow2] at h
      exact h
    calc P {ω | ENNReal.ofReal C < (gmsInnerDegree (η ω)).toENNReal}
        ≤ P {ω | ¬ (η ω '' Set.Icc (-1) 1 ⊆ Metric.ball 0 (coneScaleRadius γ (hcirc ω) (C ^ ζ) / 8))} +
          P {ω | ENNReal.ofReal (C ^ (1 - ζ)) < ENNReal.ofReal (C ^ (-ζ)) * μb (C ^ ζ) ω (Metric.ball 0 1)} := hT
      _ ≤ ENNReal.ofReal (max K 0 * C ^ (-Nt)) + ENNReal.ofReal (Mb.toReal * C ^ (-q)) := add_le_add hE hTm
      _ = ENNReal.ofReal (Mb.toReal * C ^ (-q)) + ENNReal.ofReal (max K 0 * C ^ (-Nt)) := add_comm _ _
  exact tail_moment_outer P (fun ω => (gmsInnerDegree (η ω)).toENNReal) hp0 hpq hpNt hC₀pos hMr0 hK0 htail

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
