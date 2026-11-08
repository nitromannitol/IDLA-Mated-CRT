import Mathlib
import MatedCRT.Defs.Setting

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

Not staged, with reasons (see the fleet report):
* (4.5) of Lemma 4.3: not consumed by the moment route.
* (4.22) of Proposition 4.6: its printed range `p ∈ [1, 4/γ)^2` is malformed; the route derives the inner-degree
  moment from the beta-moment paragraph and (4.6) (r3:2674-2753), never from (4.22).
* (4.25): its printed last bound carries the positive exponent `β(1-ζ)`; it is not imported.

The canonical zero-cone law is carried by `IsCanonicalZeroConeModel` (a predicate on the joint law, not a
hypothesis on any abstract environment). The α-cone predicate `IsAlphaQuantumCone` is the `IsQuantumCone` of
`MatedCRT/Defs/QuantumCone.lean` with the drift parameter `α` in place of `γ`; `IsAlphaQuantumCone γ γ` is that
γ-quantum cone (not proved here). No proofs appear in this file: every `…Stmt` is a published input.
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

/-- **Proposition 4.4, (4.14)**, GMS p. 31: `E[DA(H₀)^p] < ∞` for all `p ≥ 1`. -/
def GMSProposition44Stmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
    ∀ p : ℝ, 1 ≤ p → ∫⁻ ω, gmsDA (η ω) ^ p ∂P < ⊤

/-- **Proposition 4.6, (4.23)**, GMS p. 33: `E[deg_out(H₀)^p] < ∞` for all `p ≥ 1`. (The inner-degree display (4.22)
is not staged; see the module docstring.) -/
def GMSProposition46OuterStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
    ∀ p : ℝ, 1 ≤ p → ∫⁻ ω, (gmsOuterDegree (η ω)).toENNReal ^ p ∂P < ⊤

/-- **Uniform normalized-mass beta-moment paragraph**, GMS p. 33, immediately before (4.25) (proof of Proposition
4.6): for fixed `ζ ∈ (0, 1)` and `β ∈ (0, 4/γ²)`, the normalized masses `Y_C := C^{-ζ} μ_{h^{C^ζ}}(𝔻)` satisfy
`sup_{C > 1} E[Y_C^β] < ∞` ("finite, C-independent moments of all orders β ∈ (0, 4/γ²)", citing Rhodes-Vargas RV14
Theorem 2.11). The family `μb b` is the γ-LQG area measure of `h^b` for each `b > 0` (`IsLQGMeasure`). -/
def GMSMassBetaMomentStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (η : Ω → ℝ → ℂ),
    IsCanonicalZeroConeModel 𝒮 γ P hC hcirc μ η →
    ∀ μb : ℝ → Ω → Measure ℂ,
      (∀ b : ℝ, 0 < b → IsLQGMeasure P γ
        (fun ω => gmsRescaledCircle γ (hcirc ω) (coneScaleRadius γ (hcirc ω) b)) (μb b)) →
    ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∀ β : ℝ, 0 < β → β < 4 / γ ^ 2 →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ C : ℝ, 1 < C →
        ∫⁻ ω, (ENNReal.ofReal (C ^ (-ζ)) * μb (C ^ ζ) ω (Metric.ball 0 1)) ^ β ∂P ≤ M

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

end MatedCRT.StoppedCanonicalMoments
