import MatedCRT.Draft.Section2
import MatedCRT.Draft.Section3

/-!
# Lemma 3.1 (lemma:discrete-potential-tightness, tex line 976; proof lines 1017-1087): steps

## The statement proved: `DiscretePotentialTightnessCorrectedStmt`

It is the draft `DiscretePotentialTightnessStmt` (MatedCRT/Draft/Section3.lean) with three changes.

* **(N1, review-L32)** The Hölder boundary data of the "moreover" part are `ε⁻¹`-scaled,
  `|u^ε(a) - u^ε(b)| ≤ C' ε⁻¹ (ε ∨ |η(a) - η(b)|)^χ`, as `u^ε` has order `ε⁻¹`. This strengthens the lemma (the
  hypothesis is weaker for `ε < 1`). It is what Lemma 3.5 needs, with data `m_ε φ`.
* **`D` open.** The draft allows every connected `D ⊆ B_ρ`. For a non-open `D` it is false. Take
  `D = cl(B_{ρ/2})` and `O = D`, which is compact with `cl(O) ⊆ D`. Let `u^ε` be the harmonic extension to
  `V^ε(D) \ V^ε(∂D)` of the data `ε⁻¹ sin(Re η(a) / ε^{1/20})` on `V^ε(∂D)`, a function of `(h, η)` with `Δ^ε u^ε = 0`
  and `|u^ε| ≤ ε⁻¹`. On `∂D` the cells have diameter `o(ε^{1/20})` (Lemma 2.8), so `ū^ε(x) = (ε m_ε)⁻¹ sin(Re x /
  ε^{1/20}) + o(1)` uniformly on `∂D`, with `(ε m_ε)⁻¹ ≍ 1`. No subsequence converges uniformly on `∂D ⊆ O` to a
  continuous limit. The paper's `O ⋐ D` and its proof (line 1034, `O + B_{δ₁} ⋐ D`) take `O` inside the interior,
  and every use has `D` open (balls, `B_ρ`).
* **(N3, review-L32)** The proof applies Lemmas 2.18 and 3.2 at the random scales `ε ∈ E(ω)`, but these lemmas bound
  `P[failure at ε]` for deterministic `ε` only. The repair: the scales `E ω n` take values in a deterministic
  sequence `e` with `∑_j e_j^p < ∞` for every `p > 0` (`IsPolySummableScales`). Every deterministic sequence `→ 0`
  has such a subsequence (e.g. `e_j ≤ 2^{-j}`), and random subsequences of it are allowed (line 1460).

## The proof

The paper's proof, made explicit.

* **Analytic part** (`TightnessEquicontinuityStep`, lines 1028-1085): almost surely, for every compact `K ⊆ D`, the
  functions `ε u^ε` are asymptotically equicontinuous at the level of vertices on `V^ε(K)`, and on `V^ε(cl D)` under
  the hypotheses of the "moreover" part.
  - The interior part, for vertices `a, b` with `|η(a) - η(b)| ≤ δ`, uses the ball `B = B_{√δ}(η(a))`. Write
    `u = f + (u - f)`, with `f` the harmonic extension of `u` from `V(∂B)`. Then `|u - f| ≤ C Q^ε_B` by the maximum
    principle (Lemma 2.13), and `Q^ε_B ≤ C ε⁻¹ 𝓜(B_{2√δ}) ≤ C ε⁻¹ δ^{q/2}` (Lemmas 2.18, 2.17). The first estimate of
    Lemma 3.2 gives `|f(a) - f(b)| ≤ A C ε⁻¹ δ^{ξ/2}`.
  - The "moreover" part is Lemma 3.2's (boundary-estimate) for `ε u^ε`.
  - The Borel-Cantelli lemma applies along `e` (N3).
  - Inputs: `MaximumPrincipleStmt` (Lemma 2.13), `BoundedExitTimeRVStmt`, `ExitTimeUpperBoundStmt` (Lemmas 2.17,
    2.18), `DiscreteHolderContinuityCorrectedStep` (Lemma 3.2, corrected) and `AdjacentCellsMeetAeStep`
    (MatedCRT/Steps/Infra/MatingOfTrees.lean).
  - Lemma 2.18 with Lemma 2.17 replaces the cited Lemma 2.19. The "moreover" part of Lemma 2.19 holds only in
    probability, as `ε → 0` and then `δ → 0`, which does not give the almost sure bound used at line 1058.
  - Lemma 2.8 is not needed: the cells meeting `cl(B_ρ)` have diameters `→ 0` because `η` is continuous and
    `|η(t)| → ∞`.
* **Arzelà-Ascoli and the measurable choice of `E₀`** (`TightnessSelectionStep`, lines 1021, 1086).
  - The rescaled functions `ū^ε` are piecewise constant. Asymptotic equicontinuity and boundedness
    (`|ū^ε| ≤ C m_ε⁻¹ ε⁻¹`, `MepsScalingInput`) give a uniformly convergent subsequence on compacts.
  - The subsequence is chosen measurably for `σ(h, η)` by a diagonal argument on countably many measurable proxies.
    These are the values of `ū^ε` at the first vertices `a` with `η(a) ∈ D` near the points of a countable dense set.

`AdjacentCellsMeetAeStep` (the cells of adjacent vertices of the map of Definition 1.1 intersect; DMS14 Lemma 8.8,
the `merge` field of the mating-of-trees bundle) confines the walk from `V^ε(B) \ V^ε(∂B)` to `V^ε(B)`, so that the
harmonic extension `f` is bounded by `sup_{V^ε(D)} |u^ε|`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Lemma 3.2, corrected** (review-L32.md, "Minimal corrected statement"; GMS19 Theorem 3.9). There are
`ξ = ξ(ρ, γ) ∈ (0, 1)`, `β = β(ρ, γ) ∈ (0, 1)` and `A = A(ρ, γ) > 0` such that with polynomially high probability as
`ε → 0`: for every connected domain `D ⊆ B_ρ` and every `f` which is `Δ^ε`-harmonic on `V^ε(D) \ V^ε(∂D)`,
`|f(a) - f(b)| ≤ A (sup_{V^ε(D)} |f|) ((ε^β ∨ |η(a) - η(b)|) / dist(η(a), ∂D))^ξ` for `a ∈ V^ε(D) \ V^ε(∂D)` and
`b ∈ V^ε(D)` (F2: interior `a`, floor `ε^β`). Moreover, for each `χ ∈ (0, 1]` and `C' > 0` there are
`ξ' = ξ'(ρ, γ, χ) ∈ (0, 1)` and `C = C(ρ, γ, χ, C') > 0` (F1: the exponent is chosen after `χ`) such that, with
polynomially high probability, if `D` is moreover simply connected and `|f(a) - f(b)| ≤ C' (ε ∨ |η(a) - η(b)|)^χ` on
`V^ε(∂D)`, then `|f(a) - f(b)| ≤ max {C, A sup_{V^ε(D)} |f|} (ε ∨ |η(a) - η(b)|)^ξ'` for all `a, b ∈ V^ε(D)`.
The first estimate is multiplied out by `dist(η(a), ∂D)^ξ`, as in the draft. -/
def DiscreteHolderContinuityCorrectedStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ A β : ℝ, 0 < ξ ∧ ξ < 1 ∧ 0 < A ∧ 0 < β ∧ β < 1 ∧
  ∀ χ C' : ℝ, 0 < χ → χ ≤ 1 → 0 < C' → ∃ ξ' C : ℝ, 0 < ξ' ∧ ξ' < 1 ∧ 0 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω | ∀ (D : Set ℂ) (f : ℤ → ℝ), D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
    (∀ a ∈ interiorCellVertices ε (S.η ω) D, matedLaplacian (S.mult ε ω) f a = 0) →
    (∀ a ∈ interiorCellVertices ε (S.η ω) D, ∀ b ∈ cellVertices ε (S.η ω) D,
      |f a - f b| * infDist (vertexPoint ε (S.η ω) a) (frontier D) ^ ξ ≤
        A * (⨆ a' : cellVertices ε (S.η ω) D, |f a'|) *
          max (ε ^ β) ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖ ^ ξ) ∧
    ((SimplyConnectedSpace D ∧ ∀ a ∈ cellVertices ε (S.η ω) (frontier D),
        ∀ b ∈ cellVertices ε (S.η ω) (frontier D),
          |f a - f b| ≤ C' * max ε ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖ ^ χ) →
      ∀ a ∈ cellVertices ε (S.η ω) D, ∀ b ∈ cellVertices ε (S.η ω) D,
        |f a - f b| ≤ max C (A * ⨆ a' : cellVertices ε (S.η ω) D, |f a'|) *
          max ε ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖ ^ ξ')}

/-- **Polynomially summable scales**: `e_j > 0` and `∑_j e_j^p < ∞` for every `p > 0` (e.g. `e_j = 2^{-j}`). Along such
scales, events of polynomially high probability hold eventually, almost surely (Borel-Cantelli). -/
def IsPolySummableScales (e : ℕ → ℝ) : Prop :=
  (∀ j, 0 < e j) ∧ ∀ p : ℝ, 0 < p → Summable fun j => e j ^ p

/-- **Lemma 3.1, corrected** (lemma:discrete-potential-tightness, line 976; see the module docstring for the three
changes to `DiscretePotentialTightnessStmt`: (N1) `ε⁻¹`-scaled Hölder data, `D` open, (N3) scales in a deterministic
polynomially summable sequence `e`). Let `D ⊆ B_ρ` be a connected domain and `E ∋ ε → 0` a `σ(h, η)`-measurable
sequence with values in `e`. If `σ(h, η)`-measurable `u^ε : V^ε(D) → ℝ` (`ε ∈ E`) satisfy `|Δ^ε u^ε| ≤ C` on
`V^ε(D) \ V^ε(∂D)` and `|u^ε| ≤ C ε⁻¹` on `V^ε(D)` for a `σ(h, η)`-measurable `C > 0`, then a.s. there are a
`σ(h, η)`-measurable subsequence `E₀ ⊆ E` and `ū ∈ C(D)` with `ū^ε → ū` uniformly on every compact `O ⋐ D` along
`E₀`. Moreover, if `D` is simply connected, `u^ε` is discrete harmonic in `V^ε(D) \ V^ε(∂D)` and
`|u^ε(a) - u^ε(b)| ≤ C' ε⁻¹ (ε ∨ |η(a) - η(b)|)^χ` for `a, b ∈ V^ε(∂D)` (`χ ∈ (0, 1]`, `C' > 0`), then the convergence
is uniform on `cl(D)`. -/
def DiscretePotentialTightnessCorrectedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ D : Set ℂ, D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
  ∀ e : ℕ → ℝ, IsPolySummableScales e →
  ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ),
    (∀ n, Measurable[S.envSigma] fun ω => E ω n) → (∀ ω n, E ω n ∈ range e) →
    (∀ ω, Tendsto (E ω) atTop (𝓝 0)) →
    (∀ n a, Measurable[S.envSigma] fun ω => u ω n a) →
    Measurable[S.envSigma] C → (∀ ω, 0 < C ω) →
    (∀ ω n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
      |matedLaplacian (S.mult (E ω n) ω) (u ω n) a| ≤ C ω) →
    (∀ ω n, ∀ a ∈ cellVertices (E ω n) (S.η ω) D, |u ω n a| ≤ C ω / E ω n) →
  ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
    ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
      (∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop O) ∧
      ((SimplyConnectedSpace D ∧
          (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D, matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0) ∧
          ∃ χ C' : ℝ, 0 < χ ∧ χ ≤ 1 ∧ 0 < C' ∧ ∀ n, E ω n < 1 →
            ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D), ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D),
              |u ω n a - u ω n b| ≤
                C' / E ω n * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ) →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop (closure D))

/-! ## The steps -/

/-- The hypotheses of Lemma 3.1 (corrected) on the scales `E`, the functions `u` and the constant `C`. -/
def IsTightnessData {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (D : Set ℂ) (e : ℕ → ℝ)
    (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ) : Prop :=
  (∀ n, Measurable[S.envSigma] fun ω => E ω n) ∧ (∀ ω n, E ω n ∈ range e) ∧
    (∀ ω, Tendsto (E ω) atTop (𝓝 0)) ∧ (∀ n a, Measurable[S.envSigma] fun ω => u ω n a) ∧
    Measurable[S.envSigma] C ∧ (∀ ω, 0 < C ω) ∧
    (∀ ω n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D,
      |matedLaplacian (S.mult (E ω n) ω) (u ω n) a| ≤ C ω) ∧
    (∀ ω n, ∀ a ∈ cellVertices (E ω n) (S.η ω) D, |u ω n a| ≤ C ω / E ω n)

/-- The hypotheses of the "moreover" part of Lemma 3.1 (corrected, N1) at `ω`: `D` simply connected, `u^ε` harmonic
on `V^ε(D) \ V^ε(∂D)`, and `ε⁻¹`-scaled `χ`-Hölder data on `V^ε(∂D)`. -/
def HasHolderBoundaryData {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (D : Set ℂ) (E : Ω → ℕ → ℝ)
    (u : Ω → ℕ → ℤ → ℝ) (ω : Ω) : Prop :=
  SimplyConnectedSpace D ∧
    (∀ n, ∀ a ∈ interiorCellVertices (E ω n) (S.η ω) D, matedLaplacian (S.mult (E ω n) ω) (u ω n) a = 0) ∧
    ∃ χ C' : ℝ, 0 < χ ∧ χ ≤ 1 ∧ 0 < C' ∧ ∀ n, E ω n < 1 →
      ∀ a ∈ cellVertices (E ω n) (S.η ω) (frontier D), ∀ b ∈ cellVertices (E ω n) (S.η ω) (frontier D),
        |u ω n a - u ω n b| ≤
          C' / E ω n * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ

/-- **Asymptotic equicontinuity at the level of vertices** of `ε u^ε` on `V^ε(K)` along the scales `ε_n`: for every
`k > 0` there is `δ > 0` such that for all large `n`, `ε_n |u_n(a) - u_n(b)| ≤ k` whenever `a, b ∈ V^{ε_n}(K)` and
`|η(a) - η(b)| ≤ δ` (eq:equicontinuity, line 1023, before rescaling). -/
def IsVertexAsymptoticallyEquicontinuous (ε : ℕ → ℝ) (η : ℝ → ℂ) (U : ℕ → ℤ → ℝ) (K : Set ℂ) : Prop :=
  ∀ k : ℝ, 0 < k → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ a ∈ cellVertices (ε n) η K, ∀ b ∈ cellVertices (ε n) η K,
    ‖vertexPoint (ε n) η a - vertexPoint (ε n) η b‖ ≤ δ → ε n * |U n a - U n b| ≤ k

/-- **The analytic part of the proof of Lemma 3.1** (lines 1028-1085): almost surely, `ε u^ε` is asymptotically
equicontinuous on `V^ε(K)` for every compact `K ⊆ D`, and on `V^ε(cl D)` under the hypotheses of the "moreover"
part. To be proved from Lemmas 2.13, 2.17, 2.18, 3.2 (corrected) and `AdjacentCellsMeetAeStep`. -/
def TightnessEquicontinuityStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ D : Set ℂ, D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
  ∀ e : ℕ → ℝ, IsPolySummableScales e → ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ),
    IsTightnessData S D e E u C →
  ∀ᵐ ω ∂S.P, (∀ K : Set ℂ, IsCompact K → K ⊆ D → IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u ω) K) ∧
    (HasHolderBoundaryData S D E u ω → IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u ω) (closure D))

/-- **Arzelà-Ascoli with a measurable choice of the subsequence** (lines 1021, 1086): from the almost sure asymptotic
equicontinuity, a `σ(h, η)`-measurable subsequence along which `ū^ε` converges uniformly on compacts of `D`, and on
`cl(D)` under the hypotheses of the "moreover" part. To be proved from `MepsScalingInput` (`m_ε⁻¹ ≤ C ε`). -/
def TightnessSelectionStep (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ D : Set ℂ, D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
  ∀ e : ℕ → ℝ, IsPolySummableScales e → ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ),
    IsTightnessData S D e E u C →
  (∀ᵐ ω ∂S.P, (∀ K : Set ℂ, IsCompact K → K ⊆ D → IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u ω) K) ∧
    (HasHolderBoundaryData S D E u ω → IsVertexAsymptoticallyEquicontinuous (E ω) (S.η ω) (u ω) (closure D))) →
  ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
    ∀ᵐ ω ∂S.P, StrictMono (Φ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar D ∧
      (∀ O : Set ℂ, IsCompact O → closure O ⊆ D →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop O) ∧
      (HasHolderBoundaryData S D E u ω →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop (closure D))

/-- **Lemma 3.1 (corrected)** from its steps. -/
theorem discretePotentialTightness_of_steps (𝒮 : SpaceFillingSLEModel) (hEq : TightnessEquicontinuityStep 𝒮)
    (hSel : TightnessSelectionStep 𝒮) : DiscretePotentialTightnessCorrectedStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS D hDρ hDo hDc e he E u C hEm hEe hEt hum hCm hCp hlap hbd
  have hdata : IsTightnessData S D e E u C := ⟨hEm, hEe, hEt, hum, hCm, hCp, hlap, hbd⟩
  exact hSel γ hγ hγ2 ρ hρ hρ1 Ω S hS D hDρ hDo hDc e he E u C hdata
    (hEq γ hγ hγ2 ρ hρ hρ1 Ω S hS D hDρ hDo hDc e he E u C hdata)

/-- The `ε⁻¹`-scaled Hölder condition (N1) is implied by the draft's unscaled one for `ε < 1`: the corrected
"moreover" part has the weaker hypothesis. -/
theorem holder_scaled_of_unscaled {ε C' x : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hC' : 0 < C') (hx : 0 ≤ x) :
    C' * x ≤ C' / ε * x := by
  have : C' ≤ C' / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  exact mul_le_mul_of_nonneg_right this hx

end MatedCRT
