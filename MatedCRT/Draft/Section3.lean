import MatedCRT.Defs.Setting
import MatedCRT.Defs.Sandpile

/-!
# Section 3: statements of Lemmas 3.1-3.7 (lines 952-1531)

Convergence of the Dirichlet problem, the Green's kernel and the normalized expected exit time. Conventions: see
`MatedCRT/Draft/Section1.lean`. Throughout `ρ ∈ (0, 1)` is fixed (line 954) and universally quantified.

* `ū^ε` (eq:discrete-scaling, line 961) is `rescale (S.mε ε) ε (S.η ω) u`.
* A random sequence `ε_n → 0` is `E : Ω → ℕ → ℝ` with `E ω n > 0` and `E ω n → 0`; a subsequence is
  `n ↦ E ω (Φ ω n)` with `Φ ω` strictly increasing; "`σ(h, η)`-measurable" is measurability for `S.envSigma`.
* The continuum Green's function `G_{B_r(z)}` is `HarmonicBalls.greenFunction (ball z r)` (normalized by
  `ΔG = -δ`, as in the harmonic-balls formalization). CORRECTION [C1] (ESCALATIONS E-A3, review-C): the printed
  constant `m₀` in Lemmas 3.3-3.5, 3.7 is false; for this normalization it is `c₀ = 2/m₀` (`MatedCRTEnv.c₀`; the
  Brownian occupation density is `2G`, line 1172).
* "The solution of the continuum Dirichlet problem" is any function continuous on `cl(B_r(z))` with the given
  distributional Laplacian (`HarmonicBalls.HasLaplacian`, signed measures written through positive and negative parts)
  and boundary values; it is unique, so `∃` is equivalent to "the".

Cited: Lemma 3.2 (GMS19 Theorem 3.9).
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- **Lemma 3.1** (lemma:discrete-potential-tightness, line 973). Let `D ⊆ B_ρ` be connected and `E ∋ ε → 0` a
`σ(h, η)`-measurable sequence. If `σ(h, η)`-measurable `u^ε : V^ε(D) → ℝ` (`ε ∈ E`) satisfy `|Δ^ε u^ε| ≤ C` on
`V^ε(D) \ V^ε(∂D)` and `|u^ε| ≤ C ε⁻¹` on `V^ε(D)` for a `σ(h, η)`-measurable `C > 0`, then a.s. there are a
`σ(h, η)`-measurable subsequence `E₀ ⊆ E` and `ū ∈ C(D)` with `ū^ε → ū` uniformly on every compact `O ⋐ D` along
`E₀`. Moreover, if `D` is simply connected, `u^ε` is discrete harmonic in `V^ε(D) \ V^ε(∂D)` and has Hölder boundary
data (eq:holder-boundary-data: `|u^ε(a) - u^ε(b)| ≤ C' (ε ∨ |η(a) - η(b)|)^χ` for `a, b ∈ V^ε(∂D)`, `χ ∈ (0, 1]`,
`C' > 0`), then the convergence is uniform on `cl(D)`.

CORRECTION [C3] (ESCALATIONS E-A7, review-C): the printed one-sided bound `u^ε ≤ C ε⁻¹` makes the lemma false
(`u^ε ≡ -ε⁻²`); the proof (lines 1016, 1040) and all four uses (lines 1191, 1346, 1419, 1752) have the two-sided bound
`|u^ε| ≤ C ε⁻¹`, which is stated. Review-S (S6): the `u^ε` are functions of `(h, η)` in every use (Lemmas 3.3, 3.5,
4.6), which the measurable choice of the subsequence needs; this is the hypothesis that each `u^ε(a)` is
`σ(h, η)`-measurable. The "moreover" part is for the same subsequence and limit. -/
def DiscretePotentialTightnessStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ D : Set ℂ, D ⊆ ball 0 ρ → IsConnected D →
  ∀ (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (C : Ω → ℝ),
    (∀ n, Measurable[S.envSigma] fun ω => E ω n) → (∀ ω n, 0 < E ω n) → (∀ ω, Tendsto (E ω) atTop (𝓝 0)) →
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
                C' * max (E ω n) ‖vertexPoint (E ω n) (S.η ω) a - vertexPoint (E ω n) (S.η ω) b‖ ^ χ) →
        TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u ω (Φ ω k)))
          ubar atTop (closure D))

/-- **Lemma 3.2** (lemma:discrete-holder-continuity, line 997; GMS19 Theorem 3.9). There are `ξ = ξ(ρ, γ) ∈ (0, 1)`
and `A = A(ρ, γ) > 0` such that with polynomially high probability as `ε → 0`: for every connected domain `D ⊆ B_ρ`
and every `f : V^ε(D) → ℝ` which is `Δ^ε`-harmonic on `V^ε(D) \ V^ε(∂D)`,
`|f(a) - f(b)| ≤ A (sup_{V^ε(D)} |f|) ((ε ∨ |η(a) - η(b)|) / dist(η(a), ∂D))^ξ` for all `a, b ∈ V^ε(D)`. Moreover, if
`D` is simply connected and `f` has Hölder boundary data (eq:holder-boundary-data with constants `χ, C'`), then
`|f(a) - f(b)| ≤ max {C, A sup_{V^ε(D)} |f|} (ε ∨ |η(a) - η(b)|)^ξ` for all `a, b ∈ V^ε(D)`, for a constant `C > 0`.
The constant `C` is read as deterministic, depending on `χ, C'` (and `ρ, γ`): an `ε`-dependent `C` would make the
estimate empty. "Connected domain" is a connected open set. The first estimate is written multiplied out by
`dist(η(a), ∂D)^ξ` (equivalent for `dist > 0`; for `dist = 0` the printed right side is `+∞`). -/
def DiscreteHolderContinuityStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ A : ℝ, 0 < ξ ∧ ξ < 1 ∧ 0 < A ∧
  ∀ χ C' : ℝ, 0 < χ → χ ≤ 1 → 0 < C' → ∃ C : ℝ, 0 < C ∧
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  PolyHighProb S.P fun ε => {ω | ∀ (D : Set ℂ) (f : ℤ → ℝ), D ⊆ ball 0 ρ → IsOpen D → IsConnected D →
    (∀ a ∈ interiorCellVertices ε (S.η ω) D, matedLaplacian (S.mult ε ω) f a = 0) →
    (∀ a ∈ cellVertices ε (S.η ω) D, ∀ b ∈ cellVertices ε (S.η ω) D,
      |f a - f b| * infDist (vertexPoint ε (S.η ω) a) (frontier D) ^ ξ ≤
        A * (⨆ a' : cellVertices ε (S.η ω) D, |f a'|) *
          max ε ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖ ^ ξ) ∧
    ((SimplyConnectedSpace D ∧ ∀ a ∈ cellVertices ε (S.η ω) (frontier D),
        ∀ b ∈ cellVertices ε (S.η ω) (frontier D),
          |f a - f b| ≤ C' * max ε ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖ ^ χ) →
      ∀ a ∈ cellVertices ε (S.η ω) D, ∀ b ∈ cellVertices ε (S.η ω) D,
        |f a - f b| ≤ max C (A * ⨆ a' : cellVertices ε (S.η ω) D, |f a'|) *
          max ε ‖vertexPoint ε (S.η ω) a - vertexPoint ε (S.η ω) b‖ ^ ξ)}

/-- **Lemma 3.3** (lemma:uniform-convergence-of-greens-function, line 1106). Fix deterministic `r > 0`, `z ∈ ℂ` with
`B_r(z) ⊆ B_ρ`, and `y ∈ B_r(z)`. Let `g^ε = ε⁻¹ g^ε_{B_r(z)}(a^ε_y, ·)` and `ḡ^ε` its rescaling. For each `δ > 0` and
each `O ⊆ cl(B_r(z)) \ {y}` at positive distance from `y`, with probability tending to `1` as `ε → 0`,
`sup_{x ∈ O} |ḡ^ε(x) - (c₀/6) G_{B_r(z)}(y, x)| ≤ δ`. CORRECTION [C1]: `c₀ = 2/m₀` in place of the printed `m₀`. -/
def UniformConvergenceGreenKernelStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ δ : ℝ, 0 < δ → ∀ O : Set ℂ, O ⊆ closedBall z r \ {y} → 0 < infDist y O →
    ProbTendsToOne S.P fun ε => {ω | ∀ x ∈ O,
      |rescale (S.mε ε) ε (S.η ω)
          (fun a => ε⁻¹ * greenKernel (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))
            (vertexOf ε (S.η ω) y) a) x -
        S.c₀ / 6 * greenFunction (ball z r) y x| ≤ δ}

/-- **Lemma 3.4** (lemma:integral-convergence-of-greens-function, line 1119). For deterministic `z`, `r > 0` with
`B_r(z) ⊆ B_ρ`, each `y ∈ B_r(z)` and each bounded, Hölder continuous, `σ(h, η)`-measurable `f : B_r(z) → ℝ`,
`m_ε⁻¹ ∑_{x ∈ V^ε(B_r(z))} G^ε_{B_r(z)}(a^ε_y, x) f(η(x)) → c₀ ∫_{B_r(z)} G_{B_r(z)}(y, x) f(x) dμ_h(x)`
in probability. (`f ω x` is measurable in `ω` for each `x`; bound and Hölder constants may be random.)
CORRECTION [C1]: `c₀ = 2/m₀` in place of the printed `m₀`. -/
def IntegralConvergenceGreenFunctionStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ f : Ω → ℂ → ℝ, (∀ x, Measurable[S.envSigma] fun ω => f ω x) →
    (∀ ω, ∃ M : ℝ, ∀ x ∈ ball z r, |f ω x| ≤ M) → (∀ ω, IsHolderContinuousOn (f ω) (ball z r)) →
    TendstoInProbability S.P
      (fun ε ω => (S.mε ε)⁻¹ * ∑' x : cellVertices ε (S.η ω) (ball z r),
        greenFn (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r)) (vertexOf ε (S.η ω) y) x *
          f ω (vertexPoint ε (S.η ω) x))
      (fun ω => S.c₀ * ∫ x in ball z r, greenFunction (ball z r) y x * f ω x ∂S.μ ω)

/-- **Lemma 3.5** (lemma:discrete-dirichlet-problem, line 1233). Fix deterministic `z`, `r > 0` with
`B_r(z) ⊆ B_ρ`, a bounded Hölder continuous `ψ : B_r(z) → ℝ` and a Hölder continuous `φ` on a neighbourhood
`cl(B_{r+s}(z))`, `s > 0`, of `cl(B_r(z))`. The rescaled solution `f̄^ε` of the discrete Dirichlet problem
`Δ^ε f^ε(a) = ψ(η(a))` on `V^ε(B_r(z)) \ V^ε(∂B_r(z))`, `f^ε(b) = m_ε φ(η(b))` on `V^ε(∂B_r(z))`, converges in
probability, uniformly on `cl(B_r(z))`, to the solution of `Δf̄ = c₀ ψ μ_h` on `B_r(z)`, `f̄ = φ` on `∂B_r(z)`;
moreover a.s. `f̄` is Hölder continuous on `cl(B_r(z))`. The discrete solutions are any functions `F ε ω` satisfying
the discrete problem for a.e. `ω` (it has a unique solution).
CORRECTION [C1]: `c₀ = 2/m₀` in place of the printed `m₀`. Review-S (S2): the printed `φ : cl(B_r(z)) → ℝ` is
evaluated at `η(b)` for the cells `H_b` meeting `∂B_r(z)`, whose marked points may lie outside `cl(B_r(z))` (within
the cell diameter, which tends to `0`, Lemma 2.8); with `φ` Hölder on `cl(B_r(z))` only, the lemma fails (`φ = 0` on
the ball, `1` outside). So `φ` is defined and Hölder on a neighbourhood of `cl(B_r(z))`. -/
def DiscreteDirichletProblemStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ φ : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |ψ x| ≤ M) → IsHolderContinuousOn ψ (ball z r) →
    (∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn φ (closedBall z (r + s))) →
  ∀ F : ℝ → Ω → ℤ → ℝ,
    (∀ ε, 0 < ε → ∀ᵐ ω ∂S.P,
      (∀ a ∈ interiorCellVertices ε (S.η ω) (ball z r),
        matedLaplacian (S.mult ε ω) (F ε ω) a = ψ (vertexPoint ε (S.η ω) a)) ∧
      ∀ b ∈ cellVertices ε (S.η ω) (sphere z r), F ε ω b = S.mε ε * φ (vertexPoint ε (S.η ω) b)) →
  ∃ fbar : Ω → ℂ → ℝ,
    (∀ᵐ ω ∂S.P, ContinuousOn (fbar ω) (closedBall z r) ∧
      HasLaplacian (fbar ω) ((S.μ ω).withDensity fun x => ENNReal.ofReal (S.c₀ * ψ x))
        ((S.μ ω).withDensity fun x => ENNReal.ofReal (-(S.c₀ * ψ x))) (ball z r) ∧
      (∀ x ∈ sphere z r, fbar ω x = φ x) ∧ IsHolderContinuousOn (fbar ω) (closedBall z r)) ∧
    TendstoUniformlyOnInProbability S.P (fun ε ω => rescale (S.mε ε) ε (S.η ω) (F ε ω)) fbar (closedBall z r)

/-- **Lemma 3.6** (lemma:convergence-of-harmonic-functions, line 1254). For deterministic `z`, `r > 0` with
`B_r(z) ⊆ B_ρ` and `ψ` Hölder continuous on a neighbourhood `cl(B_{r+s}(z))`, `s > 0`, of `cl(B_r(z))` (review-S
(S2): the printed `ψ : cl(B_r(z)) → ℝ` is evaluated at the marked point of the exit cell, which may lie outside
`cl(B_r(z))`; see Lemma 3.5): for every `y ∈ B_r(z)`,
`E[ψ(η(X^{a^ε_y, ε}_{τ^ε_{B_r(z)}})) | h, η] → E[ψ(X^y_{τ^y_{B_r(z)}}) | h, η]` in probability, where `τ^ε` is the exit
time of simple random walk from `V^ε(B_r(z)) \ V^ε(∂B_r(z))` and `τ^y` the exit time of LBM (rescaled,
eq:rescaled-lbm; the exit position does not depend on the time scaling) from `B_r(z)`. -/
def ConvergenceHarmonicFunctionsStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ ψ : ℂ → ℝ, (∃ s : ℝ, 0 < s ∧ IsHolderContinuousOn ψ (closedBall z (r + s))) → ∀ y ∈ ball z r,
    TendstoInProbability S.P
      (fun ε ω => ∫ x, ψ (vertexPoint ε (S.η ω)
          (vExitPosition (interiorCellVertices ε (S.η ω) (ball z r)) x))
        ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      (fun ω => ∫ b, ψ (pathExitPosition (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b))
        ∂planarBrownianMotion y)

/-- **Lemma 3.7** (lemma:convergence-of-the-normalized-exit-time, line 1391). For deterministic `z`, `r > 0` with
`B_r(z) ⊆ B_ρ`, the rescaled normalized expected exit time `q̄^ε_{B_r(z)}` converges uniformly on `cl(B_r(z))`, in
probability, to the solution `q̄_{B_r(z)}` of `Δq̄ = -(c₀/6) μ_h` on `B_r(z)`, `q̄ = 0` on `∂B_r(z)`.
CORRECTION [C1]: `c₀ = 2/m₀` in place of the printed `m₀`. -/
def ConvergenceNormalizedExitTimeStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∃ qbar : Ω → ℂ → ℝ,
    (∀ᵐ ω ∂S.P, ContinuousOn (qbar ω) (closedBall z r) ∧
      HasLaplacian (qbar ω) 0 (ENNReal.ofReal (S.c₀ / 6) • S.μ ω) (ball z r) ∧
      ∀ x ∈ sphere z r, qbar ω x = 0) ∧
    TendstoUniformlyOnInProbability S.P
      (fun ε ω => rescale (S.mε ε) ε (S.η ω)
        (normExitTime (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r))))
      qbar (closedBall z r)

end MatedCRT
