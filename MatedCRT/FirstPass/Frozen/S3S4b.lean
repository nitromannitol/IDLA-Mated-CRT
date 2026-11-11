import MatedCRT.Steps.Sec3.IntegralConvergenceGreenFunction
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.FixedTimeReduction
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.FiniteDomainBridge

/-!
# Frozen external inputs of Lemmas 3.4 and 3.5 (occupation and truncated laws)

Each `def` below is an external input, used as an explicit hypothesis. The Revuz occupation identity for Liouville Brownian motion and the truncated random-walk-to-LBM convergence are literature inputs; the third is general random-walk background. The frozen corrected Lemma 3.2 and the frozen planar Brownian outward excursion are in `FirstPass/Frozen/S3S4.lean`. Each Prop is stated about the actual walk and the actual LBM clock `S.clock` of a valid environment (no arbitrary clocks).
-/

namespace MatedCRT

open MeasureTheory Set Metric MarkovProcess
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- Retired: restated (the literal pathwise identity with the unscaled clock is not the quenched expected occupation of the paper's process); the restated form is `FrozenLBMGreenOccupationRescaled`.
The Revuz occupation identity for the actual Liouville Brownian motion (the killed Green potential of Brownian motion): for `y ∈ B_r(z)`, almost surely the LBM exit time of `B_r(z)` is finite for planar-Brownian-a.e. starting point, and for each bounded Hölder `f` on `B_r(z)` the LBM occupation integral of `f` is `2 ∫_{B_r(z)} G_{B_r(z)}(y, x) f(x) dμ_h(x)`. The Lean form is `LBMGreenOccupationStep`. Source: Garban-Rhodes-Vargas, *Liouville Brownian motion*, Theorem 2.7(1), pp. 10-11 (the citation in the paper's proof of Lemma 3.4); random-walk-to-LBM background BG20 arXiv:2003.10320 (locator: GRV Theorem 2.7(1), §2.4, arXiv:1301.2876v4; partial, restatement pending). The constant `2` is that of the existing step and is not re-audited here. -/
def FrozenLBMGreenOccupation (𝒮 : SpaceFillingSLEModel) : Prop :=
  LBMGreenOccupationStep 𝒮

/-- Retired: restated; sample-path convergence is not the paper's statement. The restated form is `FrozenTruncatedQuenchedLawsFixedTime`. Convergence of the truncated random-walk occupation functional to the truncated LBM occupation: for a bounded, continuous, Hölder test function `g` on `B_r(z)` and `T > 0`, the discrete occupation `(m_ε)⁻¹ ∑_{n < ⌊T m_ε⌋} g(η(X_n)) 1{n < τ^ε}` converges in probability to `∫_{(0, T ∧ τ_B]} g(B^LBM_t) dt`, for the actual walk `X` and the actual LBM clock of a valid environment. This is the Lean statement `TruncatedDetFixedTimeStep` (`Proofs/Sec3/IntegralConvergenceGreenFunction/FixedTimeReduction.lean:48`). Source: BG20 arXiv:2003.10320 (random-walk-to-LBM convergence; locator: BG Theorem 1.2, arXiv:2003.10320v2; partial, restatement pending), with the LBM time change of Garban-Rhodes-Vargas. -/
def FrozenTruncatedDetFixedTime (𝒮 : SpaceFillingSLEModel) : Prop :=
  TruncatedDetFixedTimeStep 𝒮

/-- The finite-domain representation of the discrete Dirichlet problem for simple random walk on a locally finite graph on `ℤ` containing the nearest-neighbour edges: a function `F` with discrete Laplacian `g` on a finite `A` equals the boundary-exit expectation of its boundary values minus the Green potential `∑_b G_A(a, b) g(b)`. This is general random-walk background, not a statement about this paper's clusters, and is the Lean statement `FiniteDomainDirichletRepresentation` (`Proofs/Sec3/DiscreteDirichletProblem/FiniteDomainBridge.lean:13`). Source: Lawler-Limic, *Random Walk: A Modern Introduction* (Cambridge 2010), Corollary 6.2.4, cited in the paper's proof of Lemma 3.5.
Truth check: TRUE. Lawler-Limic (2010), p. 125, Corollary 6.2.4, equations (6.8)-(6.9). -/
def FrozenFiniteDomainDirichletRepresentation : Prop :=
  FiniteDomainDirichletRepresentation

/-! ## Restated frozen inputs

The restated forms keep the original quantifiers and hypotheses through `y ∈ ball z r` and state the quenched meanings explicitly. The old forms `FrozenLBMGreenOccupation` and `FrozenTruncatedDetFixedTime` are retired (see their docstrings). -/

/-- Occupation `O_U(ω, f, b) = ∫_{(0, min U τ]} f(X_t) dt` of the median-rescaled Liouville Brownian motion
`X_t = rescaledLBMPath (S.clock ω) S.m₀ b t` (eq:rescaled-lbm), with exit time `τ = pathExitTime D X`. -/
noncomputable def rescaledLBMOccupation {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) (D : Set ℂ)
    (U : ENNReal) (f : ℂ → ℝ) (b : ContinuousPath ℂ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) (min U (pathExitTime D (rescaledLBMPath (S.clock ω) S.m₀ b))).toReal,
    f (rescaledLBMPath (S.clock ω) S.m₀ b t.toNNReal)

open Classical in
/-- Quenched discrete occupation `Q_ε(ω, g, T, q) = m_ε⁻¹ ∑_{k < ⌊T m_ε⌋} 1{q_0,…,q_k ∈ I_ε(D)} g(vertex_k)` of a walk
path `q` (with `I_ε(D)` the interior cell vertices of `D`). -/
noncomputable def quenchedDiscreteOccupation {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ω : Ω) (D : Set ℂ)
    (g : ℂ → ℝ) (T ε : ℝ) (q : ℕ → ℤ) : ℝ :=
  (S.mε ε)⁻¹ * ∑ k ∈ Finset.range ⌊T * S.mε ε⌋₊,
    if ∀ j ≤ k, q j ∈ interiorCellVertices ε (S.η ω) D then g (vertexPoint ε (S.η ω) (q k)) else 0

/-- Restated `LBMGreenOccupationStep` (quenched expected occupation, median-rescaled LBM, normalization `c₀ = 2 / m₀`). Source: Garban-Rhodes-Vargas, *Liouville Brownian motion*, arXiv:1301.2876v4: the Revuz (occupation) identity for LBM (locator of the exact clause not yet pinned). The cone restriction and the normalization `c₀ = 2 / m₀` follow from the LQG coordinate-change and deterministic rescaling lemmas; the Lean type is therefore not literally GRV Theorem 2.7(1). -/
def FrozenLBMGreenOccupationRescaled (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ᵐ ω ∂S.P,
    (∀ᵐ b ∂planarBrownianMotion y, pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b) < ⊤) ∧
    Integrable (fun b => (pathExitTime (ball z r) (rescaledLBMPath (S.clock ω) S.m₀ b)).toReal)
      (planarBrownianMotion y) ∧
    ∀ f : ℂ → ℝ, (∃ M : ℝ, ∀ x ∈ ball z r, |f x| ≤ M) → IsHolderContinuousOn f (ball z r) →
      (∫ b, rescaledLBMOccupation S ω (ball z r) ⊤ f b ∂planarBrownianMotion y) =
        (2 / S.m₀) * ∫ x in ball z r, greenFunction (ball z r) y x * f x ∂S.μ ω

/-- Restated `TruncatedDetFixedTimeStep`: convergence in probability of the quenched laws (quenched expectations) of the truncated discrete occupation to the quenched expected truncated LBM occupation. Source: Berestycki-Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, arXiv:2003.10320v2, Theorem 1.2 (partial: a corollary asserting convergence of quenched expectations).
Truth check: UNRESOLVED for an unconstrained SLE model; TRUE under the certified reference law, see `SLEReferenceExistsInput`. -/
def FrozenTruncatedQuenchedLawsFixedTime (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z y : ℂ), 0 < r → ball z r ⊆ ball 0 ρ → y ∈ ball z r →
  ∀ g : ℂ → ℝ, Continuous g → (∃ M : ℝ, ∀ x, |g x| ≤ M) →
  (∃ (C χ : ℝ≥0), 0 < χ ∧ HolderOnWith C χ g (ball z r)) →
  ∀ T : ℝ, 0 < T → TendstoInProbability S.P
    (fun ε ω => ∫ q, quenchedDiscreteOccupation S ω (ball z r) g T ε q
      ∂srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
    (fun ω => ∫ b, rescaledLBMOccupation S ω (ball z r) (ENNReal.ofReal T) g b ∂planarBrownianMotion y)

end MatedCRT
