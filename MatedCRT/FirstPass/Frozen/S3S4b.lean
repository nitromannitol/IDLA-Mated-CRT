import MatedCRT.Steps.Sec3.IntegralConvergenceGreenFunction
import MatedCRT.Proofs.Sec3.IntegralConvergenceGreenFunction.FixedTimeReduction
import MatedCRT.Proofs.Sec3.DiscreteDirichletProblem.FiniteDomainBridge

/-!
# First pass: frozen external inputs of Lemmas 3.4 and 3.5 (q2, task fp-S3S4b)

Each `def` below is an EXTERNAL input of the first pass, used as an explicit hypothesis. The first two are operator
rulings of 2026-11-09 17:00 UTC (inbox, "FIRST PASS wave 2"): the Revuz occupation identity for Liouville Brownian motion
and the truncated random-walk-to-LBM convergence. The third is general random-walk background. The frozen corrected
Lemma 3.2 and the frozen planar Brownian outward excursion are reused from `MatedCRT/FirstPass/Frozen/S3S4.lean`.
Each Prop is the existing statement of its Step, reused unchanged, because it is already stated about the actual walk and
the actual LBM clock `S.clock` of a valid environment (no arbitrary clocks).
-/

namespace MatedCRT

open MeasureTheory Set Metric MarkovProcess
open _root_.HarmonicBalls
open scoped ENNReal NNReal

/-- RETIRED (restated 2026-11-09 21:10 UTC: the literal pathwise identity with the unscaled clock is not the quenched
expected occupation of the paper's process; use `FrozenLBMGreenOccupationRescaled`; kept for the record, do not delete).
FIRST-PASS FROZEN. The Revuz occupation identity for the actual Liouville Brownian motion (the killed Green potential
of Brownian motion): for `y ∈ B_r(z)`, almost surely the LBM exit time of `B_r(z)` is finite for planar-Brownian-a.e.
starting point, and for each bounded Hölder `f` on `B_r(z)` the LBM occupation integral of `f` is
`2 ∫_{B_r(z)} G_{B_r(z)}(y, x) f(x) dμ_h(x)`. This is `LBMGreenOccupationStep`
(MatedCRT/Steps/Sec3/IntegralConvergenceGreenFunction.lean:30). Source: Garban–Rhodes–Vargas, *Liouville Brownian motion*,
Theorem 2.7(1), pp. 10–11 (the citation in the paper's proof of Lemma 3.4); random-walk-to-LBM background BG20 arXiv:2003.10320
(locator: GRV Theorem 2.7(1), §2.4, arXiv:1301.2876v4; partial, restatement pending, per notes/fp-gaps/CHATGPT-frozen-locators.md). The constant `2` is that of the existing Step, not re-audited here.
Used by: firstPass_3_4. -/
def FrozenLBMGreenOccupation (𝒮 : SpaceFillingSLEModel) : Prop :=
  LBMGreenOccupationStep 𝒮

/-- RETIRED (restated 2026-11-09 21:10 UTC: sample-path convergence is not the paper's statement; use
`FrozenTruncatedQuenchedLawsFixedTime`; kept for the record, do not delete). FIRST-PASS FROZEN. Convergence of the truncated random-walk occupation functional to the truncated LBM occupation: for a
bounded, continuous, Hölder test function `g` on `B_r(z)` and `T > 0`, the discrete occupation
`(m_ε)⁻¹ ∑_{n < ⌊T m_ε⌋} g(η(X_n)) 1{n < τ^ε}` converges in probability to `∫_{(0, T ∧ τ_B]} g(B^LBM_t) dt`, for the actual
walk `X` and the actual LBM clock of a valid environment. This is `TruncatedDetFixedTimeStep`
(MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/FixedTimeReduction.lean:48), reused unchanged. Source: BG20
arXiv:2003.10320 (random-walk-to-LBM convergence; operator ruling 2026-11-09 17:00 UTC; locator: BG Theorem 1.2, arXiv:2003.10320v2; partial, restatement pending, per notes/fp-gaps/CHATGPT-frozen-locators.md), with the LBM
time change of Garban–Rhodes–Vargas. Used by: firstPass_3_4. -/
def FrozenTruncatedDetFixedTime (𝒮 : SpaceFillingSLEModel) : Prop :=
  TruncatedDetFixedTimeStep 𝒮

/-- FIRST-PASS FROZEN. The finite-domain representation of the discrete Dirichlet problem for simple random walk on a locally
finite graph on `ℤ` containing the nearest-neighbour edges: a function `F` with discrete Laplacian `g` on a finite `A` equals
the boundary-exit expectation of its boundary values minus the Green potential `∑_b G_A(a, b) g(b)`. This is general
random-walk background, not a statement about this paper's clusters, and is `FiniteDomainDirichletRepresentation`
(MatedCRT/Proofs/Sec3/DiscreteDirichletProblem/FiniteDomainBridge.lean:13), reused unchanged. Source: Lawler–Limic, *Random
Walk: A Modern Introduction* (Cambridge 2010), Corollary 6.2.4, cited in the paper's proof of Lemma 3.5 (corrected paper, line
1532–1535 region). Used by: firstPass_3_5_corrected. -/
def FrozenFiniteDomainDirichletRepresentation : Prop :=
  FiniteDomainDirichletRepresentation

/-! ## Restated frozen Props (2026-11-09 21:10 UTC; notes/fp-gaps/CHATGPT-3-4-restatements.md)

The restated forms keep the original quantifiers and hypotheses through `y ∈ ball z r` and state the quenched meanings
explicitly. The old forms `FrozenLBMGreenOccupation` and `FrozenTruncatedDetFixedTime` are RETIRED (see their docstrings). -/

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

/-- FIRST-PASS FROZEN. Restated `LBMGreenOccupationStep` (quenched expected occupation, median-rescaled LBM, normalization
`c₀ = 2 / m₀`). Source: Garban–Rhodes–Vargas, *Liouville Brownian motion*, arXiv:1301.2876v4, Theorem 2.7(1) (partial:
the cone extension uses weighted clocks, see notes/fp-gaps/CHATGPT-3-4-restatements.md). Used by: firstPass_3_4 (to be
re-checked against this form; the consumer still takes the RETIRED `FrozenLBMGreenOccupation`). -/
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

/-- FIRST-PASS FROZEN. Restated `TruncatedDetFixedTimeStep`: convergence in probability of the quenched laws (quenched
expectations) of the truncated discrete occupation to the quenched expected truncated LBM occupation. Source:
Berestycki–Gwynne, *Random walks on mated-CRT planar maps and Liouville Brownian motion*, arXiv:2003.10320v2, Theorem 1.2
(partial: a corollary asserting convergence of quenched expectations; see notes/fp-gaps/CHATGPT-3-4-restatements.md).
Used by: firstPass_3_4 (to be re-checked against this form). -/
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
