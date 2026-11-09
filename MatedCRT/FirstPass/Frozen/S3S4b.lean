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

/-- FIRST-PASS FROZEN. The Revuz occupation identity for the actual Liouville Brownian motion (the killed Green potential
of Brownian motion): for `y ∈ B_r(z)`, almost surely the LBM exit time of `B_r(z)` is finite for planar-Brownian-a.e.
starting point, and for each bounded Hölder `f` on `B_r(z)` the LBM occupation integral of `f` is
`2 ∫_{B_r(z)} G_{B_r(z)}(y, x) f(x) dμ_h(x)`. This is `LBMGreenOccupationStep`
(MatedCRT/Steps/Sec3/IntegralConvergenceGreenFunction.lean:30). Source: Garban–Rhodes–Vargas, *Liouville Brownian motion*,
Theorem 2.7(1), pp. 10–11 (the citation in the paper's proof of Lemma 3.4); random-walk-to-LBM background BG20 arXiv:2003.10320
(operator ruling; locator to be confirmed). The constant `2` is that of the existing Step, not re-audited here.
Used by: firstPass_3_4. -/
def FrozenLBMGreenOccupation (𝒮 : SpaceFillingSLEModel) : Prop :=
  LBMGreenOccupationStep 𝒮

/-- FIRST-PASS FROZEN. Convergence of the truncated random-walk occupation functional to the truncated LBM occupation: for a
bounded, continuous, Hölder test function `g` on `B_r(z)` and `T > 0`, the discrete occupation
`(m_ε)⁻¹ ∑_{n < ⌊T m_ε⌋} g(η(X_n)) 1{n < τ^ε}` converges in probability to `∫_{(0, T ∧ τ_B]} g(B^LBM_t) dt`, for the actual
walk `X` and the actual LBM clock of a valid environment. This is `TruncatedDetFixedTimeStep`
(MatedCRT/Proofs/Sec3/IntegralConvergenceGreenFunction/FixedTimeReduction.lean:48), reused unchanged. Source: BG20
arXiv:2003.10320 (random-walk-to-LBM convergence; operator ruling 2026-11-09 17:00 UTC; locator to be confirmed), with the LBM
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

end MatedCRT
