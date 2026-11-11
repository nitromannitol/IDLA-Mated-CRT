import MatedCRT.Defs.Setting
import MatedCRT.Defs.WalkDisconnection

/-!
# Frozen inputs of Section 9 of the stopped layer-potential argument

Four extra inputs, frozen in the form stated below. They are literature facts about Liouville Brownian motion, mated-CRT random walks and the whole-plane field, not statements about this paper's clusters, odometers, harmonic balls or IDLA processes. The set version of the walk disconnection event (`walkSetDisconnectsBeforeHit`) is the event with a set of source vertices; it is the graph-theoretic definition of `graphDisconnects` applied to a set `Y`.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open _root_.HarmonicBalls

/-- `K` disconnects the source set `Y` from the target set `A` in the graph `G`: no path in the complement of `K`
connects a vertex of `Y` to a vertex of `A` (the set version of `graphDisconnects`). -/
def graphSetDisconnects {V : Type*} (G : SimpleGraph V) (K : Set V) (Y A : Set V) : Prop :=
  ∀ (y : V) (_hy : y ∈ Y) (hyK : y ∉ K) (a : V) (_ha : a ∈ A) (hak : a ∉ K),
    ¬ (G.induce Kᶜ).Reachable ⟨y, hyK⟩ ⟨a, hak⟩

/-- The walk `x` disconnects the source set `Y` from `A` strictly before its first hit of `A` (set version of
`walkDisconnectsBeforeHit`). -/
def walkSetDisconnectsBeforeHit (m : ℤ → ℤ → ℕ) (Y A : Set ℤ) (x : ℕ → ℤ) : Prop :=
  graphSetDisconnects (adjGraph m) (walkTraceBefore x (vHitTime A x)) Y A

/-- Input (1), continuum normalization (the lower median `m₀` is positive and finite): for the cone Liouville Brownian motion `Y` started at `0`, `0 < τ^Y_{B_{1/2}} < ∞` almost surely. Source: Berestycki-Gwynne, arXiv:2003.10320v2, §1.2, (1.6), footnote 2; standard, no exact numbered theorem. -/
def FPLBMExitTimePositiveFinite (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, ∀ᵐ b ∂(planarBrownianMotion 0),
      0 < lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b ∧ lbmExitTime (S.clock ω) (ball 0 (1 / 2)) b < ⊤

/-- Input (2), tightness of the embedded walk exit: for every `R > 0`, `lim_{M→∞} limsup_{ε↓0} P[ε τ^ε_R > M] = 0` for the annealed embedded walk from `a^ε_0`. Source: Berestycki-Gwynne, arXiv:2003.10320v2, Remark 1.3, (1.8); the tightness follows from Theorem 1.2 and that remark. The polynomial normalization bound `0 < m_ε ≤ C ε⁻¹` of the same input is `MepsScalingInput` (External/SLE.lean). -/
def FPEmbeddedWalkExitTail (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ R : ℝ, 0 < R → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
    S.IsValid 𝒮 γ →
    Tendsto (fun M : ℝ => limsup (fun ε : ℝ => ∫⁻ ω, srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) 0)
        {x | ENNReal.ofReal M < ENNReal.ofReal ε * (embeddedExitTime ε (S.η ω) (ball 0 R) x : ℝ≥0∞)} ∂S.P)
      (𝓝[>] 0)) atTop (𝓝 0)

/-- Input (3), small logarithmic potentials: for every `0 < ρ' < 1`, almost surely `lim_{r↓0} sup_{z ∈ B_{ρ'}} ∫_{B_r(z)} (1 + log⁺ (1/|z - w|)) μ_h(dw) = 0` (the upper half of (A.1), with `log⁺ = max · 0`). Source: Berestycki-Gwynne, arXiv:2003.10320v2, Lemma A.1, upper half of (A.1), followed by Borel-Cantelli and layer-cake integration. -/
def FPLogPotentialSmall (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω),
    S.IsValid 𝒮 γ →
    ∀ᵐ ω ∂S.P, Tendsto (fun r : ℝ => ⨆ z ∈ ball (0 : ℂ) ρ', ∫⁻ w in ball z r,
      ENNReal.ofReal (1 + max 0 (Real.log (1 / ‖z - w‖))) ∂(S.μ ω)) (𝓝[>] 0) (𝓝 0)

/-- Input (4), finite-annulus disconnection: for finitely many balls with `B_{3 r_j}(y_j) ⊆ B_ρ`, `ρ < 1`, there is a deterministic `p > 0` with `P[min_j P^{h,η}_{a^ε_{y_j}}(D_j^ε) ≥ p] → 1`, where `D_j^ε` is the event that the visited vertices disconnect the cells meeting `∂B_{r_j/2}(y_j)` from the cells meeting `∂B_{2 r_j}(y_j)` before hitting the latter. Source: Gwynne-Miller-Sheffield, arXiv:1807.07511v3, Lemma 3.11, (3.35). -/
def FPFiniteAnnulusDisconnection (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ (n : ℕ) (y : Fin n → ℂ) (r : Fin n → ℝ),
    (∀ j, 0 < r j ∧ closedBall (y j) (3 * r j) ⊆ ball 0 ρ) →
    ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
    ∃ p : ℝ, 0 < p ∧ ProbTendsToOne S.P (fun ε => {ω | ∀ j : Fin n,
      ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) (y j)) {x |
        walkSetDisconnectsBeforeHit (S.mult ε ω)
          (cellVertices ε (S.η ω) (sphere (y j) (r j / 2)))
          (cellVertices ε (S.η ω) (sphere (y j) (2 * r j))) x}})

end MatedCRT
