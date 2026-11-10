import MatedCRT.Draft.Section3HarmonicCorrected

/-!
# The one-sided boundary continuity estimate (BE), a FIRST-PASS FROZEN cited input (fp-S3-6-annealed-route)

Source: Gwynne-Miller-Sheffield, "The Tutte embedding of the mated-CRT map converges to LQG" (arXiv:1807.07511),
Theorem 3.9, equation (3.31) (the one-sided boundary estimate; GMS Lemma 3.11 is the annealed input of its proof).
Interface: `notes/fp-gaps/CHATGPT-idla-3-6-sameWalk-PRO.md` §2.2 (lines 221-285). The estimate is not a consequence of
Lemma 2.16 or Lemma 2.18 (PRO §2.3): it needs annular disconnection and dyadic strong-Markov iteration.

PENDING TRUTH CHECK: the printed form (3.31) of GMS, its exact quantifiers (uniformity over simply connected domains,
the constant `A` and exponent `ν`), and the convention for an empty local boundary set have not been checked against
the arXiv version. Chat 202 (UNCLEAR as typed): the binder order was repaired so that the exponents and the constant are
chosen per valid environment (after `S.IsValid 𝒮 γ`); the repaired form is PENDING TRUTH CHECK as well. The statement is stated for a space-filling model `𝒮` as a PARAMETER and is used only as a
hypothesis (never a `∀ 𝒮` inside).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

/-- The maximum of `f` over the discrete boundary cells `V^ε(∂D ∩ B_t(η(x)))` near the vertex `x` (PRO §2.2).
The supremum over the empty set is `0` (the convention of `sSup ∅` in `ℝ`); on the bounded domains used here the
index set is finite. -/
noncomputable def boundarySupNear (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) (f : ℤ → ℝ) (x : ℤ) (t : ℝ) : ℝ :=
  ⨆ k ∈ cellVertices ε η (frontier D ∩ ball (vertexPoint ε η x) t), f k

/-- The discrete sup norm of `f` over the vertices `V^ε(D)` (PRO §2.2). -/
noncomputable def discreteSupNorm (ε : ℝ) (η : ℝ → ℂ) (D : Set ℂ) (f : ℤ → ℝ) : ℝ :=
  ⨆ k ∈ cellVertices ε η D, |f k|

/-- **(BE)**, the one-sided boundary continuity estimate of discrete harmonic functions, the upper half of GMS Theorem 3.9
eq. (3.31) (derived from the two-sided statement). GMS = Gwynne-Miller-Sheffield, *Harmonic functions on mated-CRT
maps* (bibkey `gwynne2019harmonic`, `docs/campaign/GRAPH.md`); the source of the one-sided form is that Theorem 3.9.
For `γ ∈ (0,2)` and `ρ ∈ (0,1)`, every valid environment `S` (`S.IsValid 𝒮 γ`), there are exponents `κ, ν`, a constant `A` and `b > 0` such that, with polynomially high probability
(`PolyHighProb`), every simply connected domain `D ⊆ B_ρ` and every discrete function `f` which is mated-harmonic on the
interior cells of `D`, and every vertex `x ∈ V^ε(D)` and `t > 0`,
`f(x) ≤ max_{V^ε(∂D ∩ B_t(η x))} f + A ‖f‖_{∞, V^ε(D)} (t / dist(η x, ∂D))^{-ν}`.
Chat 202: UNCLEAR as previously typed; repaired binder order (the existential over `κ, ν, A, b` now sits after
`S.IsValid 𝒮 γ`, per coupling, as in the other freezes); operator truth check (10:10 UTC): the repaired form is TRUE.
Frozen with `𝒮` as a parameter; used only as a hypothesis of the annealed clause. -/
def FrozenOneSidedBoundaryContinuity (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∃ κ ν A b : ℝ, 0 < κ ∧ 0 < ν ∧ 0 < A ∧ 0 < b ∧
  PolyHighProb S.P fun ε => {ω | ∀ (D : Set ℂ) (f : ℤ → ℝ),
    D ⊆ ball 0 ρ → IsOpen D → IsConnected D → SimplyConnectedSpace D →
    (∀ x ∈ interiorCellVertices ε (S.η ω) D, matedLaplacian (S.mult ε ω) f x = 0) →
    ∀ x ∈ cellVertices ε (S.η ω) D, ∀ t : ℝ, 0 < t →
      f x ≤ boundarySupNear ε (S.η ω) D f x t
        + A * discreteSupNorm ε (S.η ω) D f * (t / infDist (vertexPoint ε (S.η ω) x) (frontier D)) ^ (-ν)}

end FirstPass36
end MatedCRT
