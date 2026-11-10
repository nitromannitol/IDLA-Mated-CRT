import MatedCRT.FirstPass.S3i.Proof
import MatedCRT.Defs.WalkDisconnection

/-!
# Lemma 3.6, boundary-excursion half of `hLens` (fp-S3i-hLens-excursion, owner z1)

Source: `docs/campaign/LEMMA36-REPLACEMENT.md`, Lemma `lem:excursion` (l.259-339), exponents `eq:exponents`
(l.182-258), inputs (l.122-181). With `b = min a β`, `d = ε^a`, `ℓ = 100 d + ε^β` and `s = ε^{b/2}`, the lemma bounds the
far-exit event of `QuenchedLensStep` (`FirstPass36.QuenchedLensStep`, `Proof.lean:240`) by `C (ℓ/s)^ν = C ε^{νb/2}`,
with `ν = -log(1-p)/log 2`.

Terminology: quenched law `srwLaw (S.mult ε ω) v` of the walk from `v` (Armstrong-Kuusi-Mourrat); one-stage annulus
barrier and disconnection (Gwynne-Miller-Sheffield, arXiv:1807.07511, Lemma 3.11, (3.35)); interior cell vertices
`V^ε(D) \ V^ε(∂D)` on the disc `D = ball z r` (Armitage-Gardiner).

Pointwise good-event properties (the part of `E_ε` used by the proof). Not the event itself: `E_ε` and its probability
bound are the business of the good-event file (q4). The two properties:
* cell size: every cell meeting `B_{ρ₁}(0)` has diameter at most `ε^a` (LEMMA36 (b));
* annulus disconnection (LEMMA36 (c), GMS (3.35)), in the form of `GMSUniformRate.lean:13`: every vertex of the
  disc `B_s(c)` (`ε^β ≤ s`, `B_{2s}(c) ⊆ B_{ρ₁}`) starts a walk that disconnects the inner vertices from the outer
  ones with probability at least `p`.

Proof route (not yet written; the pieces exist in `Proofs/Sec3/ConvergenceHarmonicFunctions`): the displacement tail
is `srwLaw_discrete_exit_excursion_le` (`DiscreteExitExcursion.lean:13`) with threshold `R = ε^{b/2}/2`, whose boundary
hypothesis `hbound` is the nested-disk survival `measure_nested_disk_survival_le_of_disconnection`
(`AnnulusBarriers.lean:335`, product `(1-p)^{n+1}`) over dyadic radii `2^j ℓ`. The planar observation sits inside the
geometric hypothesis `hgeom` of that lemma. The reduction `srwLaw_sameWalkExitDiscrepancy_le_of_excursion_tail`
(`RateTailReduction.lean:117`) is the discrepancy form. The statement's event is a subset of the discrete excursion
event, so the `SameWalkGood` conjunct and the a.s. finiteness of the exit time are not needed.

Status: STATEMENT ONLY in this file. The proof of `QuenchedLensExcursionStmt` is open (see the report).
Note: the excursion proof of LEMMA36 l.259-339 does not invoke `FrozenOneSidedBoundaryContinuity` (hBE); it uses the
annulus input (c) and the strong Markov property. hBE enters only at Step 5 of `QuenchedLensStep`.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The pointwise good-event properties at scale `ε` and environment `ω` used by the excursion lemma: the cell-size
bound (LEMMA36 (b)), and the simultaneous annulus disconnection (LEMMA36 (c), GMS (3.35), in the form of
`GMSUniformRate.lean:13`): for every disc `B_s(c)` with `c ∈ B_{ρ₁}`, `ε^β ≤ s`, `B_{2s}(c) ⊆ B_{ρ₁}`, and every
vertex `v` of `B_s(c)`, the walk from `v` disconnects `V(∂B_{s/2}(c))` from `V(∂B_{2s}(c))` with probability `≥ p`. -/
def LensExcursionGood {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ₁ a β p : ℝ) (ε : ℝ) (ω : Ω) :
    Prop :=
  (∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ₁).Nonempty → diam (cell ε (S.η ω) k) ≤ ε ^ a) ∧
  (∀ (c : ℂ) (s : ℝ), c ∈ ball 0 ρ₁ → ε ^ β ≤ s → ball c (2 * s) ⊆ ball 0 ρ₁ →
    ∀ v ∈ cellVertices ε (S.η ω) (ball c s),
      ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) v {path |
        ∀ y ∈ cellVertices ε (S.η ω) (sphere c (s / 2)),
          walkDisconnectsBeforeHit (S.mult ε ω)
            (cellVertices ε (S.η ω) (sphere c (2 * s))) y path})

/-- **Boundary-excursion half of `hLens` (statement).** For a disc `ball z r ⊆ ball 0 ρ` with `ρ < ρ₁ < 1`, and
`p ≤ 1/2`, there are `C, ε₀` such that for `0 < ε < ε₀` and every environment `ω` with the good-event properties
`LensExcursionGood` at scale `ε`, and with the start vertex `vertexOf ε (S.η ω) y` an interior cell vertex of `ball z r`,
the quenched probability that the walk has a same-walk good exit with displacement `> ε^{b/2}/2` from the projected
exit point is at most `C ε^{νb/2}`, where `b = min a β` and `ν = -log(1-p)/log 2`. -/
def QuenchedLensExcursionStmt : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ ρ₁ a β p r : ℝ) (z y : ℂ),
    0 < ρ → ρ < ρ₁ → ρ₁ < 1 → 0 < r → ball z r ⊆ ball 0 ρ → 0 < a → 0 < β → 0 < p → p ≤ 1 / 2 →
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ ω : Ω,
      LensExcursionGood S ρ₁ a β p ε ω →
      vertexOf ε (S.η ω) y ∈ interiorCellVertices ε (S.η ω) (ball z r) →
      srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
          {x | SameWalkGood S r z ε ω x ∧
            ε ^ (min a β / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)} ≤
        ENNReal.ofReal (C * ε ^ ((-Real.log (1 - p) / Real.log 2) * min a β / 2))

end FirstPass36
end MatedCRT
