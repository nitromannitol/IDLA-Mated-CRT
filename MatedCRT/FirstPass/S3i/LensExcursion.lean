import MatedCRT.FirstPass.S3i.Proof
import MatedCRT.Proofs.Sec3.ConvergenceHarmonicFunctions.ActualAnnulusBarrier

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
* annulus stay barrier `AnnulusStayGood` (LEMMA36 (c) in its one-stage form; the planar observation that the
  disconnection input forces a visit to the enlarged boundary `∂O`, `O = B_{r+3d}(z)`, is built into it through
  `MatedCRTEnv.IsValid.ae_annulus_stay_le_of_disconnection`, `ActualAnnulusBarrier.lean:81`).

Status: STATEMENT ONLY in this file. The proof of `QuenchedLensExcursionStmt` is open (see the report).
Note: the excursion proof of LEMMA36 l.259-339 does not invoke `FrozenOneSidedBoundaryContinuity` (hBE); it uses the
annulus input (c) and the strong Markov property. hBE enters only at Step 5 of `QuenchedLensStep`.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- The pointwise good-event properties at scale `ε` and environment `ω` used by the excursion lemma: the cell-size
bound (LEMMA36 (b)) and the annulus stay barrier (LEMMA36 (c), one-stage form, `AnnulusStayGood`). -/
def LensExcursionGood {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (ρ₁ a β p : ℝ) (ε : ℝ) (ω : Ω) :
    Prop :=
  (∀ k : ℤ, (cell ε (S.η ω) k ∩ ball 0 ρ₁).Nonempty → diam (cell ε (S.η ω) k) ≤ ε ^ a) ∧
    AnnulusStayGood S ε ρ₁ β p ω

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
