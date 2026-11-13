import MatedCRT.Draft.Section3HarmonicCorrected

/-!
# Corrected Lemma 3.6: the fixed-start annealed same-walk clause

The corrected numbered Lemma 3.6 asserts only the fixed-start ANNEALED comparison, at threshold `q = b χ / 2`, with
both exit locations computed from the same unrestricted walk: no pointwise or quenched clause, no mean estimate, and no
arbitrary threshold `q`. The constant `b = b(γ) > 0` depends only on `γ`. The corrected Lemma 3.6 is then
`CorrectedHarmonicConvergenceStmt 𝒮 ∧ CorrectedHarmonicSameWalkAnnealedStmt 𝒮`.

Terminology: quenched and annealed laws (Armstrong-Kuusi-Mourrat); same-walk coupling of the killed and unrestricted
walks (Gwynne-Miller-Sheffield, arXiv:1807.07511, Section 3).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

/-- The admissible Hölder datum and start of the same-walk comparison (PRO §1.4): `ψ` is `χ`-Hölder with constant `H`
on the closed disc, `0 < χ ≤ 1`, and the start `y` lies in the open disc `B_r(z)`. -/
def AdmissibleHolderDataAndStart (r : ℝ) (z : ℂ) (ψ : ℂ → ℝ) (H χ : ℝ≥0) (y : ℂ) : Prop :=
  0 < χ ∧ χ ≤ 1 ∧ HolderOnWith H χ ψ (closedBall z r) ∧ y ∈ ball z r

open Classical in
/-- **Corrected Lemma 3.6, annealed same-walk clause** (fixed start, threshold `q = b χ / 2`). For `γ ∈ (0,2)` there is
`b = b(γ) > 0` such that for every `ρ ∈ (0,1)`, every valid environment `S` with the cone field `h` and space-filling
curve `η`, every disc `B_r(z) ⊆ B_ρ`, and every admissible datum `(ψ, H, χ, y)` (`AdmissibleHolderDataAndStart`), there
are `κ, ν, C, ε₀` such that for `0 < ε < ε₀`, the outer annealed probability (the outer integral over the environment of
the quenched probabilities of the sections, `sectionwiseOuterProb`) that the same-walk exit discrepancy exceeds
`(1 + H) ε^{bχ/2}` is at most `C (ε^κ + ε^{νb/2})`. The walk law is `srwLaw (S.mult ε ω)` started at the vertex
`vertexOf ε (S.η ω) y`. The discrepancy is `sameWalkExitDiscrepancy` (Draft/Section3HarmonicCorrected.lean). -/
def CorrectedHarmonicSameWalkAnnealedStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ b : ℝ, 0 < b ∧
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ (r : ℝ) (z : ℂ), 0 < r → ball z r ⊆ ball 0 ρ →
  ∀ (ψ : ℂ → ℝ) (H χ : ℝ≥0) (y : ℂ), AdmissibleHolderDataAndStart r z ψ H χ y →
  ∃ κ ν C ε₀ : ℝ, 0 < κ ∧ 0 < ν ∧ 0 ≤ C ∧ 0 < ε₀ ∧
  ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    sectionwiseOuterProb S.P (fun ω => srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y))
      {p | (1 + (H : ℝ)) * ε ^ (b * (χ : ℝ) / 2) < sameWalkExitDiscrepancy S r z ψ ε p.1 p.2}
    ≤ ENNReal.ofReal (C * (ε ^ κ + ε ^ (ν * b / 2)))

end FirstPass36
end MatedCRT
