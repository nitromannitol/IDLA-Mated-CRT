import MatedCRT.FirstPass.S3i.Proof
import MatedCRT.FirstPass.S3i.LensDefs
import MatedCRT.FirstPass.S3i.GoodEvent

/-!
# The quenched bounds on the good event (plan section 7)

* `QuenchedBoundsOnGoodStmt`: plan Lemma 7 (section 7, `quenchedBoundsOnGood_fp36`, `S3i/QuenchedBounds.lean`),
  as a named input with the plan's exact type.

Terminology: quenched law `srwLaw` and exit time (Armstrong-Kuusi-Mourrat).
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-- **Lemma 7 of the plan (section 7), a named input until `quenchedBoundsOnGood_fp36` lands.** On a good environment
`FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω`, with `ε` small: the walk from the start vertex leaves the disc with probability one
(first estimate: exactly zero), and the far-exit event has quenched mass at most `A 96^ν ε^{νb/2}`. -/
def QuenchedBoundsOnGoodStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {ρ₀ ρ₁ b ν A r ε : ℝ} {z y : ℂ} {ω : Ω},
    0 < ε → 0 < b → 0 < ν → 0 < A → 0 < r → ρ₀ < ρ₁ → 0 < S.mε ε →
    64 * ε ^ b ≤ ε ^ (b / 2) → closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀ →
    FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω →
    let μ := srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
    μ {x | ¬ SameWalkGood S r z ε ω x} = 0 ∧
      μ {x | SameWalkGood S r z ε ω x ∧
        ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)}
        ≤ ENNReal.ofReal (A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2))


end FirstPass36
end MatedCRT
