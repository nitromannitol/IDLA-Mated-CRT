import MatedCRT.FirstPass.S3c.ExitTimeCore

/-!
# The exit-moment input `hmomS` of the one-test bound (fp-S4S6c-hone-momS)

`ShellHoneInst68.shellOneTest_of_direct` takes the pathwise exit-moment bound `hmomS` (ShellHoneInst68.lean:127)
for every test domain `D ⊆ ball 0 1`. The source (Lemma 2.18, first clause; Draft `ExitTimeUpperBoundStmt`,
MatedCRT/Draft/Section2.lean) gives the same bound only for `D ⊆ B_ρ` with `ρ < 1`, the constant `C` depending on `ρ`
(`S3cBridge.ExitMomentClause`, MatedCRT/FirstPass/S3c/ExitTimeCore.lean).

This file proves the `B_ρ` form from the bootstrap of `S3cBridge.clauses_of_events` (committed there) and
makes the binder change explicit. The finite-domain moment lemmas of `FiniteExitMoment68` only give finiteness of the
exit-time moments, not the constant `N! C^N ε^{-N}`, so they do not discharge `hmomS`.
-/

namespace MatedCRT
namespace HoneMomS68

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-- **`hmomS` in the `B_ρ` form (binder change).** The pathwise exit-moment clause at radius `ρ` gives the shape of
the binder `hmomS` (ShellHoneInst68.lean:127) with `D ⊆ ball 0 ρ` in place of `D ⊆ ball 0 1`, for every index `k`
and every `ω` in any set `S k` (the binder's `prefixSet` membership is carried by `S`). -/
theorem hmomS_ballRho_of_clause {ι : Type*} (S : ι → Set (ℕ → ℤ)) {m : ℤ → ℤ → ℕ} {μ : Measure ℂ}
    {η : ℝ → ℂ} {ε α C ρ : ℝ} (h : S3cBridge.ExitMomentClause m μ η ε α C ρ) :
    ∀ (k : ι) (ω : ℕ → ℤ), ω ∈ S k →
      ∀ D : Set ℂ, MeasurableSet D → D ⊆ ball 0 ρ → ENNReal.ofReal (ε ^ α) ≤ μ D →
      ∀ a ∈ cellVertices ε η D, ∀ N : ℕ,
        exitTimeMoment m (interiorCellVertices ε η D) a N ≤
          ENNReal.ofReal (N.factorial * C ^ N * ε ^ (-(N : ℝ))) *
            (⨆ z' ∈ D, ∫⁻ w in Metric.thickening (ε ^ α) D,
              ENNReal.ofReal (Real.log (1 / ‖z' - w‖) + 1) ∂μ) ^ N :=
  fun _ _ _ => h

/-- **The pathwise exit-moment clause at radius `ρ` from the bootstrap inputs.** `S3cBridge.clauses_of_events`
(ExitTimeCore.lean) moves the clause from the exponent `α₀` (inputs `hE₁` at radius `ρ`, `hE₂` at radius `ρ' > ρ`)
to the exponent `α` with constant `C` (`α ≤ α₀`, `2α < α₀`), using the volume lower bound `hvol` on
`B_{1-ε^{2α}}`. The named inputs are `hE₁`, `hE₂` and `hvol`; the side conditions are arithmetic. -/
theorem exitMomentClause_ballRho_of_clauses (m : ℤ → ℤ → ℕ) (μ : Measure ℂ) (η : ℝ → ℂ) (hη : Continuous η)
    {ε α α₀ b C₁ C₂ C ρ ρ' : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hα : 0 < α) (hαα₀ : α ≤ α₀)
    (h2α : 2 * α < α₀) (h2αb : 2 * α * b ≤ α₀) (hρ'1 : ρ' < 1) (hδ : ε ^ (2 * α) < ρ' - ρ)
    (hα_half : ε ^ α ≤ 1 / 2) (hC₁pos : 0 ≤ C₁) (hC₁ : C₁ ≤ C) (hC₂ : C₂ ≤ C)
    (hE₁ : S3cBridge.ExitMomentClause m μ η ε α₀ C₁ ρ)
    (hE₂ : S3cBridge.ExitMomentClause m μ η ε α₀ C₂ ρ')
    (hvol : ∀ z ∈ ball (0 : ℂ) (1 - ε ^ (2 * α)),
      ENNReal.ofReal ((ε ^ (2 * α)) ^ b) ≤ μ (ball z (ε ^ (2 * α)))) :
    S3cBridge.ExitMomentClause m μ η ε α C ρ :=
  (S3cBridge.clauses_of_events m μ η hη hε0 hε1 hα hαα₀ h2α h2αb hρ'1 hδ hα_half hC₁pos hC₁ hC₂ hE₁ hE₂ hvol).1

end HoneMomS68
end MatedCRT
