import MatedCRT.FirstPass.S4S6c.FiniteExitMomentHoneMain68
import MatedCRT.FirstPass.S4S6c.HoneWalk
import MatedCRT.FirstPass.S6r.OneTest.Concrete

/-!
# Measurability of the walk-centred test count (fp-S4S6c-hmeasBall)

This file discharges the named binder `hmeasBall` of
`FiniteExitMomentHoneMain68.hmom_pair_of_finiteDomain`. The test count of the walk-centred test ball is
`σ_D(ρ_T(w), post-T path(w))`, where `σ_D` is the exit time of the discrete interior of the test ball
(`Lemma68Window.ballExitSigma`), `ρ_T = (R_T, η(ε X_T))` is the walk-centred parameter
(`Lemma68Window.walkParam`) and the post-`T` path is the strong Markov shift (`Lemma68Window.postTimePath`).
The measurability is the composition of three measurable maps: `σ_D` in the parameter and the path,
`ρ_T` (measurable with respect to the stopped σ-algebra `𝓕_T`, hence in the ambient σ-algebra of `ℕ → ℤ`),
and the post-`T` path.
-/

namespace MatedCRT
namespace BallExitMeas68

open MeasureTheory Set Filter FiniteExitMomentHone68
open Lemma68WalkBridge Lemma68Window Function
open scoped ENNReal

/-- **Measurability of the walk-centred test count (hmeasBall).** If `T` is a stopping time of the
coordinate filtration and the radius `R` is `𝓕_T`-measurable, then `w ↦ σ_D(ρ_T(w), post-T path(w))` is
measurable on the ambient σ-algebra of `ℕ → ℤ`. -/
theorem measurable_ballExitSigma_walkParam (ε : ℝ) (η : ℝ → ℂ) (hη : Continuous η) (hε : 0 < ε)
    {T : (ℕ → ℤ) → ℕ∞} (hT : IsStoppingTime coordFiltration T)
    {R : (ℕ → ℤ) → ℝ} (hR : Measurable[hT.measurableSpace] R) :
    Measurable fun w : ℕ → ℤ =>
      ballExitSigma ε η (walkParam ε η R T w) (postTimePath (fun n w => w n) T w) := by
  have hρ : Measurable (walkParam ε η R T) := fun s hs =>
    hT.measurableSpace_le _ (measurable_walkParam hT hR ε η hs)
  have hP : Measurable fun w : ℕ → ℤ => (walkParam ε η R T w, postTimePath (fun n w => w n) T w) :=
    hρ.prodMk (measurable_postTimePath_stop hT)
  have hB : Measurable fun q : (ℝ × ℂ) × (ℕ → ℤ) => ballExitSigma ε η q.1 q.2 :=
    measurable_ballExitSigma ε η hη hε
  -- The composition is stated with its maps fixed: an unannotated `exact hB.comp hP` makes the unifier solve
  -- `?g ∘ ?f =?= fun w => ballExitSigma ...` by unfolding `ballExitSigma` (whnf timeout).
  have hcomp : Measurable ((fun q : (ℝ × ℂ) × (ℕ → ℤ) => ballExitSigma ε η q.1 q.2) ∘
      fun w : ℕ → ℤ => (walkParam ε η R T w, postTimePath (fun n w => w n) T w)) :=
    hB.comp hP
  exact hcomp

/-- **Hone binders `hmom1`, `hmom2` on finite test domains, with `hmeasBall` discharged
(fp-S4S6c-hmeasBall).** Same statement as `FiniteExitMomentHoneMain68.hmom_pair_of_finiteDomain` without the
binder `hmeasBall`; the measurability of the test count is `measurable_ballExitSigma_walkParam`. -/
theorem hmom_pair_of_finiteDomain_meas {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (hp : Filter.Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hε : 0 < ε) (a : ℤ)
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {R : ℕ → (ℕ → ℤ) → ℝ} (hR : ∀ k, Measurable[(hT k).measurableSpace] (R k))
    (hTdom : ∀ k, ∃ D : Set ℤ, D.Finite ∧ ∀ w, T k w < ⊤ → T k w ≤ vExitTime D w)
    (hRbd : ∀ k, ∃ s : ℝ, ∀ w, T k w < ⊤ → R k w ≤ s)
    (k : ℕ) :
    Integrable ({w : ℕ → ℤ | T k w < ⊤}.indicator (fun w =>
        ((ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ)))
      (srwLaw m a) ∧
    Integrable ({w : ℕ → ℤ | T k w < ⊤}.indicator (fun w =>
        ((ballExitSigma ε η (walkParam ε η (R k) (T k) w) (postTimePath (fun n w => w n) (T k) w) : ℕ) : ℝ) ^ 2))
      (srwLaw m a) :=
  FiniteExitMomentHoneMain68.hmom_pair_of_finiteDomain hlf hcons hη hp hε a hT hR hTdom hRbd
    (fun j => measurable_ballExitSigma_walkParam ε η hη hε (hT j) (hR j)) k

end BallExitMeas68
end MatedCRT
