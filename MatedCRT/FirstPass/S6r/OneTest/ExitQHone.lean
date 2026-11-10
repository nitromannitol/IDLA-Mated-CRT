import MatedCRT.FirstPass.S6r.OneTest.ParamOneTest

/-!
# The hone hypothesis of `exitQ_le_pow`, from the parametric one-test estimate (q2, S4S6c/WalkBridge68.lean)

`exitQ_le_pow` takes, for every `k ≤ n`, the bound `μ[1_{testFail (T k) (L k)} | 𝓕_{T k}] x ≤ 1 - q` on the event
`x ∈ prefixSet`, with `μ = srwLaw (S.mult ε ω) i.a` (the environment `ω` is fixed, so the multigraph `m` is fixed).
Here the test end is `L k = testEndParam (σ k) (ρ k) (T k)`: the exit time `σ k` of the test ball depends on the
`𝓕_{T k}`-measurable parameter `ρ k` (radius and centre, PRO step 8). The bound is `conditional_one_test_param` with
`q = q0 / (1 + log (1/r))²`; the moment bounds `hstep1`, `hstep2` remain named hypotheses (z1 / z12).
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MatedCRT
namespace Lemma68Window

open Lemma68WalkBridge

/-- The hone hypothesis `hone` of `exitQ_le_pow`, for all `k ≤ n` at once, from the parametric one-test estimate
(fixed environment `m`, walk law `srwLaw m a`, obstacle set `A`). -/
theorem hone_exitQ_of_param_family {P : Type*} [MeasurableSpace P] (m : ℤ → ℤ → ℕ) (a : ℤ) (A : Set ℤ)
    (hA : MeasurableSet A) (n : ℕ) {τU : (ℕ → ℤ) → ℕ∞} {c C ε r q0 q : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (hq0c : q0 ≤ c ^ 2 / (4 * C)) (hq : q = q0 / (1 + Real.log (1 / r)) ^ 2)
    {σ : ℕ → P → (ℕ → ℤ) → ℕ} (hσ : ∀ k, Measurable (fun q : P × (ℕ → ℤ) => σ k q.1 q.2))
    {T : ℕ → (ℕ → ℤ) → ℕ∞} (hT : ∀ k, IsStoppingTime coordFiltration (T k))
    {ρ : ℕ → (ℕ → ℤ) → P} (hρ : ∀ k, Measurable[(hT k).measurableSpace] (ρ k))
    {mm R : ℕ → (ℕ → ℤ) → ℝ}
    (hLst : ∀ k, IsStoppingTime coordFiltration (testEndParam (σ k) (ρ k) (T k)))
    (hint1 : ∀ k, Integrable (testCountParam A (σ k) (ρ k) (T k)) (srwLaw m a))
    (hint2 : ∀ k, Integrable ({w | T k w < ⊤}.indicator
      (fun w => occCount A (σ k (ρ k w)) (postTimePath (fun n w => w n) (T k) w) ^ 2)) (srwLaw m a))
    (hm : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU, 0 < mm k ω)
    (hRr : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      r ^ 2 ≤ R k ω ∧ R k ω ≤ 1)
    (hstep1 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      c * ε⁻¹ * mm k ω ≤ ∫ w, occCount A (σ k (ρ k ω)) w ∂(srwLaw m (ω (T k ω).toNat)))
    (hstep2 : ∀ k, ∀ ω ∈ prefixSet (fun (j : ℕ) (w : ℕ → ℤ) => w j) A (T k) τU,
      ∫ w, occCount A (σ k (ρ k ω)) w ^ 2 ∂(srwLaw m (ω (T k ω).toNat))
        ≤ C * ε⁻¹ ^ 2 * (1 + Real.log (1 / R k ω)) ^ 2 * mm k ω ^ 2) :
    ∀ k ≤ n, ∀ᵐ x ∂srwLaw m a, x ∈ prefixSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k) τU →
      (srwLaw m a)[(testFailSet (fun (j : ℕ) (y : ℕ → ℤ) => y j) A (T k)
        (testEndParam (σ k) (ρ k) (T k))).indicator (fun _ => (1 : ℝ)) | (hT k).measurableSpace] x
        ≤ 1 - q := by
  intro k _
  subst hq
  exact conditional_one_test_param m a hA (hσ k) (hT k) (hρ k) hc hC hε hr hr1 hq0c (hLst k)
    (hint1 k) (hint2 k) (hm k) (hRr k) (hstep1 k) (hstep2 k)

end Lemma68Window
end MatedCRT
