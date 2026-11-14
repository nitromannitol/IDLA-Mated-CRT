import MatedCRT.FirstPass.S6j.LitUniformStartInvariance
import LatticeProb.Topology.KnotReparametrization

/-!
# Curves modulo time parametrization compared along knot sequences

Bridges from the knot reparametrization of the library (`LatticeProb.KnotReparam`) to the distance
`cmpEDist` of curves modulo time parametrization used in the uniform-start invariance principle
(`MatedCRT.GMS21UniformStartInput`).

If a path `f` stays within `a` of an anchor `p n` between consecutive knots `τ n ≤ t < τ (n+1)`, a path
`g` stays within `a` of `q n` between `σ n ≤ s < σ (n+1)`, and `dist (p n) (q n) ≤ δ`, then
`cmpEDist f g ≤ a + δ + a`. In the application (Gwynne–Miller–Sheffield, arXiv:1807.07515, end of the
proof of Theorem 3.10) the knots are the successive exit times of the walk and of the Brownian motion from
the parent blocks of the dyadic squares of side `2^{-l} |S_k|`, the anchors are the exit positions, and `a`
is the oscillation bound `2^{-l+2} |S_k|` between consecutive exit times.
-/

namespace MatedCRT.CmpEDistKnots

open MatedCRT LatticeProb.KnotReparam Set
open scoped NNReal ENNReal

/-- An increasing homeomorphism `φ` of `[0, ∞)` with `dist (f t) (g (φ t)) ≤ c` for all `t` bounds
`cmpEDist f g` by `c`. -/
theorem cmpEDist_le_of_orderIso {f g : ℝ≥0 → ℂ} (φ : ℝ≥0 ≃o ℝ≥0) {c : ℝ}
    (h : ∀ t, dist (f t) (g (φ t)) ≤ c) : cmpEDist f g ≤ ENNReal.ofReal c := by
  have hc : 0 ≤ c := dist_nonneg.trans (h 0)
  exact (iInf_le _ φ).trans (iSup_le fun t => (edist_le_ofReal hc).2 (h t))

/-- **Knot comparison of curves modulo time parametrization**, infinitely many knots. -/
theorem cmpEDist_le_of_knots {f g : ℝ≥0 → ℂ} {τ σ : ℕ → ℝ≥0} (hτ : StrictMono τ)
    (hσ : StrictMono σ) (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτu : ∀ b, ∃ n, b < τ n)
    (hσu : ∀ b, ∃ n, b < σ n) {p q : ℕ → ℂ} {a δ : ℝ} (hpq : ∀ n, dist (p n) (q n) ≤ δ)
    (hf : ∀ n, ∀ t ∈ Ico (τ n) (τ (n + 1)), dist (f t) (p n) ≤ a)
    (hg : ∀ n, ∀ s ∈ Ico (σ n) (σ (n + 1)), dist (g s) (q n) ≤ a) :
    cmpEDist f g ≤ ENNReal.ofReal (a + δ + a) := by
  obtain ⟨φ, -, hφ⟩ := exists_orderIso_dist_le_of_knots hτ hσ hτ0 hσ0 hτu hσu hpq hf hg
  exact cmpEDist_le_of_orderIso φ hφ

/-- **Knot comparison of curves modulo time parametrization**, finitely many knots
`0 = τ 0 < ⋯ < τ N` and `0 = σ 0 < ⋯ < σ N`, with tail conditions on `[τ N, ∞)` and `[σ N, ∞)` (for
paths stopped at an exit time, the tail anchors are the stopped positions). -/
theorem cmpEDist_le_of_finite_knots {f g : ℝ≥0 → ℂ} {τ σ : ℕ → ℝ≥0} {N : ℕ}
    (hτ : ∀ n < N, τ n < τ (n + 1)) (hσ : ∀ n < N, σ n < σ (n + 1)) (hτ0 : τ 0 = 0)
    (hσ0 : σ 0 = 0) {p q : ℕ → ℂ} {a δ : ℝ} (hpq : ∀ n ≤ N, dist (p n) (q n) ≤ δ)
    (hf : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), dist (f t) (p n) ≤ a)
    (hg : ∀ n < N, ∀ s ∈ Ico (σ n) (σ (n + 1)), dist (g s) (q n) ≤ a)
    (hfN : ∀ t, τ N ≤ t → dist (f t) (p N) ≤ a) (hgN : ∀ s, σ N ≤ s → dist (g s) (q N) ≤ a) :
    cmpEDist f g ≤ ENNReal.ofReal (a + δ + a) := by
  obtain ⟨φ, -, hφ⟩ :=
    exists_orderIso_dist_le_of_finite_knots hτ hσ hτ0 hσ0 hpq hf hg hfN hgN
  exact cmpEDist_le_of_orderIso φ hφ

/-- **Stopped paths compared at their knots.** Let `f` be constant from `τ N` on and `g` constant from
`σ N` on. If the knot positions satisfy `dist (f (τ n)) (g (σ n)) ≤ δ` for `n ≤ N` and both paths have
oscillation at most `a` on each knot interval, then `cmpEDist f g ≤ a + δ + a`. -/
theorem cmpEDist_le_of_finite_knots_of_stopped {f g : ℝ≥0 → ℂ} {τ σ : ℕ → ℝ≥0} {N : ℕ}
    (hτ : ∀ n < N, τ n < τ (n + 1)) (hσ : ∀ n < N, σ n < σ (n + 1)) (hτ0 : τ 0 = 0)
    (hσ0 : σ 0 = 0) {a δ : ℝ} (ha : 0 ≤ a) (hpq : ∀ n ≤ N, dist (f (τ n)) (g (σ n)) ≤ δ)
    (hf : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), dist (f t) (f (τ n)) ≤ a)
    (hg : ∀ n < N, ∀ s ∈ Ico (σ n) (σ (n + 1)), dist (g s) (g (σ n)) ≤ a)
    (hfN : ∀ t, τ N ≤ t → f t = f (τ N)) (hgN : ∀ s, σ N ≤ s → g s = g (σ N)) :
    cmpEDist f g ≤ ENNReal.ofReal (a + δ + a) :=
  cmpEDist_le_of_finite_knots (p := fun n => f (τ n)) (q := fun n => g (σ n)) hτ hσ hτ0 hσ0 hpq
    hf hg (fun t ht => by rw [hfN t ht, dist_self]; exact ha)
    (fun s hs => by rw [hgN s hs, dist_self]; exact ha)

end MatedCRT.CmpEDistKnots
