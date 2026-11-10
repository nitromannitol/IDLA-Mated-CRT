import MatedCRT.FirstPass.S4S6c.Chain68
import MatedCRT.FirstPass.S4S6c.TailWindow68

/-!
# One window configuration of the printed Lemma 6.8 (q2, task fp-S4S6c-envscaling-6-7-6-8; LEMMA68 C3, D1-D2)

For one configuration (a cluster `F = fillCells Θ` in the plane, cells of diameter `d < r/2`, the test windows `Wt y`
and regions `Aof y` of the successive tests, the good event `Good` of legal trajectories) this file proves the
deterministic bound

  `1/2 ≤ P_a( the walk hits V(U₂) \ (S' ∪ Θ) before exiting V(U₂) )`, `a ∈ vClosure Θ`, `U₂ = thickening r F`,

from the one-test bound `hc` for every centre, the finiteness and availability of the test starts on `Good`, and the
window containment `Wt y ⊆ V(U₂) \ Θ`, `Aof y = S' \ Θ` on the band `Y`. The probabilistic inputs (`hc`, the good event)
are hypotheses here; their derivation (per-centre bound from the good annulus cover, the band geometry, the uniform
event) is the remaining work of `Uniform68`.

The start `b` enters only through the good event: the test windows and the successive exit times `τ` do not depend
on the start, so the same `hc`, `N`, `Y` serve every frontier start (`hGood` is required for each frontier start).
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT

open WalkPotential
open MatedCRT.SuccessiveExitStop MatedCRT.AmplCutoff

namespace ConfigBound68

/-- **Frontier bound of one configuration.** Every frontier start `b ∈ V(∂U₁)` has walk probability at most `1/2` of
staying in `S' \ Θ` until the exit of `V(U₂) \ Θ`, by `TailWindow68.printed68_tail_bound_window`. -/
theorem frontier_half {cell : ℤ → Set ℂ} {F : Set ℂ} {Θ S' : Set ℤ} {r : ℝ} (m : ℤ → ℤ → ℕ)
    (Wt Aof : ℤ → Set ℤ) (Y : Set ℤ)
    (τ : ℕ → (ℕ → ℤ) → ℕ∞) (S : ℕ → Set (ℕ → ℤ))
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ (N : ℕ) (x : ℕ → ℤ) (i : ℕ), τ N x = (i : ℕ∞) →
      τ (N + 1) x = (i : ℕ∞) + vExitTime (Wt (x i)) (pathShift i x))
    (hτtop : ∀ N x, τ N x = ⊤ → τ (N + 1) x = ⊤)
    (hS0 : S 0 = univ)
    (hSsucc : ∀ N, S (N + 1) = S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ stayInRegionOf Wt Aof (x k)})
    {q0 ζ : ℝ} (hq0 : 0 < q0) (hq0' : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hrA : r ≤ (q0 / 200 * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ))
    (hc : ∀ y ∈ Y, srwLaw m y (stayInRegionOf Wt Aof y) ≤
      ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2))
    (hAY : ∀ y ∉ Y, Aof y = ∅) (hWY : ∀ y ∉ Y, Wt y = univ)
    (N : ℕ) (hN : r ^ (-ζ) / 200 ≤ N)
    (Good : Set (ℕ → ℤ))
    (hGood : ∀ b ∈ FrontierSeparation.frontierVerts cell (Metric.thickening (r / 2) F),
      srwLaw m b Goodᶜ = 0)
    (hfin : ∀ x ∈ Good, ∀ j < N, τ j x ≠ ⊤)
    (hYvis : ∀ x ∈ Good, ∀ j < N, ∀ k : ℕ, τ j x = k → x k ∈ Y)
    (hWU : ∀ y ∈ Y, Wt y ⊆ FrontierSeparation.meetVerts cell (Metric.thickening r F) \ Θ)
    (hAof : ∀ y ∈ Y, Aof y = S' \ Θ) :
    ∀ b ∈ FrontierSeparation.frontierVerts cell (Metric.thickening (r / 2) F),
      srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) <
          vExitTime (FrontierSeparation.meetVerts cell (Metric.thickening r F) \ Θ) x → x n ∈ S' \ Θ} ≤
        ENNReal.ofReal (1 - 1 / 2) := by
  intro b hb
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  exact TailWindow68.printed68_tail_bound_window m b Wt Aof (S' \ Θ)
    (FrontierSeparation.meetVerts cell (Metric.thickening r F) \ Θ) Y τ S hτ0 hτsucc hτtop hS0 hSsucc
    hq0 hq0' hζ hζ' hr hr1 hrA hc hAY hWY N hN Good (hGood b hb) hfin hYvis hWU hAof

/-- **Trace bound of one configuration (deterministic core of the printed Lemma 6.8).** Under the hypotheses of
`Chain68.trace_bound_cluster_open` (cluster geometry, `a ∈ vClosure Θ`, exit almost surely finite) and the window
hypotheses of `frontier_half`, the walk from `a` visits `V(U₂) \ (S' ∪ Θ)` before exiting `V(U₂)` with probability at
least `1/2`. The constant `1/2` is the uniform `s₂` of the write-up (D1-D2). -/
theorem trace_half {m : ℤ → ℤ → ℕ} {cell : ℤ → Set ℂ} {F : Set ℂ} {Θ S' : Set ℤ} {a : ℤ} {r d : ℝ}
    (hr : 0 < r) (hd : d < r / 2)
    (hbdd : ∀ v, Bornology.IsBounded (cell v)) (hdiamA : Metric.diam (cell a) ≤ d)
    (hconn : ∀ v, IsPreconnected (cell v)) (hne : ∀ v, (cell v).Nonempty)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (cell u) ∩ closure (cell v)).Nonempty)
    (hF : ∀ k ∈ Θ, cell k ⊆ F) (ha : a ∈ vClosure m Θ)
    (hexit : ∀ᵐ x ∂srwLaw m a,
      vExitTime (FrontierSeparation.meetVerts cell (Metric.thickening r F)) x ≠ ⊤)
    (Wt Aof : ℤ → Set ℤ) (Y : Set ℤ)
    (τ : ℕ → (ℕ → ℤ) → ℕ∞) (S : ℕ → Set (ℕ → ℤ))
    (hτ0 : ∀ x, τ 0 x = 0)
    (hτsucc : ∀ (N : ℕ) (x : ℕ → ℤ) (i : ℕ), τ N x = (i : ℕ∞) →
      τ (N + 1) x = (i : ℕ∞) + vExitTime (Wt (x i)) (pathShift i x))
    (hτtop : ∀ N x, τ N x = ⊤ → τ (N + 1) x = ⊤)
    (hS0 : S 0 = univ)
    (hSsucc : ∀ N, S (N + 1) = S N ∩ {x | ∃ k : ℕ, τ N x = k ∧ pathShift k x ∈ stayInRegionOf Wt Aof (x k)})
    {q0 ζ : ℝ} (hq0 : 0 < q0) (hq0' : q0 ≤ 1) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2)
    (hr1 : r ≤ 1)
    (hrA : r ≤ (q0 / 200 * ζ ^ 2 / (16 * Real.log 2)) ^ (2 / ζ))
    (hc : ∀ y ∈ Y, srwLaw m y (stayInRegionOf Wt Aof y) ≤
      ENNReal.ofReal (1 - q0 / (1 + Real.log (1 / r)) ^ 2))
    (hAY : ∀ y ∉ Y, Aof y = ∅) (hWY : ∀ y ∉ Y, Wt y = univ)
    (N : ℕ) (hN : r ^ (-ζ) / 200 ≤ N)
    (Good : Set (ℕ → ℤ))
    (hGood : ∀ b ∈ FrontierSeparation.frontierVerts cell (Metric.thickening (r / 2) F),
      srwLaw m b Goodᶜ = 0)
    (hfin : ∀ x ∈ Good, ∀ j < N, τ j x ≠ ⊤)
    (hYvis : ∀ x ∈ Good, ∀ j < N, ∀ k : ℕ, τ j x = k → x k ∈ Y)
    (hWU : ∀ y ∈ Y, Wt y ⊆ FrontierSeparation.meetVerts cell (Metric.thickening r F) \ Θ)
    (hAof : ∀ y ∈ Y, Aof y = S' \ Θ) :
    ENNReal.ofReal (1 / 2) ≤ srwLaw m a
      {x | ∃ n : ℕ, (n : ℕ∞) < vExitTime {v | (cell v ∩ Metric.thickening r F).Nonempty} x ∧
        x n ∈ {v | (cell v ∩ Metric.thickening r F).Nonempty} \ (S' ∪ Θ)} :=
  Chain68.trace_bound_cluster_open hr hd hbdd hdiamA hconn hne hadj hF ha hexit (by norm_num) (by norm_num)
    (frontier_half m Wt Aof Y τ S hτ0 hτsucc hτtop hS0 hSsucc hq0 hq0' hζ hζ' hr hr1 hrA hc hAY hWY N hN Good
      hGood hfin hYvis hWU hAof)

end ConfigBound68

end MatedCRT

/-! ## Audit -/

#print axioms MatedCRT.ConfigBound68.frontier_half
#print axioms MatedCRT.ConfigBound68.trace_half
