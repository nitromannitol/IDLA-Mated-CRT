import MatedCRT.FirstPass.S4S6c.HcAssembly68

/-!
# First pass, Lemma 6.8: the one-test bound on the sphere band (q2, fp-S4S6c-envscaling-6-7-6-8)

The printed one-test bound `hc` of the trace argument (`ConfigBound68.trace_half`) is needed only at the vertices of the
band `Y = I(B_{4R/3}(z))` (the vertices visited at the test-start times, `hYvis`). For such a vertex it is the local
bound `hc_of_local` of `HcAssembly68`, applied at every vertex of the sphere band with the per-centre local test
(`hloc`, supplied by `HcGreen68.stayIn_le_printed_interior` once its Green and volume inputs are known). The bound is
stated for the band, not for all of `ℤ`: `TailWindow68.printed68_tail_bound_window` now takes `hc` on `Y` and the
unavailable centres off `Y` (`Aof y = ∅`, `Wt y = univ`).

Terminology: the local test is a Green-function lower bound for the walk killed on leaving the window (Armitage-Gardiner
potential theory; Berestycki-Gwynne kill the walk on leaving V(D)).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT

namespace HcPrinted68

/-- **One-test bound on the band** (`hc` of `ConfigBound68.trace_half`, restricted to the sphere band). For every
vertex `y` of the band `I(B_{4R/3}(z))`, the walk from `y` leaves the window `I(B_{2R}(z))` before it leaves the
stay region `A` with probability at most `c`, provided that every sphere-band vertex satisfies the local test `hloc`
(the bound with the smaller window `I(B_{ρ}(P b))`). The hypotheses are those of `HcAssembly68.hc_of_local`; the
exit finiteness `hfin` is the almost-sure exit statement for the band window (`ExitNull68`). -/
theorem hc_of_band {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {A : Set ℤ} {d R ρ : ℝ} {z : ℂ} {P : ℤ → ℂ} {c : ℝ≥0∞}
    (hconn : ∀ v, IsPreconnected (H v)) (hne : ∀ v, (H v).Nonempty) (hd : 0 ≤ d)
    (hsm : ∀ v, (closure (H v) ∩ closedBall z (2 * R)).Nonempty →
      ∀ x ∈ closure (H v), ∀ y' ∈ closure (H v), dist x y' ≤ d)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hPb : ∀ b, P b ∈ H b) (hgeo : 4 * R / 3 + d + ρ + d < 2 * R) (hρ : d < ρ)
    (hfin : ∀ y ∈ innerVertices H (ball z (4 * R / 3)),
      ∀ᵐ x ∂srwLaw m y, vExitTime (innerVertices H (ball z (4 * R / 3))) x ≠ ⊤)
    (hloc : ∀ b ∈ {b : ℤ | (closure (H b) ∩ Metric.sphere z (4 * R / 3)).Nonempty},
      srwLaw m b (TestBound68.stayIn (fun b => innerVertices H (ball (P b) ρ)) A b) ≤ c) :
    ∀ y ∈ innerVertices H (ball z (4 * R / 3)),
      srwLaw m y (TestBound68.stayIn (fun _ => innerVertices H (ball z (2 * R))) A y) ≤ c :=
  fun y hy => HcAssembly68.hc_of_local hconn hne hd hsm hadj hPb hgeo hρ hy (hfin y hy) hloc

end HcPrinted68

end MatedCRT

#print axioms MatedCRT.HcPrinted68.hc_of_band
