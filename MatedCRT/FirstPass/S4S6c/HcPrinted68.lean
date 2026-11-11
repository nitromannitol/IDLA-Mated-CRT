import MatedCRT.FirstPass.S4S6c.HcAssembly68
import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.FirstPass.S4S6c.SuccessiveExitStop

/-!
# First pass, Lemma 6.8: the one-test bound on the sphere band

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

/-- **Almost-sure exit from a finite band** (the `hfin` input of `hc_of_band`). A finite set `A` of vertices is left
almost surely in finite time from every start, for a locally finite multigraph `m` with `m k (k+1) ≠ 0`
(`ExitNull68.exit_null_of_finite`). For the band `A = I(B_{4R/3}(z))` the finiteness of `A` is the properness of `η`
(`IsValid.ae_tendsto_cocompact`), supplied by the event bundle. -/
theorem hfin_band {m : ℤ → ℤ → ℕ} (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    {A : Set ℤ} (hA : A.Finite) (y : ℤ) :
    ∀ᵐ x ∂srwLaw m y, vExitTime A x ≠ ⊤ := by
  rw [ae_iff]
  simpa using ExitNull68.exit_null_of_finite hlf hcons hA y

/-- The sphere band of the trace argument, with centres depending on the start vertex: `y` is in the band when the
inner window `I(B_{4R_y/3}(z_y))` of its own test contains `y`. (`z_y = Q_δ(η y)` and `R_y` the good radius of `z_y`.) -/
def bandSet (H : ℤ → Set ℂ) (zc : ℤ → ℂ) (Rc : ℤ → ℝ) : Set ℤ :=
  {y | y ∈ innerVertices H (ball (zc y) (4 * Rc y / 3))}

open scoped Classical in
/-- The test-window family of the trace argument: `bandWt Y W y = W y` on the band `Y`, and `univ` off it (such
centres are unavailable; their stay region is empty, `TailWindow68.stayInRegionOf_of_not_mem`). -/
noncomputable def bandWt (Y : Set ℤ) (W : ℤ → Set ℤ) (y : ℤ) : Set ℤ := if y ∈ Y then W y else univ

open scoped Classical in
/-- The stay-set family of the trace argument: `bandAof Y A y = A` on the band `Y`, and `∅` off it. -/
noncomputable def bandAof (Y A : Set ℤ) (y : ℤ) : Set ℤ := if y ∈ Y then A else ∅

theorem bandWt_of_mem {Y : Set ℤ} {W : ℤ → Set ℤ} {y : ℤ} (hy : y ∈ Y) : bandWt Y W y = W y := by
  unfold bandWt; simp [hy]

theorem bandWt_of_not_mem {Y : Set ℤ} {W : ℤ → Set ℤ} {y : ℤ} (hy : y ∉ Y) : bandWt Y W y = univ := by
  unfold bandWt; simp [hy]

theorem bandAof_of_mem {Y A : Set ℤ} {y : ℤ} (hy : y ∈ Y) : bandAof Y A y = A := by
  unfold bandAof; simp [hy]

theorem bandAof_of_not_mem {Y A : Set ℤ} {y : ℤ} (hy : y ∉ Y) : bandAof Y A y = ∅ := by
  unfold bandAof; simp [hy]

/-- **One-test bound of the trace argument on the sphere band.** For every band vertex `y` (its test has centre
`z_y = zc y` and radius `R_y = Rc y`), the walk from `y` stays in the window `I(B_{2R_y}(z_y))` before leaving the
stay set `A` with probability at most `c`. This is `hc` of `ConfigBound68.trace_half` in the form `bandWt`/`bandAof`,
obtained pointwise from `HcAssembly68.hc_of_local`; the per-start hypotheses (`hsm`, `hgeo`, `hρ`, `hfin`, `hloc`) are
those of that lemma with the centre and radius of the start. -/
theorem hc_band_var {H : ℤ → Set ℂ} {m : ℤ → ℤ → ℕ} {A : Set ℤ} {d : ℝ} {c : ℝ≥0∞} {P : ℤ → ℂ}
    (zc : ℤ → ℂ) (Rc : ℤ → ℝ)
    (hconn : ∀ v, IsPreconnected (H v)) (hne : ∀ v, (H v).Nonempty) (hd : 0 ≤ d)
    (hsm : ∀ y, ∀ v, (closure (H v) ∩ closedBall (zc y) (2 * Rc y)).Nonempty →
      ∀ x ∈ closure (H v), ∀ y' ∈ closure (H v), dist x y' ≤ d)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (H u) ∩ closure (H v)).Nonempty)
    (hPb : ∀ b, P b ∈ H b) (hgeo : ∀ y, 4 * Rc y / 3 + d + Rc y / 4 + d < 2 * Rc y)
    (hρ : ∀ y, d < Rc y / 4)
    (hfin : ∀ y ∈ bandSet H zc Rc,
      ∀ᵐ x ∂srwLaw m y, vExitTime (innerVertices H (ball (zc y) (4 * Rc y / 3))) x ≠ ⊤)
    (hloc : ∀ y ∈ bandSet H zc Rc,
      ∀ b ∈ {b : ℤ | (closure (H b) ∩ Metric.sphere (zc y) (4 * Rc y / 3)).Nonempty},
      srwLaw m b (TestBound68.stayIn (fun b => innerVertices H (ball (P b) (Rc y / 4))) A b) ≤ c) :
    ∀ y ∈ bandSet H zc Rc, srwLaw m y (SuccessiveExitStop.stayInRegionOf
      (bandWt (bandSet H zc Rc) (fun y => innerVertices H (ball (zc y) (2 * Rc y))))
      (bandAof (bandSet H zc Rc) A) y) ≤ c := by
  intro y hy
  have h := HcAssembly68.hc_of_local hconn hne hd (hsm y) hadj hPb (hgeo y) (hρ y) hy (hfin y hy) (hloc y hy)
  simp only [SuccessiveExitStop.stayInRegionOf, bandWt_of_mem hy, bandAof_of_mem hy]
  exact h

end HcPrinted68

end MatedCRT

#print axioms MatedCRT.HcPrinted68.hc_of_band
