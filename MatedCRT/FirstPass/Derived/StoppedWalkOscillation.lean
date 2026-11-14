import MatedCRT.FirstPass.Derived.ExitCouplingOscillation
import MatedCRT.FirstPass.Derived.ExitCouplingNoShortTravel

/-!
# Oscillation of the stopped interpolated walk (Berestycki–Gwynne (2020), Proposition 6.5)

Quenched form of the equicontinuity of paths (BG20 Proposition 6.5) for the linearly interpolated walk of
speed `m` stopped at the exit time `τ_Y` from the interior vertices `Y = V^ε(B_{ρ0})`: the walk started at `x`
has oscillation at most `3 s + J` over windows of length `ρ` before time `τ_Y / m` outside probability
`ψ₀ + K q`, where `ψ₀` bounds the failure of `τ_Y ≤ σ_K` (the bound (6.36)), `q` bounds the exit from the balls
`B_s(η(y))` within `g ≥ m ρ + 2` steps (Lemma 6.11), and `J` bounds the embedded length of the edges out of `Y`.

* `srwLaw_stoppedOscillation_le_of_shortTravel`: oscillation event of the interpolation from the
  short-travel event (deterministic bridge of `ExitCouplingOscillation`, without the walk-good conjunction);
* `srwLaw_stoppedOscillation_le`: with the short-travel probability of `srwLaw_exists_shortTravel_le`.
-/

set_option autoImplicit false

namespace MatedCRT.FirstPass.Derived

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MatedCRT.ExitDecomposition MatedCRT.ExitCouplingEvents MatedCRT.ExitCouplingOscillation
  MatedCRT.SuccessiveExitGaps MatedCRT.InteriorCellGeometry

/-- **Oscillation of the stopped interpolated walk from the short-travel event.**  If two vertices visited at
steps `i < j < i + g`, `j ≤ τ_A`, are at embedded distance more than `D` with probability at most `p`, and
`m ρ + 2 ≤ g`, then the interpolated walk of speed `m` has oscillation more than `D` over some window of length
at most `ρ` before time `τ_A / m` with probability at most `p`. -/
theorem srwLaw_stoppedOscillation_le_of_shortTravel (mult : ℤ → ℤ → ℕ) (z : ℤ) (v : ℤ → ℂ) {m : ℝ≥0}
    (hm : 0 < m) (A : Set ℤ) (ρ : ℝ≥0) {D : ℝ} (hD : 0 ≤ D) {g : ℕ} (hg : (m : ℝ) * ρ + 2 ≤ g)
    {p : ℝ≥0∞}
    (hshort : srwLaw mult z {X | ∃ i j : ℕ, i < j ∧ j < i + g ∧ (j : ℕ∞) ≤ vExitTime A X ∧
      D < dist (v (X i)) (v (X j))} ≤ p) :
    srwLaw mult z {X | ∃ s t : ℝ≥0, s ≤ ((vExitTime A X).toNat : ℝ≥0) / m ∧
      t ≤ ((vExitTime A X).toNat : ℝ≥0) / m ∧ dist s t ≤ ρ ∧
      D < dist (interpPathFn v m X s) (interpPathFn v m X t)} ≤ p := by
  refine le_trans (measure_mono ?_) hshort
  intro X hX
  obtain ⟨s, t, hs, ht, hst, hlt⟩ := hX
  by_contra hno
  have hno' : ∀ i j : ℕ, i < j → j < i + g → (j : ℕ∞) ≤ vExitTime A X →
      dist (v (X i)) (v (X j)) ≤ D := by
    intro i j hij hjg hjT
    by_contra hcon
    exact hno ⟨i, j, hij, hjg, hjT, not_le.1 hcon⟩
  have hNle : ∀ j : ℕ, j ≤ (vExitTime A X).toNat → (j : ℕ∞) ≤ vExitTime A X := by
    intro j hj
    by_cases hv : vExitTime A X = ⊤
    · rw [hv]
      exact le_top
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hv
      have hTk : (vExitTime A X).toNat = k := by rw [← hk]; simp
      rw [← hk]
      exact_mod_cast hTk ▸ hj
  have hmN : ∀ u : ℝ≥0, u ≤ ((vExitTime A X).toNat : ℝ≥0) / m →
      (m : ℝ) * u ≤ ((vExitTime A X).toNat : ℝ) := by
    intro u hu
    have := (le_div_iff₀ hm).1 hu
    have h2 : (u : ℝ) * m ≤ ((vExitTime A X).toNat : ℝ) := by exact_mod_cast this
    linarith
  have hgood := dist_interpPathFn_le_of_close (v := v) (m := m) (X := X) (N := (vExitTime A X).toNat)
    (g := g) (D := D) (ρ := ρ) ρ.coe_nonneg hD hg
    (fun i j hij hjg hjN => hno' i j hij hjg (hNle j hjN)) (hmN s hs) (hmN t ht) hst
  exact absurd hlt (not_lt.2 hgood)

/-- **No oscillation of the stopped walk (BG20 Proposition 6.5, quenched).**  Let `Y = V^ε(B_{ρ0})` be the
interior vertices, `A y = V^ε(B_s(η(y)))`.  If `τ_Y ≤ σ_K` outside probability `ψ₀` for the walk from `x`
(the bound (6.36)), every `y ∈ Y` leaves `A y` within `g` steps with probability at most `q` (Lemma 6.11), every
edge out of `Y` has embedded length at most `J` and `m ρ + 2 ≤ g`, then the interpolated walk from `x` has
oscillation more than `3 s + J` over a window of length at most `ρ` before the exit time from `Y` with probability
at most `ψ₀ + K q`. -/
theorem srwLaw_stoppedOscillation_le {mult : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε)
    (hη : Continuous η) {ρ0 s J : ℝ} (hs0 : 0 ≤ s) (hJ0 : 0 ≤ J) {m : ℝ≥0} (hm : 0 < m) (ρ : ℝ≥0)
    {g K : ℕ} (hg : (m : ℝ) * ρ + 2 ≤ g) {ψ₀ q : ℝ≥0∞} (x : ℤ)
    (hJ : ∀ w ∈ interiorCellVertices ε η (ball (0 : ℂ) ρ0), ∀ w' : ℤ, mult w w' ≠ 0 →
      dist (vertexPoint ε η w) (vertexPoint ε η w') ≤ J)
    (h0 : srwLaw mult x {X | ¬ vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X ≤
      succExit (fun w => interiorCellVertices ε η (ball (vertexPoint ε η w) s)) K X} ≤ ψ₀)
    (hq : ∀ w ∈ interiorCellVertices ε η (ball (0 : ℂ) ρ0),
      srwLaw mult w {X | vExitTime (interiorCellVertices ε η (ball (vertexPoint ε η w) s)) X <
        (g : ℕ∞)} ≤ q) :
    srwLaw mult x {X | ∃ a b : ℝ≥0,
      a ≤ ((vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X).toNat : ℝ≥0) / m ∧
      b ≤ ((vExitTime (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) X).toNat : ℝ≥0) / m ∧
      dist a b ≤ ρ ∧ 3 * s + J < dist (interpPathFn (vertexPoint ε η) m X a)
        (interpPathFn (vertexPoint ε η) m X b)} ≤ ψ₀ + (K : ℝ≥0∞) * q := by
  have hA : ∀ w ∈ interiorCellVertices ε η (ball (0 : ℂ) ρ0),
      ∀ u ∈ interiorCellVertices ε η (ball (vertexPoint ε η w) s),
        dist (vertexPoint ε η u) (vertexPoint ε η w) ≤ s := fun w _ u hu =>
    (mem_ball.1 (vertexPoint_mem_of_mem_interiorCellVertices hε hη hu)).le
  exact srwLaw_stoppedOscillation_le_of_shortTravel mult x (vertexPoint ε η) hm _ ρ
    (by linarith) hg
    (srwLaw_exists_shortTravel_le mult x
      (fun w => interiorCellVertices ε η (ball (vertexPoint ε η w) s))
      (interiorCellVertices ε η (ball (0 : ℂ) ρ0)) g K (vertexPoint ε η) h0 hq hA hJ hJ0)

end MatedCRT.FirstPass.Derived
