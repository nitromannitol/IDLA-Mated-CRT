import Mathlib
import MatedCRT.FirstPass.S6m.Pathwise
import MatedCRT.FirstPass.S6h.Schedule
import MatedCRT.FirstPass.S6j.FiniteExit
import MatedCRT.FirstPass.S4S6c.FrontierSeparation
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Lemma 6.8, write-up C12 for the concrete test schedule (fp-S6m, owner z10)

`concreteC12_killed` proves `Lemma68Concrete.ConcreteC12 m a ε η p r good (killed ε η Θ F0 r)`: almost surely, the
concrete exit time `T_N` of the test schedule `cfgExit` (with `N = cfgCount p r`) is strictly smaller than the exit time
`τ_U` of the killed set `U = killed ε η Θ F0 r`. The pathwise content is `Lemma68C12.pathwise_containment`
(`S6m/Pathwise.lean`); this file supplies the almost-sure inputs (legality of the walk, finiteness of the window
exits, the start `x 0 = a`) and the numerical facts of the dyadic scale (`δ = Δ(p,r)`, `s = √δ`, `N = ⌊r/(100 s)⌋`).

Named inputs (hypotheses): local finiteness `hlf` and nearest-neighbour edges `hcons` of the multiplicity `m`
(as in `cfgSchedule_valid`), properness `hproper` of `η`, continuity `hη`, adjacency of cells `hadj` (for `m`), the cell
size bound `hsize` with `d ≤ Δ/100`, the inclusion `F0 ⊇ V(Θ̄ + B_r)` and the start estimate `hdd` (from the
admissibility `FullAdm`, clause (12)).
-/

namespace MatedCRT

namespace Lemma68C12

open MeasureTheory Set Metric Filter
open scoped ENNReal
open Lemma68Geometry Lemma68GeometryId Lemma68Admissible Lemma68Relation Lemma68Successive
open Lemma68Concrete Lemma68Radius Lemma68Scales

/-- The square root of the dyadic scale is at most `r/1000` (the cutoff of write-up D1, as in `cfgCount_lower`). -/
lemma sqrt_delta_le {p r ζ : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (hpζ : p = 2 * ζ + 2)
    (hrζ : r ^ ζ ≤ 1 / 1000) : Real.sqrt (Delta p r) ≤ r / 1000 := by
  have hpow : r ^ p = (r ^ (1 + ζ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    congr 1
    rw [hpζ]
    push_cast
    ring
  have hsζ : Real.sqrt (Delta p r) ≤ r ^ (1 + ζ) := by
    have h1 : Delta p r ≤ r ^ p := Delta_le_rpow hp hr0 hr1
    calc Real.sqrt (Delta p r) ≤ Real.sqrt ((r ^ (1 + ζ)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [← hpow]
          exact h1
      _ = r ^ (1 + ζ) := Real.sqrt_sq (Real.rpow_nonneg hr0.le _)
  have h3 : r ^ (1 + ζ) = r * r ^ ζ := by rw [Real.rpow_add hr0, Real.rpow_one]
  have h2 : r * r ^ ζ ≤ r * (1 / 1000) := mul_le_mul_of_nonneg_left hrζ hr0.le
  linarith

/-- The exit schedule with a constant window is the successive exit schedule of `S6j`. -/
lemma nextExitSchedule_const_eq (W : ℤ → Set ℤ) : ∀ j : ℕ,
    S6j.nextExitSchedule (fun _ => W) j = exitSchedule W j
  | 0 => rfl
  | j + 1 => by
    rw [S6j.nextExitSchedule, exitSchedule, nextExitSchedule_const_eq W j]

/-- **Write-up C12 for the concrete test schedule (Lemma 6.8, bridge note Step D).** Almost surely, `T_N < τ_U` for the
killed set `U = killed ε η Θ F0 r`, the schedule `cfgExit` and the count `N = cfgCount p r`. Its hypotheses are the
inputs of `cfgSchedule_valid` and the cell-size bound at scale `Δ(p,r)/100`. -/
theorem concreteC12_killed {ε ρ d r p ζ : ℝ} {η : ℝ → ℂ} (good : ℂ → ℕ → Prop) {m : ℤ → ℤ → ℕ} {a : ℤ}
    {Θ F0 : Finset ℤ} (hε : 0 < ε) (hη : Continuous η)
    (hproper : Filter.Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ))
    (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (hpζ : p = 2 * ζ + 2) (hrζ : r ^ ζ ≤ 1 / 1000)
    (hrρ : r ≤ ρ / 100)
    (hlf : IsLocallyFiniteMult m) (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0)
    (hadj : ∀ u v : ℤ, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty)
    (hK : (fillCells ε η (↑Θ : Set ℤ)).Nonempty)
    (hKb : fillCells ε η (↑Θ : Set ℤ) ⊆ ball (0 : ℂ) (ρ / 2))
    (hd : d ≤ Delta p r / 100)
    (hsize : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty → Metric.diam (cell ε η k) ≤ d)
    (hF : cellVertices ε η (thickening r (fillCells ε η (↑Θ : Set ℤ))) ⊆ (↑F0 : Set ℤ))
    (hdd : dd ε η Θ a ≤ r / 2 ∧ r / 2 ≤ ddMax ε η Θ a) :
    Lemma68Concrete.ConcreteC12 m a ε η p r good (killed ε η Θ F0 r) := by
  classical
  have hΔ : 0 < Delta p r := delta_pos p r
  have hΔ1 : Delta p r ≤ 1 := (Delta_le_rpow hp hr0 hr1).trans (Real.rpow_le_one hr0.le hr1.le hp.le)
  have hs0 : 0 < Real.sqrt (Delta p r) := Real.sqrt_pos.2 hΔ
  have hs : Real.sqrt (Delta p r) ≤ r / 1000 := sqrt_delta_le hp hr0 hr1 hpζ hrζ
  have hss : Real.sqrt (Delta p r) * Real.sqrt (Delta p r) = Delta p r := Real.mul_self_sqrt hΔ.le
  have hs1 : Real.sqrt (Delta p r) ≤ 1 := by simpa using Real.sqrt_le_sqrt hΔ1
  have hδs : Delta p r ≤ Real.sqrt (Delta p r) := by nlinarith [Real.sqrt_nonneg (Delta p r)]
  have hsN : (cfgCount p r : ℝ) * (100 * Real.sqrt (Delta p r)) ≤ r := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ r / (100 * Real.sqrt (Delta p r)) by
      exact div_nonneg hr0.le (mul_nonneg (by norm_num) hs0.le))
    unfold cfgCount
    exact (le_div_iff₀ (mul_pos (by norm_num) hs0)).1 h
  have hR : ∀ y : ℤ, Delta p r ≤ cfgStateRadius ε η p r good y ∧
      cfgStateRadius ε η p r good y ≤ Real.sqrt (Delta p r) := fun y =>
    selectable_bounds hΔ hΔ1 (firstGood_cand_mem hΔ (good (cfgCentre ε η p r y)))
  have hz : ∀ y : ℤ, dist (cfgCentre ε η p r y) (vertexPoint ε η y) ≤ Delta p r / 100 := fun y =>
    Uniform68Round.dist_gridRound_le (div_pos hΔ (by norm_num)) (vertexPoint ε η y)
  have hfinAE : ∀ j : ℕ, ∀ᵐ x ∂srwLaw m a, cfgExit ε η p r good j x < ⊤ := by
    intro j
    have h := S6j.ae_nextExitSchedule_lt_top_of_finite m a (fun _ => cfgWindow ε η p r good) hlf hcons
      (fun _ y => cfgWindow_finite hη hproper hε p r good y) j
    filter_upwards [h] with x hx
    rw [cfgExit_eq_exitSchedule, ← nextExitSchedule_const_eq]
    exact hx
  have hall : ∀ᵐ x ∂srwLaw m a, ∀ j : ℕ, cfgExit ε η p r good j x < ⊤ := ae_all_iff.2 hfinAE
  unfold Lemma68Concrete.ConcreteC12
  filter_upwards [FrontierSeparation.ae_srwStep_legal m a, srwLaw_ae_start m a, hall] with x hleg hx0 hfinx
  have hfin : ∀ j ≤ cfgCount p r, exitSchedule (cfgWindow ε η p r good) j x ≠ ⊤ := fun j _ => by
    have h := hfinx j
    rw [cfgExit_eq_exitSchedule] at h
    exact h.ne
  rw [cfgExit_eq_exitSchedule]
  exact pathwise_containment hη hε (cfgCentre ε η p r) (cfgStateRadius ε η p r good)
    (cfgWindow ε η p r good) (fun _ => rfl) hz hR hΔ hδs hs hsN hd hr0 hrρ hK hKb hsize hF hdd x hx0 hleg hadj hfin

end Lemma68C12

end MatedCRT
