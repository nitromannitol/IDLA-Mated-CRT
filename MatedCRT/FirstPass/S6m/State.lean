import Mathlib
import MatedCRT.FirstPass.S6m.Path
import MatedCRT.FirstPass.S6h.Schedule
import MatedCRT.FirstPass.S6j.PerState
import MatedCRT.FirstPass.S4S6c.FrontierSeparation
import MatedCRT.FirstPass.S4S6c.ExitNull68
import MatedCRT.Proofs.Infra.LocallyFinite
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Lemma 6.8, write-up C13-C14: the per-state fields of the concrete test schedule (fp-S6m, owner z10)

The per-state geometric fields `hS2`, `hdy`, `hdiam` of `Lemma68Concrete.StateTestInputs` (S6h/Schedule.lean), for the
concrete centres `cfgCentre` and radii `cfgStateRadius`.

* Deterministic core `hit_lt_exit_of_legal` (write-up C13, C14): a legal walk from the state `y` leaves the inner
  window `I(B_{4R/3}(z))` at a vertex `X_{p+1}` whose cell meets the middle sphere `∂B_{4R/3}(z)`, so the hitting time
  of `middleVertices` is at most `p + 1`, while every vertex up to `p + 1` lies in the window `I(B_{2R}(z))`; the cell
  of `X_{p+1}` has diameter at most `d`, so it lies in `B_{4R/3 + d} ⊂ B_{2R}`.
* Almost sure form `ae_hit_lt_exit`: the first exit from the finite set `I(B_{4R/3}(z))` is almost surely finite
  (`ExitNull68.exit_null_of_finite`), and the walk is almost surely legal (`FrontierSeparation.ae_srwStep_legal`).
* Concrete fields `stateHS2`, `stateHdy`, `stateHdiam`: the types of the fields of `StateTestInputs`, at
  `cfgCentre`, `cfgStateRadius`.

Named inputs (hypotheses): the cell-size bound `hsize` (cells meeting `B_ρ` have diameter at most `d`), the scale
bounds `d ≤ Δ(p,r)/100` and `d ≤ c₀ Δ(p,r)` (with `0 ≤ c₀`), the adjacency `hadj` of cells for the multiplicity `m`,
and the region `hreg` on the predicate `Good` of good states: `|z_y| + 2 R_y < ρ` for the centre `z_y = cfgCentre y`
and radius `R_y = cfgStateRadius y` (write-up C8, C9: the states `X_{T_j}` of the induction satisfy it).
-/

namespace MatedCRT
namespace Lemma68C12
open MeasureTheory Set Metric Filter
open scoped ENNReal
open Lemma68Geometry Lemma68GeometryId Lemma68Admissible Lemma68Relation Lemma68Successive
open Lemma68Concrete Lemma68Radius Lemma68Scales
open S6j

/-! ### Cells, balls and interior vertices (deterministic) -/

/-- A cell `H^ε_k = η([ε(k-1), εk])` is bounded: it is the image of a compact interval under the continuous `η`. -/
lemma cell_isBounded {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    Bornology.IsBounded (cell ε η k) :=
  (isCompact_Icc.image hη).isBounded

/-- Two points of a cell of diameter at most `d` are at distance at most `d` (write-up C11, `diam H^ε_k ≤ d`). -/
lemma dist_le_of_mem_cell {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {k : ℤ} {d : ℝ}
    (hd : diam (cell ε η k) ≤ d) {u w : ℂ} (hu : u ∈ cell ε η k) (hw : w ∈ cell ε η k) :
    dist u w ≤ d :=
  (dist_le_diam_of_mem (cell_isBounded hη k) hu hw).trans hd

/-- A cell of diameter at most `d` through a point `w` with `dist w z < t` lies in `B(z, t + d)`. -/
lemma cell_subset_ball_of_diam {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {k : ℤ} {d : ℝ}
    (hd : diam (cell ε η k) ≤ d) {w : ℂ} (hw : w ∈ cell ε η k) {z : ℂ} {t : ℝ} (hwz : dist w z < t) :
    cell ε η k ⊆ ball z (t + d) := by
  intro u hu
  rw [mem_ball]
  have h1 := dist_le_of_mem_cell hη hd hu hw
  have h2 := dist_triangle u w z
  linarith

/-- A cell contained in an open ball `B(z, t)` gives an interior vertex: `k ∈ I(B(z, t))` (write-up C3). -/
lemma mem_interiorCellVertices_of_subset {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) {z : ℂ} {t : ℝ} {k : ℤ}
    (hsub : cell ε η k ⊆ ball z t) : k ∈ interiorCellVertices ε η (ball z t) := by
  have hne : k ∈ cellVertices ε η (ball z t) :=
    ⟨vertexPoint ε η k, vertexPoint_mem_cell hε η k, hsub (vertexPoint_mem_cell hε η k)⟩
  have hnf : k ∉ cellVertices ε η (frontier (ball z t)) := by
    rintro ⟨w, hw, hwf⟩
    rw [isOpen_ball.frontier_eq] at hwf
    exact hwf.2 (hsub hw)
  exact Set.mem_sdiff_of_mem hne hnf

/-! ### Exit and hitting times (deterministic) -/

/-- If `x k ∉ A` then the first exit time from `A` is at most `k`. -/
lemma vExitTime_le_of_not_mem {A : Set ℤ} {x : ℕ → ℤ} {k : ℕ} (h : x k ∉ A) :
    vExitTime A x ≤ k := by
  classical
  have hex : ∃ n, x n ∉ A := ⟨k, h⟩
  unfold vExitTime
  split_ifs
  exact_mod_cast Nat.find_min' hex h

/-- The hitting time of `B` is at most `k` when `x k ∈ B`. -/
lemma vHitTime_le_of_mem {B : Set ℤ} {x : ℕ → ℤ} {k : ℕ} (h : x k ∈ B) : vHitTime B x ≤ k :=
  vExitTime_le_of_not_mem (fun hc => hc h)

/-- If `x k ∈ A` for all `k ≤ n` then the first exit time from `A` is strictly larger than `n`. -/
lemma lt_vExitTime_of_forall_mem {A : Set ℤ} {x : ℕ → ℤ} {n : ℕ} (h : ∀ k ≤ n, x k ∈ A) :
    (n : ℕ∞) < vExitTime A x := by
  by_contra hc
  rw [not_lt] at hc
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top n) hc)
  have hkn : k ≤ n := by
    rw [← hk] at hc
    exact_mod_cast hc
  exact (vExitTime_eq_coe_spec hk.symm).1 (h k hkn)

/-! ### The deterministic core of hS2 (write-up C13, C14) -/

/-- **Deterministic core of hS2.** Let `z` be a centre and `R` a radius with `dist z 0 + 2R < ρ`. Let `x` be a legal
walk from `y` (each step stays or moves to an adjacent vertex) whose first exit from `I(B_{4R/3}(z))` is finite. If the
cell of `y` is within `R/100` of `z` (`dist(η(y), z) ≤ R/100`) and cells meeting `B_ρ` have diameter at most `d ≤ R/100`,
then the walk hits the middle vertices `V(∂B_{4R/3}(z))` strictly before it leaves `I(B_{2R}(z))`. -/
theorem hit_lt_exit_of_legal {ε ρ d R : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {z : ℂ} {y : ℤ} {x : ℕ → ℤ}
    (hε : 0 < ε) (hη : Continuous η) (hR : 0 < R) (hd : d ≤ R / 100) (hzρ : dist z 0 + 2 * R < ρ)
    (hzy : dist (vertexPoint ε η y) z ≤ R / 100)
    (hsize : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty → diam (cell ε η k) ≤ d)
    (hadj : ∀ u v : ℤ, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty)
    (hx0 : x 0 = y) (hleg : ∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0)
    (hfin : vExitTime (interiorCellVertices ε η (ball z (4 * R / 3))) x ≠ ⊤) :
    vHitTime (middleVertices ε η z R) x < vExitTime (interiorCellVertices ε η (ball z (2 * R))) x := by
  -- the start cell lies in the inner ball `B(z, 4R/3)`
  have hvp0 : dist (vertexPoint ε η y) 0 < ρ := by
    have := dist_triangle (vertexPoint ε η y) z 0
    linarith
  have hdy0 : diam (cell ε η y) ≤ d :=
    hsize y ⟨vertexPoint ε η y, vertexPoint_mem_cell hε η y, mem_ball.2 hvp0⟩
  have hstart : y ∈ interiorCellVertices ε η (ball z (4 * R / 3)) :=
    mem_interiorCellVertices_of_subset hε
      ((cell_subset_ball_of_diam hη hdy0 (vertexPoint_mem_cell hε η y) (t := R / 50) (by linarith)).trans
        (ball_subset_ball (by linarith)))
  -- the first exit `n0` from `I(B_{4R/3}(z))`
  obtain ⟨n0, hn0⟩ := ENat.ne_top_iff_exists.1 hfin
  obtain ⟨hout, hin⟩ := vExitTime_eq_coe_spec hn0.symm
  have hn0pos : n0 ≠ 0 := by
    rintro rfl
    exact hout (by rw [hx0]; exact hstart)
  obtain ⟨p, rfl⟩ : ∃ p, n0 = p + 1 := ⟨n0 - 1, by omega⟩
  have hxp : x p ∈ interiorCellVertices ε η (ball z (4 * R / 3)) := hin p (by omega)
  -- the exit step is a genuine step between adjacent cells
  have hstep : m (x p) (x (p + 1)) ≠ 0 := by
    rcases hleg p with h | h
    · exact (hout (by rw [h]; exact hxp)).elim
    · exact h
  obtain ⟨w, hwp, hwq⟩ := hadj _ _ hstep
  have hwball : w ∈ ball z (4 * R / 3) := cell_subset_of_mem_interior hη z (4 * R / 3) hxp hwp
  -- the exit vertex lies on the middle sphere: its cell meets `∂B_{4R/3}(z)`
  have hM : x (p + 1) ∈ middleVertices ε η z R := by
    by_contra hnM
    apply hout
    refine Set.mem_sdiff_of_mem ⟨w, hwq, hwball⟩ ?_
    rintro ⟨u, hu, huf⟩
    have hr : (4 * R / 3 : ℝ) ≠ 0 := ne_of_gt (by linarith)
    rw [frontier_ball _ hr] at huf
    exact hnM ⟨u, hu, huf⟩
  -- the exit cell has diameter at most `d`, so it lies in `B(z, 4R/3 + d) ⊂ B(z, 2R)`
  have hw0 : w ∈ ball (0 : ℂ) ρ :=
    mem_ball.2 (by
      have h1 := dist_triangle w z 0
      have h2 := mem_ball.1 hwball
      linarith)
  have hcellq : diam (cell ε η (x (p + 1))) ≤ d := hsize _ ⟨w, hwq, hw0⟩
  have hsubq : cell ε η (x (p + 1)) ⊆ ball z (2 * R) :=
    (cell_subset_ball_of_diam hη hcellq hwq (mem_ball.1 hwball)).trans (ball_subset_ball (by linarith))
  have hWq : x (p + 1) ∈ interiorCellVertices ε η (ball z (2 * R)) :=
    mem_interiorCellVertices_of_subset hε hsubq
  -- every vertex up to the exit lies in the window `I(B_{2R}(z))`
  have hWle : ∀ k ≤ p + 1, x k ∈ interiorCellVertices ε η (ball z (2 * R)) := by
    intro k hk
    rcases Nat.lt_or_ge k (p + 1) with hlt | hge
    · exact mem_interiorCellVertices_of_subset hε
        ((cell_subset_of_mem_interior hη z (4 * R / 3) (hin k hlt)).trans (ball_subset_ball (by linarith)))
    · have hk' : k = p + 1 := by omega
      rw [hk']
      exact hWq
  exact lt_of_le_of_lt (vHitTime_le_of_mem hM) (lt_vExitTime_of_forall_mem hWle)

/-! ### The almost sure form (write-up C13, C14 with the walk law `srwLaw m y`) -/

/-- **Almost sure hS2 for a fixed centre and radius.** Under the walk law `srwLaw m y`, almost surely the hitting time of
`middleVertices ε η z R` precedes the exit time of `I(B_{2R}(z))`. Uses the finiteness of the window
`I(B_{4R/3}(z))` (properness of `η`), the exit finiteness `ExitNull68.exit_null_of_finite`, and the legality
`FrontierSeparation.ae_srwStep_legal`. -/
theorem ae_hit_lt_exit {ε ρ d R : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} {z : ℂ} (hε : 0 < ε) (hη : Continuous η)
    (hproper : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hadj : ∀ u v : ℤ, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty)
    (hR : 0 < R) (hd : d ≤ R / 100) (hzρ : dist z 0 + 2 * R < ρ)
    (hsize : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty → diam (cell ε η k) ≤ d) (y : ℤ)
    (hzy : dist (vertexPoint ε η y) z ≤ R / 100) :
    ∀ᵐ x ∂srwLaw m y,
      vHitTime (middleVertices ε η z R) x < vExitTime (interiorCellVertices ε η (ball z (2 * R))) x := by
  have hfinI : (interiorCellVertices ε η (ball z (4 * R / 3))).Finite := by
    refine (cellVertices_finite_of_isCompact hη hproper hε (isCompact_closedBall z (4 * R / 3))).subset ?_
    intro k hk
    obtain ⟨u, hu⟩ := hk.1
    exact ⟨u, hu.1, ball_subset_closedBall hu.2⟩
  have hae : ∀ᵐ x ∂srwLaw m y, vExitTime (interiorCellVertices ε η (ball z (4 * R / 3))) x ≠ ⊤ := by
    rw [ae_iff]
    simpa using ExitNull68.exit_null_of_finite hlf hcons hfinI y
  filter_upwards [hae, srwLaw_ae_start m y, FrontierSeparation.ae_srwStep_legal m y] with x hfin hx0 hleg
  exact hit_lt_exit_of_legal hε hη hR hd hzρ hzy hsize hadj hx0 hleg hfin

/-! ### The fields of `StateTestInputs` at the concrete centres and radii -/

/-- The concrete radius bounds `Δ(p,r) ≤ R_y ≤ √Δ(p,r)` at every state (write-up C1, A5 selection). -/
lemma cfgStateRadius_bounds (ε : ℝ) (η : ℝ → ℂ) {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (good : ℂ → ℕ → Prop) (y : ℤ) :
    Delta p r ≤ cfgStateRadius ε η p r good y ∧ cfgStateRadius ε η p r good y ≤ Real.sqrt (Delta p r) := by
  have hΔ : 0 < Delta p r := delta_pos p r
  have hΔ1 : Delta p r ≤ 1 := (Delta_le_rpow hp hr0 hr1).trans (Real.rpow_le_one hr0.le hr1.le hp.le)
  exact selectable_bounds hΔ hΔ1 (firstGood_cand_mem hΔ (good (cfgCentre ε η p r y)))

/-- **Field `hS2` of `StateTestInputs`** (write-up C13, C14; z12's S2), at the concrete centres `cfgCentre` and radii
`cfgStateRadius`. The region hypothesis `hreg` is on the good states. -/
theorem stateHS2 {ε ρ d p r : ℝ} {η : ℝ → ℂ} {m : ℤ → ℤ → ℕ} (good : ℂ → ℕ → Prop) {Good : ℤ → Prop}
    (hε : 0 < ε) (hη : Continuous η) (hproper : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) (hlf : IsLocallyFiniteMult m)
    (hcons : ∀ k : ℤ, m k (k + 1) ≠ 0) (hadj : ∀ u v : ℤ, m u v ≠ 0 → (cell ε η u ∩ cell ε η v).Nonempty)
    (hd : d ≤ Delta p r / 100)
    (hsize : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty → diam (cell ε η k) ≤ d)
    (hreg : ∀ y, Good y → dist (cfgCentre ε η p r y) 0 + 2 * cfgStateRadius ε η p r good y < ρ) :
    ∀ y, Good y → ∀ᵐ x ∂srwLaw m y,
      vHitTime (middleVertices ε η (cfgCentre ε η p r y) (cfgStateRadius ε η p r good y)) x <
        vExitTime (interiorCellVertices ε η
          (Metric.ball (cfgCentre ε η p r y) (2 * cfgStateRadius ε η p r good y))) x := by
  intro y hy
  obtain ⟨hR1, _⟩ := cfgStateRadius_bounds ε η hp hr0 hr1 good y
  have hΔ : 0 < Delta p r := delta_pos p r
  have hR : 0 < cfgStateRadius ε η p r good y := lt_of_lt_of_le hΔ hR1
  have hzy : dist (vertexPoint ε η y) (cfgCentre ε η p r y) ≤ cfgStateRadius ε η p r good y / 100 := by
    have h := Uniform68Round.dist_gridRound_le (div_pos hΔ (by norm_num : (0 : ℝ) < 100)) (vertexPoint ε η y)
    rw [dist_comm]
    calc dist (cfgCentre ε η p r y) (vertexPoint ε η y) ≤ Delta p r / 100 := h
      _ ≤ cfgStateRadius ε η p r good y / 100 := by linarith
  have hd' : d ≤ cfgStateRadius ε η p r good y / 100 := by linarith
  exact ae_hit_lt_exit hε hη hproper hlf hcons hadj hR hd' (hreg y hy) hsize y hzy

/-- **Field `hdy` of `StateTestInputs`** (write-up B11, C3), at the concrete centres and radii: every middle vertex has
cells of diameter at most `R/100`. -/
theorem stateHdy {ε ρ d p r : ℝ} {η : ℝ → ℂ} (good : ℂ → ℕ → Prop) {Good : ℤ → Prop}
    (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (hd : d ≤ Delta p r / 100)
    (hsize : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty → diam (cell ε η k) ≤ d)
    (hreg : ∀ y, Good y → dist (cfgCentre ε η p r y) 0 + 2 * cfgStateRadius ε η p r good y < ρ) :
    ∀ y, Good y → ∀ v ∈ middleVertices ε η (cfgCentre ε η p r y) (cfgStateRadius ε η p r good y),
      Metric.diam (cell ε η v) ≤ cfgStateRadius ε η p r good y / 100 := by
  intro y hy v hv
  obtain ⟨hR1, _⟩ := cfgStateRadius_bounds ε η hp hr0 hr1 good y
  have hΔ : 0 < Delta p r := delta_pos p r
  have hR : 0 < cfgStateRadius ε η p r good y := lt_of_lt_of_le hΔ hR1
  obtain ⟨w, hwc, hws⟩ := hv
  have hwz : dist w (cfgCentre ε η p r y) = 4 * cfgStateRadius ε η p r good y / 3 := mem_sphere.1 hws
  have hw0 : w ∈ ball (0 : ℂ) ρ :=
    mem_ball.2 (by
      have h1 := dist_triangle w (cfgCentre ε η p r y) 0
      have h2 := hreg y hy
      linarith)
  have h3 := hsize v ⟨w, hwc, hw0⟩
  have hd' : d ≤ cfgStateRadius ε η p r good y / 100 := by linarith
  linarith

/-- **Field `hdiam` of `StateTestInputs`** (write-up B11, C3), at the concrete centres and radii: every cell meeting
`B(vertexPoint v, R/4)` for a middle vertex `v` has diameter at most `c₀ R`. Needs `d ≤ c₀ Δ(p,r)` (with `0 ≤ c₀`). -/
theorem stateHdiam {ε ρ d p r c0 : ℝ} {η : ℝ → ℂ} (good : ℂ → ℕ → Prop) {Good : ℤ → Prop}
    (hε : 0 < ε) (hη : Continuous η) (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1)
    (hc0 : 0 ≤ c0) (hdc : d ≤ c0 * Delta p r) (hd : d ≤ Delta p r / 100)
    (hsize : ∀ k : ℤ, (cell ε η k ∩ ball (0 : ℂ) ρ).Nonempty → diam (cell ε η k) ≤ d)
    (hreg : ∀ y, Good y → dist (cfgCentre ε η p r y) 0 + 2 * cfgStateRadius ε η p r good y < ρ) :
    ∀ y, Good y → ∀ v ∈ middleVertices ε η (cfgCentre ε η p r y) (cfgStateRadius ε η p r good y),
      ∀ k : ℤ, (cell ε η k ∩ Metric.ball (vertexPoint ε η v) (cfgStateRadius ε η p r good y / 4)).Nonempty →
        Metric.diam (cell ε η k) ≤ c0 * cfgStateRadius ε η p r good y := by
  intro y hy v hv k hk
  obtain ⟨hR1, _⟩ := cfgStateRadius_bounds ε η hp hr0 hr1 good y
  have hΔ : 0 < Delta p r := delta_pos p r
  have hR : 0 < cfgStateRadius ε η p r good y := lt_of_lt_of_le hΔ hR1
  have hd' : d ≤ cfgStateRadius ε η p r good y / 100 := by linarith
  obtain ⟨w, hwc, hws⟩ := hv
  have hwz : dist w (cfgCentre ε η p r y) = 4 * cfgStateRadius ε η p r good y / 3 := mem_sphere.1 hws
  have hw0 : w ∈ ball (0 : ℂ) ρ :=
    mem_ball.2 (by
      have h1 := dist_triangle w (cfgCentre ε η p r y) 0
      have h2 := hreg y hy
      linarith)
  have hdv : diam (cell ε η v) ≤ d := hsize v ⟨w, hwc, hw0⟩
  have hvw : dist (vertexPoint ε η v) w ≤ d :=
    dist_le_of_mem_cell hη hdv (vertexPoint_mem_cell hε η v) hwc
  obtain ⟨u, huk, hub⟩ := hk
  have hub' := mem_ball.1 hub
  have huz : dist u (cfgCentre ε η p r y) < 2 * cfgStateRadius ε η p r good y := by
    have h1 := dist_triangle u (vertexPoint ε η v) (cfgCentre ε η p r y)
    have h2 := dist_triangle (vertexPoint ε η v) w (cfgCentre ε η p r y)
    linarith
  have hu0 : u ∈ ball (0 : ℂ) ρ :=
    mem_ball.2 (by
      have h1 := dist_triangle u (cfgCentre ε η p r y) 0
      have h2 := hreg y hy
      linarith)
  have hdk : diam (cell ε η k) ≤ d := hsize k ⟨u, huk, hu0⟩
  calc diam (cell ε η k) ≤ d := hdk
    _ ≤ c0 * Delta p r := hdc
    _ ≤ c0 * cfgStateRadius ε η p r good y := mul_le_mul_of_nonneg_left hR1 hc0

end Lemma68C12
end MatedCRT
