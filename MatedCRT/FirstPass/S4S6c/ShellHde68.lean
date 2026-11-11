import MatedCRT.FirstPass.S4S6c.ShellOrderFullAdm
import MatedCRT.FirstPass.S6r.ShortWindow
import MatedCRT.FirstPass.S6r.ShellPathAe
import MatedCRT.FirstPass.S6r.ShellTest

/-!
# The shell hypothesis `hde` of `shellOrder_fullAdm_ae`, almost surely

For a configuration `i` satisfying the full guard `FullAdm` at radius `r`, the shell exits `T_k` (`shellExit`) are finite
and the shell centres `z_k` (`shellCentre`) are eligible, for `k ≤ n = shellCount r s - 1`, almost surely. The eligibility
predicate used is the set `Z_d = shortEligible ρ d s` (PRO step 3), and the caller's `Elig` must contain it (binder `hElig`).

The argument is pathwise (route steps 1-5 and 7):
* Let `U = killed ε η Θ F0 r` and `τ = vExitTime U x`. Since `τ < ⊤`, the cells `cell (x 0), …, cell (x τ)` form a chain of
  connected sets (`ae_cell_adjacent`, `cell_isPreconnected`), so the union is connected
  (`IsPreconnected.iUnion_of_chain`). The level `f = |dist(·, K) - r/2|` is continuous, equals `0` on the start cell
  (`hstart`, the frontier of `thickening (r/2) K`) and is `≥ r/2` on the exit cell (`level_ge_of_not_killed`). Hence the
  shell level `λ_k = 20 (k+1) s ∈ (0, r/20]` is attained on some cell `cell (x i)`, `i ≤ τ` (`exists_index_level`). So the
  first hit `C_{k+1} ≤ τ`.
* The centre `z_k = Q_{d/100}(η(X_{C_{k+1}}))` is within `2d/100` of the shell (cell diameter `≤ d/100` and rounding
  `≤ d/100`). Its norm lies in `[10 s, ρ - 3 s)`, so `z_k ∈ Z_d` (`centre_norm_bounds`). Its eligibility gives `R z_k ≤ s`.
* `interiorCellVertices (ball z (4 R z/3)) ⊆ U` (`cell_meets_ball_mem_killed`), so `x τ ∉ I(B(z, 4Rz/3))` and the exit
  `T_k ≤ τ < ⊤`.

Inputs that are not derived here: `hmesh` (the mesh bound `CellDiamLe`), `hstart` (the start cell meets the frontier of
the `r/2`-thickening), `hR` (the range of `Rf` on `Elig`), `hElig` (`Elig` contains `Z_d`; the definition choice of `Elig`),
and the test-end finiteness `htest` (the conjunct `testEnd ≠ ⊤`).
`hkill` is derived from `Lemma68ShellEnvAeInputs.hkill_of_valid`.

The almost-sure statement carries the guard `FullAdm` pointwise in `ω`: `FullAdm` supplies `ball 0 s₀ ⊆ fillCells Θ`,
`closure (fillCells Θ) ⊆ ball 0 (ρ/2)` and `F0 = cellVertices (ball 0 ρ)`, which the level and eligibility arguments use.
Without it the conclusion is not derivable.
-/

open MeasureTheory Set Filter
open MatedCRT.Lemma68Window MatedCRT.Lemma68Omega MatedCRT.Lemma68GeometryId MatedCRT.Lemma68Admissible
open MatedCRT.Lemma68ShellPath MatedCRT.Lemma68Geometry

namespace MatedCRT
namespace Lemma68ShellHde68

/-- **Discrete intermediate value along a path of cells (level crossing).** If consecutive cells of `x` meet, then a
continuous `f` takes every value `c` in `[f p, f q]` on some cell `cell (x i)` with `i ≤ τ`, for `p` in the start cell
and `q` in the cell `τ`. The union of the cells `x 0, …, x τ` is connected (`IsPreconnected.iUnion_of_chain`, with the
index clamped at `τ`), and its image under `f` is an interval. -/
theorem exists_index_level {η : ℝ → ℂ} (hη : Continuous η) {ε : ℝ} (hε : 0 < ε) {x : ℕ → ℤ} {τ : ℕ}
    (hadj : ∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty)
    {f : ℂ → ℝ} (hf : Continuous f) {p q : ℂ} (hp : p ∈ cell ε η (x 0)) (hq : q ∈ cell ε η (x τ))
    {c : ℝ} (hpc : f p ≤ c) (hcq : c ≤ f q) :
    ∃ i ≤ τ, ∃ y ∈ cell ε η (x i), f y = c := by
  set s : ℕ → Set ℂ := fun n => cell ε η (x (min n τ)) with hs_def
  have hconn : IsPreconnected (⋃ n, s n) := by
    refine IsPreconnected.iUnion_of_chain (fun n => isPreconnected_cell ε η hη _) (fun n => ?_)
    show (s n ∩ s (n + 1)).Nonempty
    rcases lt_or_ge n τ with h | h
    · have e1 : min n τ = n := min_eq_left h.le
      have e2 : min (n + 1) τ = n + 1 := min_eq_left (by omega)
      simp only [hs_def, e1, e2]
      exact hadj n
    · have e1 : min n τ = τ := min_eq_right h
      have e2 : min (n + 1) τ = τ := min_eq_right (by omega)
      simp only [hs_def, e1, e2, Set.inter_self]
      exact cell_nonempty (η := η) hε (x τ)
  have hp' : f p ∈ f '' ⋃ n, s n :=
    ⟨p, mem_iUnion.2 ⟨0, by simp only [hs_def, Nat.zero_min]; exact hp⟩, rfl⟩
  have hq' : f q ∈ f '' ⋃ n, s n :=
    ⟨q, mem_iUnion.2 ⟨τ, by simp only [hs_def, min_self]; exact hq⟩, rfl⟩
  obtain ⟨y, hy, hyc⟩ := (hconn.image f hf.continuousOn).Icc_subset hp' hq' ⟨hpc, hcq⟩
  obtain ⟨n, hn⟩ := mem_iUnion.1 hy
  exact ⟨min n τ, min_le_right n τ, y, hn, hyc⟩

/-- **The level of the start frontier.** A point of the frontier of `thickening δ K` (for nonempty `K`) lies at distance
exactly `δ` from `K`. -/
theorem infDist_eq_of_mem_frontier {K : Set ℂ} (hK : K.Nonempty) {δ : ℝ} {p : ℂ}
    (hp : p ∈ frontier (Metric.thickening δ K)) : Metric.infDist p K = δ := by
  rw [Metric.isOpen_thickening.frontier_eq] at hp
  obtain ⟨hcl, hnot⟩ := hp
  have h1 : δ ≤ Metric.infDist p K := by
    by_contra hlt
    rw [not_le] at hlt
    apply hnot
    obtain ⟨y, hy, hdy⟩ := (Metric.infDist_lt_iff hK).1 hlt
    exact Metric.mem_thickening_iff.2 ⟨y, hy, hdy⟩
  have h2 : Metric.infDist p K ≤ δ := by
    have hsub : Metric.thickening δ K ⊆ {q : ℂ | Metric.infDist q K ≤ δ} := by
      intro q hq
      obtain ⟨y, hy, hdy⟩ := Metric.mem_thickening_iff.1 hq
      exact (Metric.infDist_le_dist_of_mem hy).trans hdy.le
    have hclosed : IsClosed {q : ℂ | Metric.infDist q K ≤ δ} :=
      isClosed_le (Metric.continuous_infDist_pt K) continuous_const
    exact (closure_minimal hsub hclosed) hcl
  exact le_antisymm h2 h1

/-- **The exit cell lies at level at least `r/2`.** If the cell of `v` is not in the killed set `killed ε η Θ F0 r`,
then some point `q` of the cell satisfies `r/2 ≤ |dist(q, K) - r/2|` (`K = fillCells Θ`). Three cases: `v ∈ Θ` (the cell
lies in `K`, level `r/2`); `v ∉ F0` (the cell lies outside `ball 0 ρ`, so `dist(·,K) ≥ ρ/2`); `dd v ≥ r` (the cell misses
`thickening r K`, so `dist(·,K) ≥ r`). -/
theorem level_ge_of_not_killed {η : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε) (hη : Continuous η) {ρ r : ℝ} (hr : 0 < r)
    (hrρ : r ≤ ρ / 4) {Θ F0 : Finset ℤ} (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (hKne : (fillCells ε η ↑Θ).Nonempty) (hcl : fillCells ε η ↑Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2)) {v : ℤ}
    (hv : v ∉ killed ε η Θ F0 r) :
    ∃ q ∈ cell ε η v, r / 2 ≤ |Metric.infDist q (fillCells ε η ↑Θ) - r / 2| := by
  obtain ⟨q, hq⟩ := cell_nonempty (η := η) hε v
  refine ⟨q, hq, ?_⟩
  have hv' : ¬ (v ∈ F0 ∧ dd ε η Θ v < r ∧ v ∉ Θ) := hv
  by_cases hΘv : v ∈ Θ
  · have hqK : q ∈ fillCells ε η ↑Θ := cell_subset_fillCells (ε := ε) (η := η) hΘv hq
    rw [Metric.infDist_zero_of_mem hqK, zero_sub, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < r / 2)]
  · by_cases hdd : dd ε η Θ v < r
    · have hF0v : v ∉ F0 := fun h => hv' ⟨h, hdd, hΘv⟩
      have hq_out : ρ ≤ ‖q‖ := by
        by_contra hlt
        rw [not_le] at hlt
        apply hF0v
        rw [← Finset.mem_coe, hF0]
        exact ⟨q, hq, mem_ball_zero_iff.2 hlt⟩
      have hinf : ρ / 2 ≤ Metric.infDist q (fillCells ε η ↑Θ) := by
        rw [Metric.le_infDist hKne]
        intro y hy
        have hy' : ‖y‖ < ρ / 2 := mem_ball_zero_iff.1 (hcl hy)
        have h2 : ‖q‖ - ‖y‖ ≤ dist q y := by
          rw [dist_eq_norm]
          exact norm_sub_norm_le q y
        linarith
      exact le_trans (by linarith) (le_abs_self _)
    · have hq_far : r ≤ Metric.infDist q (fillCells ε η ↑Θ) := by
        by_contra hlt
        rw [not_le] at hlt
        obtain ⟨y, hy, hdy⟩ := (Metric.infDist_lt_iff hKne).1 hlt
        apply hdd
        have hmem : v ∈ cellVertices ε η (Metric.thickening r (fillCells ε η ↑Θ)) :=
          ⟨q, hq, Metric.mem_thickening_iff.2 ⟨y, hy, hdy⟩⟩
        rw [cellVertices_thickening_eq hη hε Θ r] at hmem
        exact ENNReal.toReal_lt_of_lt_ofReal hmem
      exact le_trans (by linarith) (le_abs_self _)

/-- **Norm bounds of a shell centre.** If `y0` lies on the two-sided shell of offset `lam ≤ r/20` and `dist z y0 ≤ 2d/100`,
then `10 s ≤ ‖z‖ < ρ - 3 s` (with `d ≤ s ≤ r/4000` and `r ≤ ρ/4`). The lower bound uses `0 ∈ K`, the upper bound
`K ⊆ ball 0 (ρ/2)`. -/
theorem centre_norm_bounds {K : Set ℂ} (h0 : (0 : ℂ) ∈ K) {ρ r d s lam : ℝ} {z y0 : ℂ}
    (hKb : K ⊆ Metric.ball (0 : ℂ) (ρ / 2)) (hlam : lam ≤ r / 20) (hy0 : y0 ∈ twoSidedShell K r lam)
    (hzy : dist z y0 ≤ 2 * (d / 100)) (_hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d) (hds : d ≤ s)
    (hs4 : s ≤ r / 4000) :
    10 * s ≤ ‖z‖ ∧ ‖z‖ < ρ - 3 * s := by
  obtain ⟨hlo, hhi⟩ := shell_band hlam hy0
  have hn0 : Metric.infDist y0 K ≤ ‖y0‖ := by
    have := Metric.infDist_le_dist_of_mem (x := y0) h0
    rwa [dist_zero_right] at this
  have hn1 : ‖y0‖ ≤ ρ / 2 + 11 / 20 * r := norm_le_of_infDist_le ⟨0, h0⟩ hKb hhi
  have hz1 : ‖z‖ ≤ dist z y0 + ‖y0‖ := by
    have := dist_triangle z y0 0
    rwa [dist_zero_right, dist_zero_right] at this
  have hz2 : ‖y0‖ ≤ dist z y0 + ‖z‖ := by
    have := dist_triangle y0 z 0
    rw [dist_zero_right, dist_zero_right, dist_comm y0 z] at this
    exact this
  constructor <;> linarith

/-- **Shell exits are killed-exit bounded.** If `v` has a cell meeting `ball z (4R'/3)`, where `z` is a shell centre
(`dist z y0 ≤ 2d/100` for a point `y0` of the shell of offset `lam`) and `R' ≤ s`, then `v` lies in the killed set
`killed ε η Θ F0 r`. Thus `interiorCellVertices (ball z (4R'/3)) ⊆ killed`. -/
theorem cell_meets_ball_mem_killed {η : ℝ → ℂ} {ε : ℝ} (hη : Continuous η) (hε : 0 < ε) {ρ r d s lam R' : ℝ}
    {Θ F0 : Finset ℤ} (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) {z y0 : ℂ} (hy0 : y0 ∈ twoSidedShell (fillCells ε η ↑Θ) r lam)
    (hlam : lam ≤ r / 20) (hzy : dist z y0 ≤ 2 * (d / 100)) (hzρ : ‖z‖ < ρ - 3 * s)
    (hR0 : 0 < R') (hRs : R' ≤ s) (hds : d ≤ s) (hs4 : s ≤ r / 4000) (_hd : 0 < d) (_hr : 0 < r)
    (_hrρ : r ≤ ρ / 4) {v : ℤ} (hv : (cell ε η v ∩ Metric.ball z (4 * R' / 3)).Nonempty) :
    v ∈ killed ε η Θ F0 r := by
  obtain ⟨y, hyc, hyB⟩ := hv
  have hdy : dist y z < 4 * R' / 3 := Metric.mem_ball.1 hyB
  have hdy0 : dist y y0 ≤ 2 * (d / 100) + 4 * s / 3 := by
    have := dist_triangle y z y0
    linarith
  obtain ⟨hlo, hhi⟩ := shell_band hlam hy0
  have hKne : (fillCells ε η ↑Θ).Nonempty := ⟨0, h0⟩
  have hinf_lo : 9 / 20 * r - 2 * (d / 100) - 4 * s / 3 ≤ Metric.infDist y (fillCells ε η ↑Θ) := by
    have := Metric.infDist_le_infDist_add_dist (x := y0) (y := y) (s := fillCells ε η ↑Θ)
    rw [dist_comm] at this
    linarith
  have hinf_hi : Metric.infDist y (fillCells ε η ↑Θ) ≤ 11 / 20 * r + 2 * (d / 100) + 4 * s / 3 := by
    have := Metric.infDist_le_infDist_add_dist (x := y) (y := y0) (s := fillCells ε η ↑Θ)
    linarith
  show v ∈ F0 ∧ dd ε η Θ v < r ∧ v ∉ Θ
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.mem_coe, hF0]
    refine ⟨y, hyc, mem_ball_zero_iff.2 ?_⟩
    have := dist_triangle y z 0
    rw [dist_zero_right, dist_zero_right] at this
    linarith
  · obtain ⟨w, hw, hdw⟩ := (Metric.infDist_lt_iff hKne).1 (show Metric.infDist y (fillCells ε η ↑Θ) < r by linarith)
    have hmem : v ∈ cellVertices ε η (Metric.thickening r (fillCells ε η ↑Θ)) :=
      ⟨y, hyc, Metric.mem_thickening_iff.2 ⟨w, hw, hdw⟩⟩
    rw [cellVertices_thickening_eq hη hε Θ r] at hmem
    exact ENNReal.toReal_lt_of_lt_ofReal hmem
  · intro hΘv
    have hy0' : Metric.infDist y (fillCells ε η ↑Θ) = 0 :=
      Metric.infDist_zero_of_mem ((cell_subset_fillCells (ε := ε) (η := η) hΘv) hyc)
    linarith

/-- **A grid point of `gℤ²`.** The nearest-grid rounding is `g (m + n i)` for integers `m, n`. -/
theorem gridRound_mem_grid {g : ℝ} (w : ℂ) :
    ∃ m n : ℤ, Lemma68Window.gridRound g w = ((g : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I) :=
  ⟨round (w.re / g), round (w.im / g), by
    apply Complex.ext <;> simp [Lemma68Window.gridRound]⟩

/-- **The shell hit, pathwise (deterministic).** For a path `x` whose consecutive cells meet, with the killed exit `τ = vExitTime
(killed Θ F0 r) x` finite and the start cell meeting the frontier of the `r/2`-thickening, every shell index `k ≤ n` has
`T_k = shellExit k x ≠ ⊤` and `z_k = shellCentre k x ∈ shortEligible ρ d s`. Here `s = d ^ a`. -/
theorem shell_fin_of_path {η : ℝ → ℂ} {ε : ℝ} (hη : Continuous η) (hε : 0 < ε)
    {Θ F0 : Finset ℤ} {ρ r d a : ℝ} {R : ℂ → ℝ} {n : ℕ} (hr : 0 < r) (hrρ : r ≤ ρ / 4) (hd : 0 < d)
    (hds : d ≤ d ^ a) (hs4 : d ^ a ≤ r / 4000) (hNs : 20 * ((n + 1 : ℕ) : ℝ) * d ^ a ≤ r / 20)
    (hmesh : CellDiamLe ε η (d / 100) Set.univ)
    (hF0 : (↑F0 : Set ℤ) = cellVertices ε η (Metric.ball (0 : ℂ) ρ))
    (h0 : (0 : ℂ) ∈ fillCells ε η ↑Θ) (hKb : fillCells ε η ↑Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2))
    (hRS : ∀ w ∈ shortEligible ρ d a, d ≤ R w ∧ R w ≤ d ^ a)
    {x : ℕ → ℤ} (hadj : ∀ j : ℕ, (cell ε η (x j) ∩ cell ε η (x (j + 1))).Nonempty)
    (hst : (cell ε η (x 0) ∩ frontier (Metric.thickening (r / 2) (fillCells ε η ↑Θ))).Nonempty)
    (hτ : vExitTime (killed ε η Θ F0 r) x ≠ ⊤) :
    ∀ k ≤ n, shellExit ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x ≠ ⊤ ∧
      shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x ∈ shortEligible ρ d a := by
  intro k hk
  have hKne : (fillCells ε η ↑Θ).Nonempty := ⟨0, h0⟩
  have hs : 0 < d ^ a := Real.rpow_pos_of_pos hd a
  have hlam0 : 0 < shellOffset (d ^ a) (k + 1) := by
    unfold shellOffset
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.2 (Nat.succ_pos k))) hs
  have hlam1 : shellOffset (d ^ a) (k + 1) ≤ r / 20 := by
    unfold shellOffset
    have hk' : ((k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hk
    have hm := mul_le_mul_of_nonneg_right hk' (show (0 : ℝ) ≤ 20 * d ^ a by positivity)
    linarith
  -- the start level 0 and the exit level at least r/2
  obtain ⟨p, hp, hpf⟩ := hst
  have hpinf : Metric.infDist p (fillCells ε η ↑Θ) = r / 2 := infDist_eq_of_mem_frontier hKne hpf
  have hτn : x (vExitTime (killed ε η Θ F0 r) x).toNat ∉ killed ε η Θ F0 r :=
    vExitTime_toNat_not_mem hτ
  obtain ⟨q, hq, hqf⟩ := level_ge_of_not_killed hε hη hr hrρ hF0 hKne hKb hτn
  have hf : Continuous (fun y : ℂ => |Metric.infDist y (fillCells ε η ↑Θ) - r / 2|) :=
    continuous_abs.comp ((Metric.continuous_infDist_pt _).sub continuous_const)
  obtain ⟨i, hi, y, hyc, hy⟩ := exists_index_level hη hε hadj hf hp hq
    (c := shellOffset (d ^ a) (k + 1))
    (by
      show |Metric.infDist p (fillCells ε η ↑Θ) - r / 2| ≤ shellOffset (d ^ a) (k + 1)
      rw [hpinf, sub_self, abs_zero]
      exact hlam0.le)
    (by
      show shellOffset (d ^ a) (k + 1) ≤ |Metric.infDist q (fillCells ε η ↑Θ) - r / 2|
      linarith)
  have hyshell : y ∈ twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1)) := hy
  -- the first hit is at most the killed exit time
  set τ : ℕ := (vExitTime (killed ε η Θ F0 r) x).toNat with hτ_def
  have hitle : shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x ≤ (τ : ℕ∞) := by
    unfold shellHit
    exact (firstTime_le_iff _ τ).2 ⟨i, hi, y, hyc, hyshell⟩
  have hCfin : shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top τ) hitle
  set C : ℕ := (shellHit ε η (fillCells ε η ↑Θ) r (d ^ a) k x).toNat with hC_def
  have hCspec : (cell ε η (x C) ∩ twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1))).Nonempty :=
    firstTime_toNat_spec (P := fun m => (cell ε η (x m) ∩
      twoSidedShell (fillCells ε η ↑Θ) r (shellOffset (d ^ a) (k + 1))).Nonempty) hCfin
  obtain ⟨y0, hy0c, hy0⟩ := hCspec
  -- the centre is within 2d/100 of the shell
  have hw : vertexPoint ε η (x C) ∈ cell ε η (x C) := vertexPoint_mem_cell_nonneg hε.le η (x C)
  have hwy : dist (vertexPoint ε η (x C)) y0 ≤ d / 100 :=
    cell_diam_of_univ hε hmesh (x C) _ hw _ hy0c
  have hz_def : shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x
      = Lemma68Window.gridRound (d / 100) (vertexPoint ε η (x C)) := rfl
  have hzy : dist (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) y0 ≤ 2 * (d / 100) := by
    rw [hz_def]
    have h1 := Lemma68Window.dist_gridRound_le (g := d / 100) (div_pos hd (by norm_num))
      (vertexPoint ε η (x C))
    have h2 := dist_triangle (Lemma68Window.gridRound (d / 100) (vertexPoint ε η (x C)))
      (vertexPoint ε η (x C)) y0
    linarith
  have hz_bd := centre_norm_bounds h0 hKb hlam1 hy0 hzy hr hrρ hd hds hs4
  -- the centre lies in the eligible set Z_d
  have hzS : shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x ∈ shortEligible ρ d a := by
    obtain ⟨m, nn, hmn⟩ := gridRound_mem_grid (g := d / 100) (vertexPoint ε η (x C))
    refine ⟨⟨mem_ball_zero_iff.2 hz_bd.2, fun h => ?_⟩, m, nn, ?_⟩
    · have := mem_ball_zero_iff.1 h
      linarith [hz_bd.1]
    · rw [hz_def]
      exact hmn
  obtain ⟨hRlo, hRhi⟩ := hRS _ hzS
  have hR0 : 0 < R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) := lt_of_lt_of_le hd hRlo
  -- the walk at the killed exit time is outside the exit ball
  have hxτB : x τ ∉ interiorCellVertices ε η
      (Metric.ball (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x)
        (4 * R (shellCentre ε η (fillCells ε η ↑Θ) r (d ^ a) d k x) / 3)) := by
    intro hmem
    exact hτn (cell_meets_ball_mem_killed hη hε hF0 h0 hy0 hlam1 hzy hz_bd.2 hR0 hRhi hds hs4 hd hr hrρ
      (mem_interiorCellVertices_iff.1 hmem).1)
  have hexit : shellExit ε η (fillCells ε η ↑Θ) r (d ^ a) d R k x ≤ (τ : ℕ∞) := by
    unfold shellExit
    exact (firstTime_le_iff _ τ).2 ⟨τ, le_rfl, hitle, hxτB⟩
  exact ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top τ) hexit, hzS⟩

/-- **The shell hypothesis `hde`, almost surely (guarded by `FullAdm`).** For the configuration `i` at radius `r`, almost
surely: if the full guard `FullAdm` holds, then for almost every walk from `i.a` on `S.mult ε ω`, every shell exit
`shellExit k` (`k ≤ shellCount - 1`) is finite and every shell centre `shellCentre k` is eligible. The inputs `hmesh`,
`hstart` are a.s. environment facts, `hR` is the range of `Rf` on `Elig`, and `hElig` says that `Elig` contains the
eligible set `shortEligible ρ (dyadicD r) (shortExp ζ)` (the definition choice of `Elig`). The killed exit `hkill` is
`hkill_of_valid`. The testEnd conjunct is `shellHde68_full`. -/
theorem shellHde_ae68 {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68) {Rf : ℂ → ℝ} {Elig : ℂ → Prop}
    (hR : ∀ w, Elig w → dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    (hElig : ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) → Elig w)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P,
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) := by
  -- deterministic parameter facts (as in `shellOrder_fullAdm_ae`)
  have hr1 : r ≤ 1 := hrz.trans (countThreshold_le_one hζ)
  have hd : 0 < dyadicD r := dyadicD_pos r
  have hd1 : dyadicD r ≤ 1 := dyadicD_le_one r
  have hd2 : dyadicD r < 2 * r ^ 2 := dyadicD_lt_two_mul_sq hr hr1
  have ha1 : shortExp ζ ≤ 1 := by unfold shortExp; linarith
  have hs4 : dyadicD r ^ shortExp ζ ≤ r / 4000 := shell_size_le hζ hr hrz hd hd2
  have hds : dyadicD r ≤ dyadicD r ^ shortExp ζ := by
    have h1 : dyadicD r ^ (1 : ℝ) ≤ dyadicD r ^ shortExp ζ :=
      Real.rpow_le_rpow_of_exponent_ge hd hd1 ha1
    rw [Real.rpow_one] at h1
    exact h1
  have h400 : 400 * dyadicD r ^ shortExp ζ ≤ r := by
    have hs : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd _
    linarith
  have hc1 : 1 ≤ shellCount r (dyadicD r ^ shortExp ζ) := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ (by linarith)]
    linarith
  have hfl : (shellCount r (dyadicD r ^ shortExp ζ) : ℝ) * (400 * dyadicD r ^ shortExp ζ) ≤ r := by
    have h := Nat.floor_le (show 0 ≤ r / (400 * dyadicD r ^ shortExp ζ) by
      have hs : 0 < dyadicD r ^ shortExp ζ := Real.rpow_pos_of_pos hd _
      positivity)
    exact (le_div_iff₀ (by linarith)).1 h
  have hNs : 20 * ((shellCount r (dyadicD r ^ shortExp ζ) - 1 + 1 : ℕ) : ℝ) * dyadicD r ^ shortExp ζ
      ≤ r / 20 := by
    rw [Nat.sub_add_cancel hc1]
    nlinarith [hfl]
  -- almost sure environment facts
  filter_upwards [TraceInputs68.ae_continuous_eta hS, Lemma68ShellEnvAe.map_cells_meet_ae hγ0 hγ2 S hS,
    Lemma68ShellEnvAeInputs.hkill_of_valid hγ0 hγ2 S hS hε (Θ := i.Θ) (F0 := i.F0) (r := r) (a := i.a),
    hmesh, hstart] with ω hη hmap _hkill hm hst
  intro hadm
  unfold Lemma68Config.FullAdm Lemma68Config.ConfigOK at hadm
  obtain ⟨⟨hF0eq, hcl, hball⟩, -⟩ := hadm
  have h0K : (0 : ℂ) ∈ fillCells ε (S.η ω) ↑i.Θ := hball (Metric.mem_ball_self hs₀)
  have hKb : fillCells ε (S.η ω) ↑i.Θ ⊆ Metric.ball (0 : ℂ) (ρ / 2) := fun y hy => hcl (subset_closure hy)
  have hRS : ∀ w ∈ shortEligible ρ (dyadicD r) (shortExp ζ),
      dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ := fun w hw => hR w (hElig w hw)
  filter_upwards [srwLaw_ae_start (S.mult ε ω) i.a,
    Lemma68ShellPathAe.ae_cell_adjacent (S.mult ε ω) i.a hε (hmap ε hε), _hkill] with x hx0 hadj hτ
  have hpath := shell_fin_of_path (ε := ε) (R := Rf) (n := shellCount r (dyadicD r ^ shortExp ζ) - 1)
    hη hε hr hrρ hd hds hs4 hNs hm hF0eq h0K hKb hRS hadj (by rw [hx0]; exact hst) hτ
  exact ⟨fun k hk => (hpath k hk).1, fun k hk => hElig _ (hpath k hk).2⟩

/-- **The full shell hypothesis `hde`, almost surely, with the testEnd conjunct as a named input.** `htest` is the
finite-domain exit statement for the test ends (`testEnd ≠ ⊤`),
guarded by `FullAdm` as well. The conclusion is the conjunction of `shellHde_ae68` with `htest`. -/
theorem shellHde68_full {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (hS : S.IsValid 𝒮 γ)
    {ε ρ s₀ ζ r : ℝ} (hε : 0 < ε) (hs₀ : 0 < s₀) (hζ : 0 < ζ) (hζ1 : ζ < 1 / 2) (hr : 0 < r)
    (hrz : r ≤ countThreshold ζ) (hrρ : r ≤ ρ / 4) (i : Lemma68Config.Config68) {Rf : ℂ → ℝ} {Elig : ℂ → Prop}
    (hR : ∀ w, Elig w → dyadicD r ≤ Rf w ∧ Rf w ≤ dyadicD r ^ shortExp ζ)
    (hElig : ∀ w, w ∈ shortEligible ρ (dyadicD r) (shortExp ζ) → Elig w)
    (hmesh : ∀ᵐ ω ∂S.P, CellDiamLe ε (S.η ω) (dyadicD r / 100) Set.univ)
    (hstart : ∀ᵐ ω ∂S.P,
      (cell ε (S.η ω) i.a ∩ frontier (Metric.thickening (r / 2) (fillCells ε (S.η ω) ↑i.Θ))).Nonempty)
    (htest : ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        ∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) :
    ∀ᵐ ω ∂S.P, Lemma68Config.FullAdm S ρ s₀ γ ε ω r i →
      ∀ᵐ x ∂(srwLaw (S.mult ε ω) i.a),
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          shellExit ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤ ∧
          testEnd ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) Rf k x ≠ ⊤) ∧
        (∀ k ≤ shellCount r (dyadicD r ^ shortExp ζ) - 1,
          Elig (shellCentre ε (S.η ω) (fillCells ε (S.η ω) ↑i.Θ) r (dyadicD r ^ shortExp ζ) (dyadicD r) k x)) := by
  filter_upwards [shellHde_ae68 hγ0 hγ2 S hS hε hs₀ hζ hζ1 hr hrz hrρ i hR hElig hmesh hstart, htest]
    with ω h1 h2 hadm
  filter_upwards [h1 hadm, h2 hadm] with x ha hb
  exact ⟨fun k hk => ⟨ha.1 k hk, hb k hk⟩, ha.2⟩

end Lemma68ShellHde68
end MatedCRT

#print axioms MatedCRT.Lemma68ShellHde68.shellHde_ae68
#print axioms MatedCRT.Lemma68ShellHde68.shellHde68_full
