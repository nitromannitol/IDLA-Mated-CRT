import MatedCRT.Defs.Map
import MatedCRT.Defs.RandomWalk
import MatedCRT.FirstPass.S6r.LocalBudget

/-!
# First-pass 6.8, redesign: the successive two-sided shell test, steps 6-9 (fp-S6r-shell-test, z9)

Written argument: `notes/fp-gaps/CHATGPT-idla-6-8-shells.md`: step 6 `boundary_start_time` (l.397-441), step 7
`test_finishes_before_next_shell` (l.442-546), step 8 `local_test_stays_in_U` (l.547-600), step 9
`S5_geometry_at_shell_test` (l.601-707). Setup (l.15-57): `K = closure Θ`, `U = V(K+B_r) \ Θ`, `f = dist(·,K)`,
`s = d^a`, `h_ε` the cell-size bound (7.0).

Repository conventions (`MatedCRT/Defs/Map.lean`, `MatedCRT/Defs/RandomWalk.lean`): `cell ε η k = η '' Icc (ε(k-1)) (εk)`;
`vertexPoint ε η k = η (εk)`; `cellVertices ε η D = V(D) = {k | (cell k ∩ D).Nonempty}`;
`interiorCellVertices ε η D = V(D) \ V(∂D)` is the walk-side `I(D)`: the cells meeting `D` but not `∂D`, which for
connected cells are the cells wholly inside `D`. A walk is a path `x : ℕ → ℤ`; `vExitTime A x` is `τ_A`.

Named inputs (each enters as a hypothesis of the lemma that uses it):
* `hηc : Continuous η` (cells are connected), `hadj` (consecutive walk vertices have intersecting cells);
* the shell data of steps 1-5 (`Σ'`, the entry times `C_j ≤ C_{j+1}` of (7.22), `dist z Σ ≤ R/50` of (7.25));
* the cell-size input `CellDiamLe` (the paper's `h_ε`, (7.0));
* the S5 one-test bound (7.50) is NOT formalized here (probability space, filtration, strong Markov at `T_j`);
  see the report. The geometric hypotheses of S5 at `x'_j` are discharged below.
-/

namespace MatedCRT
namespace Lemma68Window

open Set Metric
open MeasureTheory

/-! ## Cells: connectedness, the vertex point, the cell-size input -/

/-- The cell-size input `h_ε` (7.0): every cell meeting `E` has diameter at most `h`. -/
def CellDiamLe (ε : ℝ) (η : ℝ → ℂ) (h : ℝ) (E : Set ℂ) : Prop :=
  ∀ k : ℤ, (cell ε η k ∩ E).Nonempty → ∀ p ∈ cell ε η k, ∀ q ∈ cell ε η k, dist p q ≤ h

lemma isPreconnected_cell (ε : ℝ) (η : ℝ → ℂ) (hηc : Continuous η) (k : ℤ) :
    IsPreconnected (cell ε η k) :=
  isPreconnected_Icc.image η hηc.continuousOn

/-- The vertex point `η(εk)` is a point of its own cell (the right endpoint of `Icc (ε(k-1)) (εk)`). -/
lemma vertexPoint_mem_cell {ε : ℝ} (hε : 0 ≤ ε) (η : ℝ → ℂ) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * (k : ℝ), ⟨mul_le_mul_of_nonneg_left (by linarith : (k : ℝ) - 1 ≤ (k : ℝ)) hε, le_rfl⟩, rfl⟩

/-- A preconnected set that meets `D` and misses `∂D` lies in `D` (the connectedness step behind `(7.28)`:
a connected cell meeting the ball `B` and not its boundary sphere is wholly inside `B`). -/
lemma subset_of_isPreconnected_of_disjoint_frontier {D S : Set ℂ} (hS : IsPreconnected S)
    (hfr : Disjoint S (frontier D)) (hSD : (S ∩ D).Nonempty) : S ⊆ D := by
  have hcov : S ⊆ interior D ∪ (closure D)ᶜ := by
    intro p hp
    by_cases hc : p ∈ closure D
    · refine Or.inl ?_
      by_contra hi
      exact (Set.disjoint_left.1 hfr hp) (show p ∈ closure D \ interior D from ⟨hc, hi⟩)
    · exact Or.inr hc
  have hdisj : Disjoint (interior D) (closure D)ᶜ :=
    Set.disjoint_left.2 fun p hp hp' => hp' (subset_closure (interior_subset hp))
  obtain ⟨p, hpS, hpD⟩ := hSD
  have hpint : p ∈ interior D := by
    by_contra hi
    exact (Set.disjoint_left.1 hfr hpS) (show p ∈ closure D \ interior D from ⟨subset_closure hpD, hi⟩)
  exact (hS.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj hcov
    ⟨p, hpS, hpint⟩).trans interior_subset

/-- Membership in the walk-side interior `I(D) = V(D) \ V(∂D)`, unfolded. -/
lemma mem_interiorCellVertices_iff {ε : ℝ} {η : ℝ → ℂ} {D : Set ℂ} {k : ℤ} :
    k ∈ interiorCellVertices ε η D ↔ (cell ε η k ∩ D).Nonempty ∧ ¬ (cell ε η k ∩ frontier D).Nonempty :=
  Iff.rfl

/-! ## Step 6: `boundary_start_time` (l.397-441) -/

/-- Step 6, vertex form of `(7.28)`. Let `C < T` and let `T` be the first time after `C` at which the walk leaves
`I(D)`. Then `X_T ∈ V(∂D)`: the previous cell lies in `D` (connected, meets `D`, misses `∂D`), and the exit cell is
adjacent to it, so it meets `D` but not `I(D)`, hence meets `∂D`. Uses: `hηc`, `hadj`. -/
theorem boundary_start_vertex {ε : ℝ} {η : ℝ → ℂ} (hηc : Continuous η) (x : ℕ → ℤ)
    (hadj : ∀ n, (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty) {D : Set ℂ} {C T : ℕ} (hCT : C < T)
    (hmin : ∀ n, C ≤ n → n < T → x n ∈ interiorCellVertices ε η D) (hT : x T ∉ interiorCellVertices ε η D) :
    x T ∈ cellVertices ε η (frontier D) := by
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 1 := ⟨T - 1, by omega⟩
  obtain ⟨hmD, hmfr⟩ := mem_interiorCellVertices_iff.1 (hmin m (by omega) (by omega))
  have hfr : Disjoint (cell ε η (x m)) (frontier D) :=
    Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hmfr)
  have hsub := subset_of_isPreconnected_of_disjoint_frontier (isPreconnected_cell ε η hηc (x m)) hfr hmD
  obtain ⟨p, hp1, hp2⟩ := hadj m
  by_contra hout
  exact hT (mem_interiorCellVertices_iff.2 ⟨⟨p, hp2, hsub hp1⟩, hout⟩)

/-- Step 6, radial form `(7.29)`: a vertex whose cell meets `∂B_ρ(z)` has its vertex point within `h` of the sphere
of radius `ρ`. Uses the cell-size input on `E ⊇ ∂B_ρ(z)`. -/
theorem exit_vertex_radius {ε : ℝ} {η : ℝ → ℂ} (hε : 0 ≤ ε) {h : ℝ} {E : Set ℂ} (hmesh : CellDiamLe ε η h E)
    (z : ℂ) {ρ : ℝ} (hρ : ρ ≠ 0) (hE : frontier (ball z ρ) ⊆ E) {b : ℤ}
    (hb : b ∈ cellVertices ε η (frontier (ball z ρ))) :
    |dist (vertexPoint ε η b) z - ρ| ≤ h := by
  obtain ⟨p, hp1, hp2⟩ := hb
  have hpE : (cell ε η b ∩ E).Nonempty := ⟨p, hp1, hE hp2⟩
  have hdiam : dist (vertexPoint ε η b) p ≤ h :=
    hmesh b hpE (vertexPoint ε η b) (vertexPoint_mem_cell hε η b) p hp1
  have hpsph : dist p z = ρ := by
    rw [frontier_ball z hρ] at hp2
    exact mem_sphere.1 hp2
  have htri := abs_dist_sub_le (vertexPoint ε η b) p z
  rw [hpsph] at htri
  exact htri.trans hdiam

/-! ## Step 7: `test_finishes_before_next_shell` (l.442-546) -/

/-- `|f - c|` moves by at most `dist` when `f = dist(·, K)` is 1-Lipschitz. -/
lemma abs_level_sub_le (K : Set ℂ) (r : ℝ) (u v : ℂ) :
    |(|infDist u K - r / 2| - |infDist v K - r / 2|)| ≤ dist u v := by
  have a1 : infDist u K ≤ infDist v K + dist u v := infDist_le_infDist_add_dist
  have a2 : infDist v K ≤ infDist u K + dist v u := infDist_le_infDist_add_dist
  rw [dist_comm v u] at a2
  have h1 : |infDist u K - infDist v K| ≤ dist u v := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  calc |(|infDist u K - r / 2| - |infDist v K - r / 2|)|
      ≤ |(infDist u K - r / 2) - (infDist v K - r / 2)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |infDist u K - infDist v K| := by congr 1; ring
    _ ≤ dist u v := h1

/-- `(7.30)`: if `Σ(λ) = {|f - r/2| = λ}` passes within `R/50` of `z`, then on `B_{2R}(z)` the level `|f - r/2|`
is within `3s` of `λ`. Uses `R ≤ s`. -/
theorem level_near_centre {K : Set ℂ} {r lam s R : ℝ} {z y : ℂ} (hy : |infDist y K - r / 2| = lam)
    (hzy : dist z y ≤ R / 50) (hRs : R ≤ s) (hs : 0 < s) {u : ℂ} (hu : dist u z < 2 * R) :
    |(|infDist u K - r / 2| - lam)| < 3 * s := by
  subst hy
  have h2 : dist u y ≤ dist u z + dist z y := dist_triangle u z y
  have h3 : dist u y < 3 * s := by linarith
  exact lt_of_le_of_lt (abs_level_sub_le K r u y) h3

/-- `(7.31)`: a point `p` of a cell of diameter `≤ h` that contains a point `q ∈ B_{2R}(z)` has `|f - r/2|` within
`3s + h` of `λ`. -/
theorem cell_level_within {K : Set ℂ} {r lam s R h : ℝ} {z y : ℂ} (hy : |infDist y K - r / 2| = lam)
    (hzy : dist z y ≤ R / 50) (hRs : R ≤ s) (hs : 0 < s) {q p : ℂ} (hq : dist q z < 2 * R)
    (hpq : dist p q ≤ h) : |(|infDist p K - r / 2| - lam)| < 3 * s + h := by
  have A := level_near_centre hy hzy hRs hs hq
  have B := abs_level_sub_le K r p q
  have C := abs_sub_le (|infDist p K - r / 2|) (|infDist q K - r / 2|) lam
  linarith [B, C, A, hpq]

/-- `(7.32)` with `(7.31)`: no cell meeting `B_{2R}(z)` meets the next shell `{|f - r/2| = λ + 20s}`, since
`h ≤ s` and `20s > 3s + h`. -/
theorem cell_misses_next_shell {K : Set ℂ} {r lam s R h : ℝ} {z y : ℂ} (hy : |infDist y K - r / 2| = lam)
    (hzy : dist z y ≤ R / 50) (hRs : R ≤ s) (hs : 0 < s) (hhs : h ≤ s) {q p : ℂ}
    (hq : dist q z < 2 * R) (hpq : dist p q ≤ h) : |infDist p K - r / 2| ≠ lam + 20 * s := by
  intro hp
  have A := cell_level_within (K := K) (r := r) hy hzy hRs hs hq hpq
  rw [hp] at A
  have e : lam + 20 * s - lam = 20 * s := by ring
  rw [e, abs_of_pos (by linarith : (0:ℝ) < 20 * s)] at A
  linarith

/-- Step 7, `(7.38)`: the local test on `D' = B_{R/4}(η(X_T))` ends before the next shell, `T_j < L_j < C_{j+1}`.
Here `x T ∈ I(D')` (so `L ≠ T`), `D' ⊆ B_{2R}(z)`, and `hsep` is `(7.32)`. If `C_{j+1} < L_j` then `X_{C_{j+1}}`
has its cell in `D'`; if `C_{j+1} = L_j` then the previous cell lies in `D'` and is adjacent to `X_{L_j}`. Uses: `hηc`,
`hadj`. -/
theorem local_test_before_next_shell {ε : ℝ} {η : ℝ → ℂ} (hηc : Continuous η) (x : ℕ → ℤ)
    (hadj : ∀ n, (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    {z : ℂ} {R : ℝ} {Sn : Set ℂ}
    (hsep : ∀ k : ℤ, (cell ε η k ∩ ball z (2 * R)).Nonempty → ¬ (cell ε η k ∩ Sn).Nonempty)
    {D' : Set ℂ} (hD' : D' ⊆ ball z (2 * R)) {T C1 L : ℕ} (hTC1 : T < C1)
    (hC1 : (cell ε η (x C1) ∩ Sn).Nonempty)
    (hTL : T ≤ L) (hT : x T ∈ interiorCellVertices ε η D')
    (hLmin : ∀ n, T ≤ n → n < L → x n ∈ interiorCellVertices ε η D')
    (hL : x L ∉ interiorCellVertices ε η D') : L < C1 := by
  have hTL' : T < L := lt_of_le_of_ne hTL (fun h => hL (h ▸ hT))
  by_contra hge
  rcases (not_lt.1 hge).lt_or_eq with hlt | heq
  · obtain ⟨⟨p, hp1, hp2⟩, -⟩ := mem_interiorCellVertices_iff.1 (hLmin C1 (le_of_lt hTC1) hlt)
    exact hsep (x C1) ⟨p, hp1, hD' hp2⟩ hC1
  · obtain ⟨hne, hnfr⟩ := mem_interiorCellVertices_iff.1 (hLmin (L - 1) (by omega) (by omega))
    have hfr : Disjoint (cell ε η (x (L - 1))) (frontier D') :=
      Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hnfr)
    have hsub := subset_of_isPreconnected_of_disjoint_frontier
      (isPreconnected_cell ε η hηc (x (L - 1))) hfr hne
    obtain ⟨p, hp1, hp2⟩ := hadj (L - 1)
    have hL1 : L - 1 + 1 = L := by omega
    rw [hL1] at hp2
    rw [heq] at hC1
    exact hsep (x L) ⟨p, hp2, hD' (hsub hp1)⟩ hC1

/-- Step 7, `(7.33)`: the bad path leaves `B_{4R/3}(z)` before the next shell is reached, `C_j < T_j < C_{j+1}`.
`hsep` is `(7.32)`: no cell meeting `B_{2R}(z)` meets `Σ_{j+1}`. Uses: `hηc`, `hadj`, the step-6 vertex lemma. -/
theorem exit_before_next_shell {ε : ℝ} {η : ℝ → ℂ} (hηc : Continuous η) (x : ℕ → ℤ)
    (hadj : ∀ n, (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    {z : ℂ} {R : ℝ} (hR : 0 < R) {Sn : Set ℂ}
    (hsep : ∀ k : ℤ, (cell ε η k ∩ ball z (2 * R)).Nonempty → ¬ (cell ε η k ∩ Sn).Nonempty)
    {Cj C1 T : ℕ} (hCC : Cj ≤ C1) (hC1 : (cell ε η (x C1) ∩ Sn).Nonempty) (hCjT : Cj ≤ T)
    (hCj : x Cj ∈ interiorCellVertices ε η (ball z (4 * R / 3)))
    (hTmin : ∀ n, Cj ≤ n → n < T → x n ∈ interiorCellVertices ε η (ball z (4 * R / 3)))
    (hT : x T ∉ interiorCellVertices ε η (ball z (4 * R / 3))) :
    Cj < T ∧ T < C1 := by
  have hlt : Cj < T := lt_of_le_of_ne hCjT (fun h => hT (h ▸ hCj))
  refine ⟨hlt, ?_⟩
  by_contra hle
  have hle' : C1 ≤ T := not_lt.1 hle
  have hbad : (cell ε η (x C1) ∩ ball z (2 * R)).Nonempty := by
    rcases hle'.lt_or_eq with hlt' | heq
    · obtain ⟨⟨p, hp1, hp2⟩, -⟩ := mem_interiorCellVertices_iff.1 (hTmin C1 hCC hlt')
      exact ⟨p, hp1, Metric.ball_subset_ball (by linarith) hp2⟩
    · have hfr := boundary_start_vertex hηc x hadj hlt hTmin hT
      rw [← heq] at hfr
      obtain ⟨p, hp1, hp2⟩ := hfr
      have hpz : dist p z = 4 * R / 3 := by
        rw [frontier_ball z (by linarith : (0:ℝ) < 4 * R / 3).ne'] at hp2
        exact mem_sphere.1 hp2
      exact ⟨p, hp1, mem_ball.2 (by rw [hpz]; linarith)⟩
  exact hsep (x C1) hbad hC1

/-- `(7.36)-(7.37)`: if the vertex point `b' = η(b)` lies within `R/4` of `B_{4R/3}`-sphere radius `h` and the cell
of `b` has diameter `≤ h < R/4`, then `b ∈ I(B_{R/4}(b'))` and `B_{R/4}(b') ⊆ B_{2R}(z)`. -/
theorem exit_cell_test_ball {ε : ℝ} {η : ℝ → ℂ} {b : ℤ} {h R : ℝ} {z : ℂ} (hε : 0 ≤ ε) (hR : 0 < R)
    (hdiam : ∀ p ∈ cell ε η b, dist p (vertexPoint ε η b) ≤ h) (hhR : h < R / 4)
    (hrad : |dist (vertexPoint ε η b) z - 4 * R / 3| ≤ h) :
    b ∈ interiorCellVertices ε η (ball (vertexPoint ε η b) (R / 4)) ∧
      ball (vertexPoint ε η b) (R / 4) ⊆ ball z (2 * R) := by
  constructor
  · refine mem_interiorCellVertices_iff.2 ⟨⟨vertexPoint ε η b, vertexPoint_mem_cell hε η b,
      mem_ball_self (by linarith)⟩, ?_⟩
    rintro ⟨p, hp1, hp2⟩
    have hpd : dist p (vertexPoint ε η b) = R / 4 := by
      rw [frontier_ball (vertexPoint ε η b) (by linarith : (0:ℝ) < R / 4).ne'] at hp2
      exact mem_sphere.1 hp2
    linarith [hdiam p hp1]
  · intro w hw
    have hwd := mem_ball.1 hw
    have hab := abs_le.1 hrad
    have t := dist_triangle w (vertexPoint ε η b) z
    rw [mem_ball]
    linarith [hab.1, hab.2]

/-! ## Step 8: `local_test_stays_in_U` (l.547-600) -/

/-- `λ_j = 20 j s ≤ r/20` for `j ≤ N` when `N·400s ≤ r` (the shell count of step 1). -/
theorem shell_level_le {r s : ℝ} {N j : ℕ} (hs : 0 ≤ s) (hN : (N : ℝ) * (400 * s) ≤ r) (hj : j ≤ N) :
    20 * (j : ℝ) * s ≤ r / 20 := by
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
  have := mul_le_mul_of_nonneg_right hjN hs
  linarith

/-- `(7.40)`: a level `x` with `|x - r/2| < λ + 4s`, `λ ≤ r/20`, `s ≤ r/4000` satisfies `0 < x < r`. -/
theorem level_window {r s lam x : ℝ} (hlam : lam ≤ r / 20) (hs4 : s ≤ r / 4000)
    (hx : |x - r / 2| < lam + 4 * s) : 0 < x ∧ x < r := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hx
  constructor <;> linarith

/-- `(7.41)`: a vertex whose cell lies in `(K + B_r) \ K` (with `K + B_r = {f < r}`, `f = dist(·, K)`) lies in
`U = V(K+B_r) \ Θ`, when the cells of `Θ` lie in `K`. -/
theorem vertex_mem_U {ε : ℝ} {η : ℝ → ℂ} {K : Set ℂ} {r : ℝ} {Θv : Set ℤ}
    (hΘK : ∀ a ∈ Θv, cell ε η a ⊆ K) {a : ℤ} (hne : (cell ε η a).Nonempty)
    (hpos : ∀ p ∈ cell ε η a, 0 < infDist p K) (hlt : ∀ p ∈ cell ε η a, infDist p K < r) :
    a ∈ cellVertices ε η {p | infDist p K < r} \ Θv := by
  obtain ⟨p0, hp0⟩ := hne
  refine ⟨⟨p0, hp0, hlt p0 hp0⟩, fun ha => ?_⟩
  have h0 : infDist p0 K = 0 := infDist_zero_of_mem (hΘK a ha hp0)
  linarith [hpos p0 hp0]

open Classical in
/-- `k < τ_A` implies `x k ∈ A`: the first exit time `τ_A = inf {n : x n ∉ A}`. -/
theorem mem_of_lt_vExitTime {A : Set ℤ} {x : ℕ → ℤ} {k : ℕ} (h : (k : ℕ∞) < vExitTime A x) : x k ∈ A := by
  unfold vExitTime at h
  split_ifs at h with hex
  · by_contra hk
    have hle : Nat.find hex ≤ k := Nat.find_min' hex hk
    exact absurd h (not_lt.2 (by exact_mod_cast hle))
  · by_contra hk
    exact hex ⟨k, hk⟩

/-! ## Step 9: radii, the enlarged ball, the S4 first moment (l.601-707) -/

/-- `(7.44)-(7.45)`: `r² ≤ d ≤ R ≤ s ≤ r/4000`, so `r² ≤ R < r`. -/
theorem shell_radius_bounds {r d R s : ℝ} (hd : r ^ 2 ≤ d) (hdR : d ≤ R) (hRs : R ≤ s) (hs4 : s ≤ r / 4000)
    (hr : 0 < r) : r ^ 2 ≤ R ∧ R ≤ s ∧ R < r :=
  ⟨le_trans hd hdR, hRs, by linarith⟩

/-- `(7.49)`: with `|dist x' z - 4R/3| ≤ h` and `h + e ≤ R/12`, the enlarged ball `B_{R/4+e}(x')` lies in the good
annulus `{R < |· - z| < 2R}`. -/
theorem enlarged_ball_in_annulus {x' z : ℂ} {R h e : ℝ} (hR : 0 < R) (hrad : |dist x' z - 4 * R / 3| ≤ h)
    (hhe : h + e ≤ R / 12) :
    ball x' (R / 4 + e) ⊆ {p | R < dist p z ∧ dist p z < 2 * R} := by
  intro w hw
  have hwd := mem_ball.1 hw
  have hab := abs_le.1 hrad
  have t1 := dist_triangle x' w z
  have t2 := dist_triangle w x' z
  rw [dist_comm x' w] at t1
  show R < dist w z ∧ dist w z < 2 * R
  constructor <;> linarith [hab.1, hab.2]

/-- The one-test lower bound `q(r) = q₀ / (1 + log(1/r))²` of (7.51). -/
noncomputable def shellTestQ (q0 r : ℝ) : ℝ := q0 / (1 + Real.log (1 / r)) ^ 2

/-- `(7.46)-(7.48)`: from the S4 sparsity `ε·|A ∩ V(B_{c₀R})| ≤ s₁ r^{2β}` and `r² ≤ R`, and the volume lower bound
`μ(B_{c₀R}) ≥ c_v c₀^β R^β` with `4 s₁ ≤ c_v c₀^β`, the first-moment bound `ε·|A ∩ V| ≤ μ/4` holds. -/
theorem first_moment_of_sparsity {cnt m ε s1 cv c0 β R r : ℝ} (hβ : 0 ≤ β) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hs1 : 0 ≤ s1) (hr2 : r ^ 2 ≤ R) (hcnt : ε * cnt ≤ s1 * r ^ (2 * β))
    (hvol : cv * c0 ^ β * R ^ β ≤ m) (hcs : 4 * s1 ≤ cv * c0 ^ β) : ε * cnt ≤ m / 4 := by
  have hpow : r ^ (2 * β) ≤ R ^ β := by
    rw [Real.rpow_mul hr, Real.rpow_two]
    exact Real.rpow_le_rpow (sq_nonneg r) hr2 hβ
  have hRb : 0 ≤ R ^ β := Real.rpow_nonneg hR β
  have h1 : s1 * r ^ (2 * β) ≤ s1 * R ^ β := mul_le_mul_of_nonneg_left hpow hs1
  have h2 : 4 * s1 * R ^ β ≤ cv * c0 ^ β * R ^ β := mul_le_mul_of_nonneg_right hcs hRb
  linarith

/-! ## Step 9, S5 at the shell boundary: the geometric hypotheses of the one-test bound -/

/-- The numerical window of a shell test: the radii `r² ≤ d ≤ R ≤ s ≤ r/4000` (7.42-7.45), the cell-size
numerics `h < R/4` (from (7.0), `h ≤ d/100`), and the enlargement `0 ≤ e`, `h + e ≤ R/12` of (7.49). -/
def S5Window (r d R s h e : ℝ) : Prop :=
  r ^ 2 ≤ d ∧ d ≤ R ∧ R ≤ s ∧ s ≤ r / 4000 ∧ 0 < r ∧ 0 < R ∧ 0 ≤ e ∧ h + e ≤ R / 12 ∧ h < R / 4

/-- Step 9 (`S5_geometry_at_shell_test`, l.601-707), pathwise. At the exit time `T_j` of the walk from `I(B_{4R/3}(z))`
(step 6), with the exit vertex `b = X_{T_j}` and its vertex point `x' = η(b)`:
* `|x' - z| ` is within `h` of `4R/3` (7.29);
* the test ball `B_{R/4}(x')` lies in `I(·)` and in `B_{2R}(z)` (7.36-7.37);
* the enlarged ball `B_{R/4+e}(x')` lies in the good annulus `{R < |· - z| < 2R}` (7.49);
* `r² ≤ R < r` (7.44-7.45);
* the S4 first-moment bound `|A ∩ V(B_{c₀R}(x'))| ≤ μ(B_{c₀R}(x'))/(4ε)`, i.e. `ε·|A ∩ V| ≤ μ/4` (7.46-7.48), from
  the committed `localCount_of_ball` (`LocalBudget.lean`), with the radius-`r` sparsity `hglob` (Lemma 6.8's `A`-hypothesis),
  the finiteness `hfin` of the cell-vertex sets and the volume lower bound `hvol` as named inputs. -/
theorem S5_geometry_at_shell_test {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (hηc : Continuous η) (x : ℕ → ℤ)
    (hadj : ∀ n, (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    {z : ℂ} {r d R s h e : ℝ} (hW : S5Window r d R s h e)
    {E : Set ℂ} (hmesh : CellDiamLe ε η h E) (hE : frontier (ball z (4 * R / 3)) ⊆ E)
    {C T : ℕ} (hCT : C < T)
    (hmin : ∀ n, C ≤ n → n < T → x n ∈ interiorCellVertices ε η (ball z (4 * R / 3)))
    (hT : x T ∉ interiorCellVertices ε η (ball z (4 * R / 3)))
    {μ : Measure ℂ} {A : Set ℤ} {s1 β c0 : ℝ} (hs0 : 0 ≤ s1) (hβ0 : 0 ≤ β) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hs1small : 44 * s1 ≤ c0 ^ β) (hfin : ∀ w : ℂ, (cellVertices ε η (ball w r)).Finite)
    (hglob : ∀ w : ℂ, ((A ∩ cellVertices ε η (ball w r)).ncard : ℝ) < s1 * r ^ (2 * β) / ε)
    (hvol : (c0 * R) ^ β ≤ (μ (ball (vertexPoint ε η (x T)) (c0 * R))).toReal) :
    |dist (vertexPoint ε η (x T)) z - 4 * R / 3| ≤ h ∧
      ball (vertexPoint ε η (x T)) (R / 4 + e) ⊆ {p | R < dist p z ∧ dist p z < 2 * R} ∧
      (x T ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x T)) (R / 4)) ∧
        ball (vertexPoint ε η (x T)) (R / 4) ⊆ ball z (2 * R)) ∧
      ((A ∩ cellVertices ε η (ball (vertexPoint ε η (x T)) (c0 * R))).ncard : ℝ) ≤
        (μ (ball (vertexPoint ε η (x T)) (c0 * R))).toReal / (4 * ε) ∧ r ^ 2 ≤ R ∧ R < r := by
  obtain ⟨hd, hdR, hRs, hs4, hr, hR, he0, hhe, hhR⟩ := hW
  have hρ : (4 * R / 3 : ℝ) ≠ 0 := by
    have : (0 : ℝ) < 4 * R / 3 := by linarith
    exact this.ne'
  have hb := boundary_start_vertex hηc x hadj hCT hmin hT
  have hrad := exit_vertex_radius hε.le hmesh z hρ hE hb
  obtain ⟨p, hp1, hp2⟩ := hb
  have hpE : (cell ε η (x T) ∩ E).Nonempty := ⟨p, hp1, hE hp2⟩
  have hdiam : ∀ q ∈ cell ε η (x T), dist q (vertexPoint ε η (x T)) ≤ h := fun q hq => by
    rw [dist_comm]
    exact hmesh (x T) hpE (vertexPoint ε η (x T)) (vertexPoint_mem_cell hε.le η (x T)) q hq
  obtain ⟨hI, hball⟩ := exit_cell_test_ball hε.le hR hdiam hhR hrad
  have hsq := shell_radius_bounds hd hdR hRs hs4 hr
  have hcR : c0 * R ≤ r := le_trans (mul_le_of_le_one_left hR.le hc01) hsq.2.2.le
  exact ⟨hrad, enlarged_ball_in_annulus hR hrad hhe, ⟨hI, hball⟩,
    localCount_of_ball hε hs0 hβ0 hr hR hc0 hcR (le_trans hd hdR) hs1small hfin hglob hvol,
    hsq.1, hsq.2.2⟩

/-- Step 9, `(7.50)` in the form consumed by the strong-Markov step (`oneTest_step` of `Amplification.lean`).
`F` is the test-failure event `{X_n ∈ A for all T_j ≤ n < L_j}`, so `μ[1_F | 𝓖] ≤ 1 - q(r)` on `P` is the bound
`P(∃ n ∈ [T_j, L_j): X_n ∉ A | 𝓖) ≥ q(r)` (complement). The named hypothesis `hS5` is the S5 one-test estimate
(z5, not committed), valid on the set `G` of paths whose test geometry is `S5_geometry_at_shell_test`; the
inclusion `P ⊆ G` is supplied pathwise by that lemma. No probability is estimated here. -/
theorem S5_at_shell_boundary {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓖 : MeasurableSpace Ω} {F P G : Set Ω} {q : ℝ} (hPG : P ⊆ G)
    (hS5 : ∀ᵐ ω ∂μ, ω ∈ G → μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω ≤ 1 - q) :
    ∀ᵐ ω ∂μ, ω ∈ P → μ[F.indicator (fun _ => (1 : ℝ)) | 𝓖] ω ≤ 1 - q :=
  hS5.mono fun _ h hω => h (hPG hω)

#print axioms MatedCRT.Lemma68Window.S5_geometry_at_shell_test
#print axioms MatedCRT.Lemma68Window.S5_at_shell_boundary
#print axioms MatedCRT.Lemma68Window.boundary_start_vertex
#print axioms MatedCRT.Lemma68Window.exit_vertex_radius
#print axioms MatedCRT.Lemma68Window.exit_before_next_shell
#print axioms MatedCRT.Lemma68Window.local_test_before_next_shell
#print axioms MatedCRT.Lemma68Window.exit_cell_test_ball
#print axioms MatedCRT.Lemma68Window.cell_misses_next_shell
#print axioms MatedCRT.Lemma68Window.level_window
#print axioms MatedCRT.Lemma68Window.vertex_mem_U
#print axioms MatedCRT.Lemma68Window.mem_of_lt_vExitTime
#print axioms MatedCRT.Lemma68Window.enlarged_ball_in_annulus
#print axioms MatedCRT.Lemma68Window.first_moment_of_sparsity

end Lemma68Window
end MatedCRT
