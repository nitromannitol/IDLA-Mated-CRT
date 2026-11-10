import MatedCRT.FirstPass.S6r.ShellTest
import MatedCRT.FirstPass.S6r.Shells

/-!
# Lemma 6.8, S8' wiring: the shell hypotheses `hTT`, `hLT`, `hcross`, `hend` (pathwise)

Source: `notes/fp-gaps/CHATGPT-idla-6-8-shells.md`, steps 4-9 (displayed (7.20)-(7.41)).
Index convention of `Amplification.lean`: shells and tests `k = 0, ..., n`; the notes' shell `Σ_{k+1}`
has offset `shellOffset s (k+1) = 20 (k+1) s`, and `N = n + 1`.

For one walk `x : ℕ → ℤ` (one sample path; the probabilistic layer applies it pathwise):
* `hitTime ε η K r s x k` is the first hitting index `C_{k+1}` of `Σ_{k+1}` (z10, step 4, `firstShellHit`);
* `T k` is the first exit time of `I(B_{4R_k/3}(z_k))` after `hitTime k` (ShellTest, steps 6-7);
* `L k` is the first exit time of `I(B_{R_k/4}(η(X_{T_k})))` after `T k` (ShellTest, steps 7-8);
* `z_k = gridRound (d/100) (vertexPoint (x (hitTime k)))`, `R_k = R z_k` (z10, step 5, `shell_hit_choose_center`).

The first-exit properties of `T`, `L` are hypotheses of `shell_chain_pathwise` (they characterise the
stopping times; the probabilistic layer supplies them).
Conclusions: `T k < C_{k+1}`, `L k < C_{k+1}`, `C_{k+1} < T_{k+1}` for `k < n`, and `L n < τ`, `T n ≤ L n`
for the exit index `τ` of `U = V(K+B_r) \ Θ`. These are the pathwise content of `hTT`, `hLT`, `hcross`, `hend`.
-/

namespace MatedCRT
namespace Lemma68Window

open Set Metric

variable {ε : ℝ} {η : ℝ → ℂ} {K : Set ℂ} {r s h : ℝ}

/-- Notes (7.20): `C_{k+1} = inf {n ≥ 0 : H_{X_n} ∩ Σ_{k+1} ≠ ∅}`, shell `Σ_{k+1}` of offset `20 (k+1) s`. -/
noncomputable def hitTime (ε : ℝ) (η : ℝ → ℂ) (K : Set ℂ) (r s : ℝ) (x : ℕ → ℤ) (k : ℕ) : ℕ :=
  firstShellHit ε η x (twoSidedShell K r (shellOffset s (k + 1)))

lemma shellOffset_succ (s : ℝ) (j : ℕ) :
    shellOffset s (j + 1 + 1) = shellOffset s (j + 1) + 20 * s := by
  unfold shellOffset
  push_cast
  ring

/-- A cell whose vertex lies in `I(D)` lies in `D`: the cell is connected and misses `∂D` (notes (7.33)). -/
lemma cell_subset_of_mem_interior (hηc : Continuous η) (k : ℤ) {D : Set ℂ}
    (hk : k ∈ interiorCellVertices ε η D) : cell ε η k ⊆ D := by
  obtain ⟨hne, hnfr⟩ := mem_interiorCellVertices_iff.1 hk
  have hfr : Disjoint (cell ε η k) (frontier D) :=
    Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hnfr)
  exact subset_of_isPreconnected_of_disjoint_frontier (isPreconnected_cell ε η hηc k) hfr hne

/-- Notes (7.22)-(7.26): if every point of the cell of `k` is within `ρ` of `z`, then `k ∈ I(B_ρ(z))`. -/
lemma mem_interior_of_cell_lt (hε : 0 ≤ ε) {k : ℤ} {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hk : ∀ p ∈ cell ε η k, dist p z < ρ) : k ∈ interiorCellVertices ε η (ball z ρ) := by
  refine mem_interiorCellVertices_iff.2 ⟨⟨vertexPoint ε η k, vertexPoint_mem_cell_nonneg hε η k,
    mem_ball.2 (hk _ (vertexPoint_mem_cell_nonneg hε η k))⟩, ?_⟩
  rintro ⟨p, hp1, hp2⟩
  rw [frontier_ball z hρ.ne'] at hp2
  have hpz : dist p z = ρ := mem_sphere.1 hp2
  linarith [hk p hp1]

/-- Steps 6-8 at one shell (notes (7.28)-(7.38)): for the first exit `T` of `B_{4R/3}(z)` after `C`, the vertex
`x T` lies in `I(D)` for the local disk `D = B_{R/4}(η(X_T))` and `D ⊆ B_{2R}(z)`. Uses the cell-size input
on `B_{2R}(z)` (`CellDiamLe`), `h < R/4`. -/
lemma test_ball_of_exit (hηc : Continuous η) (hε : 0 ≤ ε) (x : ℕ → ℤ)
    (hadj : ∀ n, (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    {z : ℂ} {R : ℝ} (hR : 0 < R) (hhR : h < R / 4) (hmesh : CellDiamLe ε η h (ball z (2 * R)))
    {C T : ℕ} (hCT : C < T)
    (hmin : ∀ n, C ≤ n → n < T → x n ∈ interiorCellVertices ε η (ball z (4 * R / 3)))
    (hT : x T ∉ interiorCellVertices ε η (ball z (4 * R / 3))) :
    x T ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x T)) (R / 4)) ∧
      ball (vertexPoint ε η (x T)) (R / 4) ⊆ ball z (2 * R) := by
  have hR43 : (4 * R / 3 : ℝ) ≠ 0 := by positivity
  have hE : frontier (ball z (4 * R / 3)) ⊆ ball z (2 * R) := by
    intro p hp
    rw [frontier_ball z hR43] at hp
    have hpz : dist p z = 4 * R / 3 := mem_sphere.1 hp
    rw [mem_ball, hpz]
    linarith
  have hb : x T ∈ cellVertices ε η (frontier (ball z (4 * R / 3))) :=
    boundary_start_vertex hηc x hadj hCT hmin hT
  have hrad : |dist (vertexPoint ε η (x T)) z - 4 * R / 3| ≤ h :=
    exit_vertex_radius hε hmesh z hR43 hE hb
  have hneE : (cell ε η (x T) ∩ ball z (2 * R)).Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := hb
    exact ⟨p, hp1, hE hp2⟩
  have hdiam : ∀ p ∈ cell ε η (x T), dist p (vertexPoint ε η (x T)) ≤ h :=
    fun p hp => hmesh (x T) hneE p hp (vertexPoint ε η (x T)) (vertexPoint_mem_cell_nonneg hε η (x T))
  exact exit_cell_test_ball hε hR hdiam hhR hrad

/-- Steps 4-8 at one shell `k` with a next shell (notes (7.33), (7.38)): with `C = C_{k+1}`, `C1 = C_{k+2}`,
`T` the first exit of `B_{4R/3}(z)` after `C`, `L` the first exit of the local disk after `T`:
`C < T < C1` and `L < C1`. Uses the shell-spacing geometry `hsep` (7.32) from `cell_misses_next_shell`. -/
lemma shell_step_order (hηc : Continuous η) (hε : 0 ≤ ε) (x : ℕ → ℤ)
    (hadj : ∀ n, (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty)
    {z : ℂ} {R lam : ℝ} (hR : 0 < R) (hRs : R ≤ s) (hs : 0 < s) (hhs : h ≤ s) (hhR : h < R / 4)
    (hy : ∃ y ∈ twoSidedShell K r lam, dist z y ≤ R / 50)
    (hmesh : CellDiamLe ε η h (ball z (2 * R)))
    {C C1 T L : ℕ} (hCC : C ≤ C1)
    (hC1 : (cell ε η (x C1) ∩ twoSidedShell K r (lam + 20 * s)).Nonempty)
    (hCT : C ≤ T) (hCin : x C ∈ interiorCellVertices ε η (ball z (4 * R / 3)))
    (hmin : ∀ n, C ≤ n → n < T → x n ∈ interiorCellVertices ε η (ball z (4 * R / 3)))
    (hT : x T ∉ interiorCellVertices ε η (ball z (4 * R / 3)))
    (hTL : T ≤ L)
    (hLmin : ∀ n, T ≤ n → n < L →
      x n ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x T)) (R / 4)))
    (hL : x L ∉ interiorCellVertices ε η (ball (vertexPoint ε η (x T)) (R / 4))) :
    C < T ∧ T < L ∧ L < C1 := by
  obtain ⟨y, hyS, hzy⟩ := hy
  have hyS' : |infDist y K - r / 2| = lam := hyS
  have hsep : ∀ k : ℤ, (cell ε η k ∩ ball z (2 * R)).Nonempty →
      ¬ (cell ε η k ∩ twoSidedShell K r (lam + 20 * s)).Nonempty := by
    rintro k ⟨q, hqc, hqb⟩ ⟨p, hpc, hps⟩
    have hpq : dist p q ≤ h := hmesh k ⟨q, hqc, hqb⟩ p hpc q hqc
    have hps' : |infDist p K - r / 2| = lam + 20 * s := hps
    exact cell_misses_next_shell hyS' hzy hRs hs hhs (mem_ball.1 hqb) hpq hps'
  have hCTlt : C < T := lt_of_le_of_ne hCT (fun h' => hT (h' ▸ hCin))
  obtain ⟨hD, hDsub⟩ := test_ball_of_exit hηc hε x hadj hR hhR hmesh hCTlt hmin hT
  exact test_finishes_before_next_shell hηc x hadj hR hsep hCC hC1 hCT hCin hmin hT hTL hDsub hD hLmin hL

/-- Step 8 at the last shell (notes (7.39)-(7.41)): every vertex `x m` with `C ≤ m ≤ L` lies in
`U = V(K+B_r) \ Θ`. The level window `0 < f < r` near the centre comes from `level_near_centre` and
`level_window`; the adjacent vertex `x L` is controlled through the overlap point with `D`. -/
lemma last_shell_mem_U (hηc : Continuous η) (hε : 0 ≤ ε) (x : ℕ → ℤ)
    (hadj : ∀ n, (cell ε η (x n) ∩ cell ε η (x (n + 1))).Nonempty) {Θv : Set ℤ}
    (hΘK : ∀ a ∈ Θv, cell ε η a ⊆ K) {z : ℂ} {R lam : ℝ} (hR : 0 < R) (hRs : R ≤ s) (hs : 0 < s)
    (hs4 : s ≤ r / 4000) (hlam : lam ≤ r / 20) (hhR : h < R / 4)
    (hy : ∃ y ∈ twoSidedShell K r lam, dist z y ≤ R / 50)
    (hmesh : CellDiamLe ε η h (ball z (2 * R)))
    {C T L : ℕ} (hCT : C ≤ T) (hCin : x C ∈ interiorCellVertices ε η (ball z (4 * R / 3)))
    (hmin : ∀ n, C ≤ n → n < T → x n ∈ interiorCellVertices ε η (ball z (4 * R / 3)))
    (hT : x T ∉ interiorCellVertices ε η (ball z (4 * R / 3)))
    (hTL : T ≤ L)
    (hLmin : ∀ n, T ≤ n → n < L →
      x n ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x T)) (R / 4)))
    (hL : x L ∉ interiorCellVertices ε η (ball (vertexPoint ε η (x T)) (R / 4))) :
    ∀ m, C ≤ m → m ≤ L → x m ∈ cellVertices ε η {p | infDist p K < r} \ Θv := by
  intro m hCm hmL
  obtain ⟨y, hyS, hzy⟩ := hy
  have hyS' : |infDist y K - r / 2| = lam := hyS
  have hCTlt : C < T := lt_of_le_of_ne hCT (fun h' => hT (h' ▸ hCin))
  obtain ⟨hD0, hDsub⟩ := test_ball_of_exit hηc hε x hadj hR hhR hmesh hCTlt hmin hT
  -- the level window: points within `2R` of `z` have `0 < f < r`
  have hwin : ∀ u : ℂ, dist u z < 2 * R → 0 < infDist u K ∧ infDist u K < r := by
    intro u hu
    have h1 := abs_lt.1 (level_near_centre hyS' hzy hRs hs hu)
    exact level_window hlam hs4 (by linarith [h1.2])
  have hUcell : ∀ a : ℤ, (∀ p ∈ cell ε η a, 0 < infDist p K ∧ infDist p K < r) →
      a ∈ cellVertices ε η {p | infDist p K < r} \ Θv := by
    intro a ha
    exact vertex_mem_U hΘK ⟨vertexPoint ε η a, vertexPoint_mem_cell_nonneg hε η a⟩
      (fun p hp => (ha p hp).1) (fun p hp => (ha p hp).2)
  by_cases hm1 : m < T
  · apply hUcell
    intro p hp
    apply hwin p
    have hpb : p ∈ ball z (4 * R / 3) := cell_subset_of_mem_interior hηc (x m) (hmin m hCm hm1) hp
    have hpd : dist p z < 4 * R / 3 := mem_ball.1 hpb
    linarith
  by_cases hm2 : m < L
  · apply hUcell
    intro p hp
    apply hwin p
    have hDp : p ∈ ball (vertexPoint ε η (x T)) (R / 4) :=
      cell_subset_of_mem_interior hηc (x m) (hLmin m (not_lt.1 hm1) hm2) hp
    exact mem_ball.1 (hDsub hDp)
  -- the last vertex `x L`: its cell is adjacent to the cell of `x (L-1)`, which lies in `D`
  have hmL' : m = L := le_antisymm hmL (not_lt.1 hm2)
  rw [hmL']
  have hTL' : T < L := by
    refine lt_of_le_of_ne hTL ?_
    intro h'
    have hxL : x T = x L := congrArg x h'
    rw [← hxL] at hL
    exact hL hD0
  obtain ⟨w, hwc1, hwc2⟩ := hadj (L - 1)
  have hL1 : L - 1 + 1 = L := by omega
  rw [hL1] at hwc2
  have hwD : w ∈ ball (vertexPoint ε η (x T)) (R / 4) :=
    cell_subset_of_mem_interior hηc (x (L - 1)) (hLmin (L - 1) (by omega) (by omega)) hwc1
  have hwE : w ∈ ball z (2 * R) := hDsub hwD
  have hw1 : |infDist w K - r / 2| < lam + 3 * s := by
    have h1 := abs_lt.1 (level_near_centre hyS' hzy hRs hs (mem_ball.1 hwE))
    linarith [h1.2]
  apply hUcell
  intro p hp
  have hpd : dist p w ≤ h := hmesh (x L) ⟨w, hwc2, hwE⟩ p hp w hwc2
  have hlip := abs_infDist_sub_infDist_le K p w
  have htri := abs_sub_le (infDist p K) (infDist w K) (r / 2)
  exact level_window hlam hs4 (by linarith)

/-- Pathwise chain (notes (7.33), (7.38), (7.39), steps 4-9 of S7'). For a walk `x` with exit index `τ`
(`x τ ∉ U`) and the mesh hypotheses of z10 and `CellDiamLe` on the shell balls, the first hitting times
`hitTime k` (z10, step 4), the shell centres (z10, step 5, `shell_hit_choose_center`) and the first exit times
`T k`, `L k` (steps 6-8) satisfy:
* `T k ≤ T (k+1)` and `L k ≤ T (k+1)` for `k < n` (the pathwise forms of `hTT`, `hLT`, via
`T k < C_{k+1} < T_{k+1}` and `L k < C_{k+1}`), and `T n < τ`, `L n ≤ τ` (`hcross`, `hend`), in `ℕ∞`. -/
theorem shell_chain_pathwise {K : Set ℂ} {r s d h ε : ℝ} {η : ℝ → ℂ} {Θv : Set ℤ} {x : ℕ → ℤ} {n τ : ℕ}
    (hKne : K.Nonempty) (hη : Continuous η) (hε : 0 < ε) (hr : 0 < r) (hs : 0 < s)
    (hs4 : s ≤ r / 4000) (hd : 0 < d) (hh : h ≤ d / 100) (hds : d / 100 ≤ s / 100)
    (hadj : ∀ m, (cell ε η (x m) ∩ cell ε η (x (m + 1))).Nonempty)
    (hΘv : ∀ k ∈ Θv, cell ε η k ⊆ K)
    (hτ : x τ ∉ cellVertices ε η (thickening r K) \ Θv)
    (hstart : (cell ε η (x 0) ∩ frontier (thickening (r / 2) K)).Nonempty)
    (hdiam : ∀ m ≤ τ, ∀ p ∈ cell ε η (x m), ∀ q ∈ cell ε η (x m), dist p q ≤ h)
    (hNs : 20 * ((n + 1 : ℕ) : ℝ) * s ≤ r / 20)
    (R : ℂ → ℝ) (Elig : ℂ → Prop) (hR : ∀ w, Elig w → d ≤ R w ∧ R w ≤ s)
    (zc : ℕ → ℂ) (hzc : ∀ k ≤ n, zc k = gridRound (d / 100) (vertexPoint ε η (x (hitTime ε η K r s x k))))
    (hzElig : ∀ k ≤ n, Elig (zc k))
    (hmesh : ∀ k ≤ n, CellDiamLe ε η h (ball (zc k) (2 * R (zc k))))
    (T L : ℕ → ℕ)
    (hCT : ∀ k ≤ n, hitTime ε η K r s x k ≤ T k)
    (hTmin : ∀ k ≤ n, ∀ m, hitTime ε η K r s x k ≤ m → m < T k →
      x m ∈ interiorCellVertices ε η (ball (zc k) (4 * R (zc k) / 3)))
    (hTex : ∀ k ≤ n, x (T k) ∉ interiorCellVertices ε η (ball (zc k) (4 * R (zc k) / 3)))
    (hTL : ∀ k ≤ n, T k ≤ L k)
    (hLmin : ∀ k ≤ n, ∀ m, T k ≤ m → m < L k →
      x m ∈ interiorCellVertices ε η (ball (vertexPoint ε η (x (T k))) (R (zc k) / 4)))
    (hLex : ∀ k ≤ n, x (L k) ∉ interiorCellVertices ε η (ball (vertexPoint ε η (x (T k))) (R (zc k) / 4))) :
    (∀ k < n, (T k : ℕ∞) ≤ (T (k + 1) : ℕ∞) ∧ (L k : ℕ∞) ≤ (T (k + 1) : ℕ∞)) ∧
      (∀ k < n, T k < L k ∧ L k < hitTime ε η K r s x (k + 1)) ∧
      (T n : ℕ∞) < (τ : ℕ∞) ∧ (L n : ℕ∞) ≤ (τ : ℕ∞) := by
  -- step 4 (z10): all shells are hit before τ, and the hitting times strictly increase
  have hhs : h ≤ s / 100 := le_trans hh hds
  have hbad := bad_path_crosses_all_shells hKne hε hη hr hs hhs x τ (n + 1) Θv hΘv hτ
    (fun m _ => hadj m) hstart hdiam hNs
  obtain ⟨hhit, hlt, hmono⟩ := hbad
  have hC_lt : ∀ k ≤ n, hitTime ε η K r s x k < τ := fun k hk => hlt (k + 1) (by omega) (by omega)
  have hC_mono : ∀ k < n, hitTime ε η K r s x k < hitTime ε η K r s x (k + 1) :=
    fun k hk => hmono (k + 1) (by omega) (by omega)
  have hhit_mem : ∀ k ≤ n, (cell ε η (x (hitTime ε η K r s x k)) ∩
      twoSidedShell K r (shellOffset s (k + 1))).Nonempty := by
    intro k hk
    obtain ⟨m, -, hm⟩ := hhit (k + 1) (by omega) (by omega)
    exact firstShellHit_mem hm
  -- step 5 (z10, `shell_hit_choose_center`): the centre `z_k` and the good radius `R_k`
  have hsc : ∀ k ≤ n, (∃ y ∈ twoSidedShell K r (shellOffset s (k + 1)),
      dist (zc k) y ≤ R (zc k) / 50) ∧
      (∀ p ∈ cell ε η (x (hitTime ε η K r s x k)), dist p (zc k) < 4 * R (zc k) / 3) ∧
      d ≤ R (zc k) ∧ R (zc k) ≤ s := by
    intro k hk
    obtain ⟨⟨y, hy1, hy2⟩, hgh, -, hcell, hR'⟩ :=
      shell_hit_choose_center (g := d / 100) (lam := shellOffset s (k + 1)) (η := η) hε x
        (hitTime ε η K r s x k) R Elig (zc k) (fun p hp q hq => hdiam _ (hC_lt k hk).le p hp q hq)
        (hhit_mem k hk) rfl hd hh hR (hzc k hk) (hzElig k hk)
    exact ⟨⟨y, hy1, by linarith⟩, hcell, hR'.1, hR'.2.1⟩
  have hRpos : ∀ k ≤ n, 0 < R (zc k) := fun k hk => lt_of_lt_of_le hd (hsc k hk).2.2.1
  have hCinK : ∀ k ≤ n, x (hitTime ε η K r s x k) ∈
      interiorCellVertices ε η (ball (zc k) (4 * R (zc k) / 3)) := fun k hk =>
    mem_interior_of_cell_lt hε.le (by linarith [hRpos k hk]) (hsc k hk).2.1
  -- steps 6-9 at shells `k < n`, and the step-8 claim at the last shell
  have hstep : ∀ k < n, T k < L k ∧ L k < hitTime ε η K r s x (k + 1) ∧
      hitTime ε η K r s x (k + 1) < T (k + 1) := by
    intro k hk
    have hC1 : (cell ε η (x (hitTime ε η K r s x (k + 1))) ∩
        twoSidedShell K r (shellOffset s (k + 1) + 20 * s)).Nonempty := by
      rw [← shellOffset_succ]
      exact hhit_mem (k + 1) (by omega)
    obtain ⟨-, hTLk, hC⟩ := shell_step_order hη hε.le x hadj
      (hR := hRpos k (by omega)) (hRs := (hsc k (by omega)).2.2.2) (hs := hs)
      (hhs := by linarith [hh, hds]) (hhR := by linarith [hh, hds, (hsc k (by omega)).2.2.1, hRpos k (by omega)])
      (hy := (hsc k (by omega)).1) (hmesh := hmesh k (by omega)) (hCC := (hC_mono k hk).le)
      (hC1 := hC1) (hCT := hCT k (by omega)) (hCin := hCinK k (by omega))
      (hmin := hTmin k (by omega)) (hT := hTex k (by omega)) (hTL := hTL k (by omega))
      (hLmin := hLmin k (by omega)) (hL := hLex k (by omega))
    refine ⟨hTLk, hC, lt_of_le_of_ne (hCT (k + 1) (by omega)) (fun h' => hTex (k + 1) (by omega) ?_)⟩
    rw [← h']
    exact hCinK (k + 1) (by omega)
  -- step 8 at the last shell: `x m ∈ U` on `[C_n, L_n]`, so `τ ∉ [C_n, L_n]` and `L_n < τ`
  have hlamn : shellOffset s (n + 1) ≤ r / 20 := by
    unfold shellOffset
    exact hNs
  have hLn : L n < τ := by
    by_contra hcon
    have hset : thickening r K = {p | infDist p K < r} := by
      ext p
      exact mem_thickening_iff_infDist_lt hKne
    have hin := last_shell_mem_U hη hε.le x hadj hΘv (hR := hRpos n le_rfl)
      (hRs := (hsc n le_rfl).2.2.2) (hs := hs) (hs4 := hs4) (hlam := hlamn)
      (hhR := by linarith [hh, hds, (hsc n le_rfl).2.2.1, hRpos n le_rfl])
      (hy := (hsc n le_rfl).1) (hmesh := hmesh n le_rfl) (hCT := hCT n le_rfl)
      (hCin := hCinK n le_rfl) (hmin := hTmin n le_rfl) (hT := hTex n le_rfl)
      (hTL := hTL n le_rfl) (hLmin := hLmin n le_rfl) (hL := hLex n le_rfl)
    rw [hset] at hτ
    exact hτ (hin τ (hC_lt n le_rfl).le (not_lt.1 hcon))
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ⟨(hstep k hk).1, (hstep k hk).2.1⟩, ?_, ?_⟩
  · exact_mod_cast le_of_lt (lt_trans (hstep k hk).1 (lt_trans (hstep k hk).2.1 (hstep k hk).2.2))
  · exact_mod_cast le_of_lt (lt_trans (hstep k hk).2.1 (hstep k hk).2.2)
  · exact_mod_cast lt_of_le_of_lt (hTL n le_rfl) hLn
  · exact_mod_cast hLn.le

end Lemma68Window
end MatedCRT
