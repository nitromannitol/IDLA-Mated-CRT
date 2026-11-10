import MatedCRT.Defs.Map
import MatedCRT.FirstPass.S6r.Shells.Parameters

/-!
# Lemma 6.8, window S7': successive shell crossing (steps 3 and 4)

Steps 3 and 4 of the redesigned S7' (`notes/fp-gaps/CHATGPT-idla-6-8-shells.md`, displayed (7.14)-(7.22)).
Cells are `H^ε_k = η([ε(k-1), εk])` (`MatedCRT.cell`), vertices `η(εk)` (`MatedCRT.vertexPoint`), the walk
`X : ℕ → ℤ` is a legal graph trajectory (consecutive cells intersect), and `𝒞_m = ⋃_{n ≤ m} H_{X_n}` is the
connected union of the cells visited up to time `m` (displayed (7.16)).

Terminology: `K = closure Θ`, `f = dist(·, K)` (`Metric.infDist`), `K + B_r = {f < r}` (`Metric.thickening`),
`Σ_j` the two-sided shell of `Shells/Parameters.lean`.

The event `B = {X_n ∈ A for all n < τ_U}` of (7.15) is not an extra hypothesis: the deterministic argument of
(7.16)-(7.22) uses only the legal trajectory, the exit condition `X_{τ_U} ∉ U` with `U = V(K+B_r) \ Θ`, and the
starting cell.
-/

namespace MatedCRT.Lemma68Window

open Metric Set

/-- The vertex point `η(εk)` lies in its own cell `H^ε_k = η([ε(k-1), εk])`. -/
lemma vertexPoint_mem_cell {ε : ℝ} {η : ℝ → ℂ} (hε : 0 < ε) (k : ℤ) :
    vertexPoint ε η k ∈ cell ε η k :=
  ⟨ε * (k : ℝ), ⟨mul_le_mul_of_nonneg_left (by linarith) hε.le, le_refl _⟩, rfl⟩

/-- Each cell is connected (image of an interval under the continuous curve `η`). -/
lemma cell_isPreconnected {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (k : ℤ) :
    IsPreconnected (cell ε η k) :=
  isPreconnected_Icc.image η hη.continuousOn

/-- `f = dist(·, K)` is `1`-Lipschitz. -/
lemma abs_infDist_sub_infDist_le (K : Set ℂ) (p q : ℂ) :
    |infDist p K - infDist q K| ≤ dist p q := by
  rw [abs_sub_le_iff]
  constructor
  · have := infDist_le_infDist_add_dist (x := p) (y := q) (s := K)
    linarith [dist_comm p q]
  · have := infDist_le_infDist_add_dist (x := q) (y := p) (s := K)
    linarith [dist_comm p q]

/-- The union `𝒞_m = ⋃_{0 ≤ n ≤ m} H_{X_n}` of the cells visited up to time `m` (displayed (7.16)). -/
def pathCells (ε : ℝ) (η : ℝ → ℂ) (X : ℕ → ℤ) (m : ℕ) : Set ℂ :=
  ⋃ n ∈ Set.Iic m, cell ε η (X n)

lemma mem_pathCells_of_le {ε : ℝ} {η : ℝ → ℂ} {X : ℕ → ℤ} {n m : ℕ} (h : n ≤ m) {p : ℂ}
    (hp : p ∈ cell ε η (X n)) : p ∈ pathCells ε η X m :=
  Set.mem_iUnion₂.mpr ⟨n, h, hp⟩

/-- On a legal trajectory the cell-union `𝒞_m` is connected for `m ≤ τ`: consecutive cells intersect and
each cell is connected (displayed (7.16) and the proof of (7.16)). -/
lemma pathCells_isPreconnected {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (X : ℕ → ℤ) (τ : ℕ)
    (hlegal : ∀ n < τ, (cell ε η (X n) ∩ cell ε η (X (n + 1))).Nonempty) :
    ∀ m ≤ τ, IsPreconnected (pathCells ε η X m) := by
  intro m
  induction m with
  | zero =>
    intro _
    have h0 : pathCells ε η X 0 = cell ε η (X 0) := by
      ext p
      simp [pathCells]
    rw [h0]
    exact cell_isPreconnected hη _
  | succ m ih =>
    intro hm
    have hprev : IsPreconnected (pathCells ε η X m) := ih (by omega)
    have hset : pathCells ε η X (m + 1) = pathCells ε η X m ∪ cell ε η (X (m + 1)) := by
      ext p
      simp only [pathCells, Set.mem_union, Set.mem_iUnion, Set.mem_Iic]
      constructor
      · rintro ⟨n, hn, hp⟩
        rcases Nat.lt_or_ge n (m + 1) with h | h
        · exact Or.inl ⟨n, by omega, hp⟩
        · have hnm : n = m + 1 := by omega
          subst hnm
          exact Or.inr hp
      · rintro (⟨n, hn, hp⟩ | hp)
        · exact ⟨n, by omega, hp⟩
        · exact ⟨m + 1, le_refl _, hp⟩
    rw [hset]
    obtain ⟨p, hp1, hp2⟩ := hlegal m (by omega)
    exact IsPreconnected.union' ⟨p, mem_pathCells_of_le le_rfl hp1, hp2⟩ hprev
      (cell_isPreconnected hη _)

/-- A preconnected subset of `ℝ` contains the interval between any two of its points. -/
lemma uIcc_subset_of_preconnected {s : Set ℝ} (hs : IsPreconnected s) {a b : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) : uIcc a b ⊆ s := by
  rcases le_total a b with h | h
  · rw [Set.uIcc_of_le h]; exact hs.Icc_subset ha hb
  · rw [Set.uIcc_of_ge h]; exact hs.Icc_subset hb ha

/-- Intermediate values along the walk: a level `t` between two values of `f` attained on `𝒞_m` is attained
on a cell `H_{X_n}` with `n ≤ m` (connectedness of `𝒞_m`, displayed (7.19)). -/
lemma exists_level_on_path {K : Set ℂ} {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) (X : ℕ → ℤ) {τ m : ℕ}
    (hm : m ≤ τ) (hlegal : ∀ n < τ, (cell ε η (X n) ∩ cell ε η (X (n + 1))).Nonempty)
    {a b t : ℝ} {p₀ p₁ : ℂ} (hp₀ : p₀ ∈ pathCells ε η X m) (ha : infDist p₀ K = a)
    (hp₁ : p₁ ∈ pathCells ε η X m) (hb : infDist p₁ K = b) (ht : t ∈ uIcc a b) :
    ∃ n ≤ m, ∃ p ∈ cell ε η (X n), infDist p K = t := by
  have hI : IsPreconnected ((fun x => infDist x K) '' pathCells ε η X m) :=
    (pathCells_isPreconnected hη X τ hlegal m hm).image _
      (Metric.continuous_infDist_pt K).continuousOn
  have hsub := uIcc_subset_of_preconnected hI (⟨p₀, hp₀, ha⟩ : a ∈ (fun x => infDist x K) '' pathCells ε η X m)
    (⟨p₁, hp₁, hb⟩ : b ∈ (fun x => infDist x K) '' pathCells ε η X m)
  obtain ⟨p, hp, hpt⟩ := hsub ht
  simp only [pathCells, Set.mem_iUnion, Set.mem_Iic] at hp
  obtain ⟨n, hn, hpn⟩ := hp
  exact ⟨n, hn, p, hpn, hpt⟩

/-- The first hitting index `C_j = inf {n ≥ 0 : H_{X_n} ∩ Σ ≠ ∅}` (displayed (7.20)). -/
noncomputable def firstShellHit (ε : ℝ) (η : ℝ → ℂ) (X : ℕ → ℤ) (S : Set ℂ) : ℕ :=
  sInf {n : ℕ | (cell ε η (X n) ∩ S).Nonempty}

lemma firstShellHit_le {ε : ℝ} {η : ℝ → ℂ} {X : ℕ → ℤ} {S : Set ℂ} {n : ℕ}
    (hn : (cell ε η (X n) ∩ S).Nonempty) : firstShellHit ε η X S ≤ n :=
  Nat.sInf_le (show n ∈ {m : ℕ | (cell ε η (X m) ∩ S).Nonempty} from hn)

lemma firstShellHit_mem {ε : ℝ} {η : ℝ → ℂ} {X : ℕ → ℤ} {S : Set ℂ} {n : ℕ}
    (hn : (cell ε η (X n) ∩ S).Nonempty) :
    (cell ε η (X (firstShellHit ε η X S)) ∩ S).Nonempty :=
  Nat.sInf_mem (⟨n, hn⟩ : Set.Nonempty {m : ℕ | (cell ε η (X m) ∩ S).Nonempty})

/-- Displayed (7.14), referee repair of step 3: the starting cell `H_a` meets `∂(K + B_{r/2})` at a point `p_a`,
and for **every** `u ∈ H_a` one has `|f(u) - r/2| ≤ |u - p_a| ≤ h_ε` (`f = dist(·, K)`), not only for the vertex
`η(a)`. Since `h_ε ≤ d/100 ≤ s/100 < 20 s = λ_1`, no point of the whole starting cell lies on a shell of offset
`≥ 20 s`. -/
theorem initial_cell_between_shells {K : Set ℂ} (hKne : K.Nonempty) {ε r h d s : ℝ} {η : ℝ → ℂ}
    {k0 : ℤ} (hmeet : (cell ε η k0 ∩ frontier (thickening (r / 2) K)).Nonempty)
    (hdiam : ∀ p ∈ cell ε η k0, ∀ q ∈ cell ε η k0, dist p q ≤ h)
    (hh : h ≤ d / 100) (hsd : d / 100 ≤ s / 100) (hs : 0 < s) :
    (∀ p ∈ cell ε η k0, |infDist p K - r / 2| ≤ h) ∧ h < 20 * s ∧
      ∀ lam : ℝ, 20 * s ≤ lam → ∀ p ∈ cell ε η k0, p ∉ twoSidedShell K r lam := by
  obtain ⟨q, hqcell, hqfr⟩ := hmeet
  have hq : infDist q K = r / 2 := frontier_thickening_subset_level hKne (r / 2) hqfr
  have hlt : h < 20 * s := by linarith
  have hbound : ∀ p ∈ cell ε η k0, |infDist p K - r / 2| ≤ h := by
    intro p hp
    have h1 := abs_infDist_sub_infDist_le K p q
    rw [hq] at h1
    exact h1.trans (hdiam p hp q hqcell)
  refine ⟨hbound, hlt, ?_⟩
  intro lam hlam p hp hSig
  have hSig' : |infDist p K - r / 2| = lam := hSig
  have h3 := hbound p hp
  linarith

/-- Step 4, displayed (7.15)-(7.22): on a legal trajectory which exits `U = V(K+B_r) \ Θ` at `τ`, every shell
`Σ_j`, `1 ≤ j ≤ N`, is hit before `τ`, and the first hitting times are strictly increasing in `j`:
`C_1 < C_2 < ⋯ < C_N < τ`. -/
theorem bad_path_crosses_all_shells {K : Set ℂ} (hKne : K.Nonempty) {ε r h s : ℝ} {η : ℝ → ℂ}
    (hε : 0 < ε) (hη : Continuous η) (hr : 0 < r) (hs : 0 < s) (hhs : h ≤ s / 100)
    (X : ℕ → ℤ) (τ N : ℕ) (Θv : Set ℤ)
    (hΘv : ∀ k ∈ Θv, cell ε η k ⊆ K)
    (hτ : X τ ∉ cellVertices ε η (thickening r K) \ Θv)
    (hlegal : ∀ n < τ, (cell ε η (X n) ∩ cell ε η (X (n + 1))).Nonempty)
    (hstart : (cell ε η (X 0) ∩ frontier (thickening (r / 2) K)).Nonempty)
    (hdiam : ∀ n ≤ τ, ∀ p ∈ cell ε η (X n), ∀ q ∈ cell ε η (X n), dist p q ≤ h)
    (hNs : 20 * (N : ℝ) * s ≤ r / 20) :
    (∀ j : ℕ, 1 ≤ j → j ≤ N →
      ∃ n ≤ τ, (cell ε η (X n) ∩ twoSidedShell K r (shellOffset s j)).Nonempty) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ N → firstShellHit ε η X (twoSidedShell K r (shellOffset s j)) < τ) ∧
    (∀ j : ℕ, 1 ≤ j → j < N →
      firstShellHit ε η X (twoSidedShell K r (shellOffset s j)) <
        firstShellHit ε η X (twoSidedShell K r (shellOffset s (j + 1)))) := by
  have hoff : ∀ j : ℕ, 1 ≤ j → j ≤ N → 0 ≤ shellOffset s j ∧ shellOffset s j ≤ r / 20 := by
    intro j hj1 hjN
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hjN' : (j : ℝ) ≤ N := by exact_mod_cast hjN
    unfold shellOffset
    constructor <;> nlinarith
  -- the starting cell carries a point with f = r/2
  obtain ⟨q0, hq0cell, hq0fr⟩ := hstart
  have hq0 : infDist q0 K = r / 2 := frontier_thickening_subset_level hKne (r / 2) hq0fr
  -- the terminal cell: every point has f = 0 (inner exit) or f ≥ r (outer exit)
  have hterm_all : ∀ p ∈ cell ε η (X τ), infDist p K = 0 ∨ r ≤ infDist p K := by
    intro p hp
    by_cases hΘ : X τ ∈ Θv
    · exact Or.inl (infDist_zero_of_mem (hΘv _ hΘ hp))
    · right
      by_contra hcon
      apply hτ
      have hmemV : X τ ∈ cellVertices ε η (thickening r K) :=
        (⟨p, hp, (mem_thickening_iff_infDist_lt hKne).mpr (not_le.mp hcon)⟩ :
          (cell ε η (X τ) ∩ thickening r K).Nonempty)
      exact (Set.mem_sdiff _).mpr ⟨hmemV, hΘ⟩
  have hvT : vertexPoint ε η (X τ) ∈ cell ε η (X τ) := vertexPoint_mem_cell hε _
  have hP0 : q0 ∈ pathCells ε η X τ := mem_pathCells_of_le (Nat.zero_le τ) hq0cell
  have hPt : vertexPoint ε η (X τ) ∈ pathCells ε η X τ := mem_pathCells_of_le le_rfl hvT
  -- (7.19): every shell level is attained on the path
  have hcross : ∀ lam : ℝ, 0 ≤ lam → lam ≤ r / 20 →
      ∃ n ≤ τ, (cell ε η (X n) ∩ twoSidedShell K r lam).Nonempty := by
    intro lam hl0 hl1
    rcases hterm_all _ hvT with hT0 | hTr
    · obtain ⟨n, hn, p, hpn, hfp⟩ := exists_level_on_path hη X le_rfl hlegal hP0 hq0 hPt hT0
        (Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩) :
          r / 2 - lam ∈ uIcc (r / 2) 0)
      have hSig : |infDist p K - r / 2| = lam := by
        rw [hfp, show r / 2 - lam - r / 2 = -lam by ring, abs_neg, abs_of_nonneg hl0]
      exact ⟨n, hn, p, hpn, hSig⟩
    · obtain ⟨n, hn, p, hpn, hfp⟩ := exists_level_on_path hη X le_rfl hlegal hP0 hq0 hPt rfl
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩) :
          r / 2 + lam ∈ uIcc (r / 2) (infDist (vertexPoint ε η (X τ)) K))
      have hSig : |infDist p K - r / 2| = lam := by
        rw [hfp, show r / 2 + lam - r / 2 = lam by ring, abs_of_nonneg hl0]
      exact ⟨n, hn, p, hpn, hSig⟩
  -- the terminal cell misses every shell
  have hterm_empty : ∀ lam : ℝ, lam ≤ r / 20 → ∀ p ∈ cell ε η (X τ), p ∉ twoSidedShell K r lam := by
    intro lam hlam p hp hSig
    have hb := shell_band hlam hSig
    rcases hterm_all p hp with h0 | hr'
    · rw [h0] at hb
      linarith [hb.1]
    · linarith [hb.2]
  -- (7.21): C_j < τ
  have hlt_tau : ∀ lam : ℝ, 0 ≤ lam → lam ≤ r / 20 →
      firstShellHit ε η X (twoSidedShell K r lam) < τ := by
    intro lam hl0 hl1
    obtain ⟨n, hn, hne⟩ := hcross lam hl0 hl1
    have hle := firstShellHit_le (S := twoSidedShell K r lam) hne
    have hmem := firstShellHit_mem (S := twoSidedShell K r lam) hne
    have hne_tau : firstShellHit ε η X (twoSidedShell K r lam) ≠ τ := by
      intro heq
      rw [heq] at hmem
      obtain ⟨p, hp1, hp2⟩ := hmem
      exact hterm_empty lam hl1 p hp1 hp2
    omega
  -- (7.22): C_j < C_{j+1}
  have hstep_gen : ∀ lam mu : ℝ, 0 ≤ lam → mu = lam + 20 * s → mu ≤ r / 20 →
      firstShellHit ε η X (twoSidedShell K r lam) < firstShellHit ε η X (twoSidedShell K r mu) := by
    intro lam mu hl0 hmu hmu1
    have hlam1 : lam ≤ r / 20 := by linarith
    obtain ⟨_, _, hne'⟩ := hcross mu (by linarith) hmu1
    have hnτ : firstShellHit ε η X (twoSidedShell K r mu) < τ := hlt_tau mu (by linarith) hmu1
    have hmu_cell := firstShellHit_mem (S := twoSidedShell K r mu) hne'
    set n := firstShellHit ε η X (twoSidedShell K r mu) with hn_def
    obtain ⟨q, hqcell, hqSig⟩ := hmu_cell
    have hqabs : |infDist q K - r / 2| = mu := hqSig
    have hqn : q ∈ pathCells ε η X n := mem_pathCells_of_le le_rfl hqcell
    have hP0n : q0 ∈ pathCells ε η X n := mem_pathCells_of_le (Nat.zero_le n) hq0cell
    have hle : firstShellHit ε η X (twoSidedShell K r lam) ≤ n := by
      have hnle : n ≤ τ := hnτ.le
      rcases le_total (r / 2) (infDist q K) with hge | hle'
      · have hqv : infDist q K - r / 2 = mu := by
          rw [abs_of_nonneg (show (0:ℝ) ≤ infDist q K - r / 2 by linarith)] at hqabs
          exact hqabs
        obtain ⟨m, hm, p, hpm, hfp⟩ := exists_level_on_path hη X hnle hlegal hP0n hq0 hqn rfl
          (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩) :
            r / 2 + lam ∈ uIcc (r / 2) (infDist q K))
        have hSig : |infDist p K - r / 2| = lam := by
          rw [hfp, show r / 2 + lam - r / 2 = lam by ring, abs_of_nonneg hl0]
        have hne_m : (cell ε η (X m) ∩ twoSidedShell K r lam).Nonempty := ⟨p, hpm, hSig⟩
        exact le_trans (firstShellHit_le hne_m) hm
      · have hqv : -(infDist q K - r / 2) = mu := by
          rw [abs_of_nonpos (show infDist q K - r / 2 ≤ 0 by linarith)] at hqabs
          exact hqabs
        obtain ⟨m, hm, p, hpm, hfp⟩ := exists_level_on_path hη X hnle hlegal hP0n hq0 hqn rfl
          (Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩) :
            r / 2 - lam ∈ uIcc (r / 2) (infDist q K))
        have hSig : |infDist p K - r / 2| = lam := by
          rw [hfp, show r / 2 - lam - r / 2 = -lam by ring, abs_neg, abs_of_nonneg hl0]
        have hne_m : (cell ε η (X m) ∩ twoSidedShell K r lam).Nonempty := ⟨p, hpm, hSig⟩
        exact le_trans (firstShellHit_le hne_m) hm
    have hne_eq : firstShellHit ε η X (twoSidedShell K r lam) ≠ n := by
      intro heq
      obtain ⟨_, _, hne0⟩ := hcross lam hl0 hlam1
      have hcellLam := firstShellHit_mem (S := twoSidedShell K r lam) hne0
      rw [heq] at hcellLam
      obtain ⟨p, hpcell, hpSig⟩ := hcellLam
      have hpabs : |infDist p K - r / 2| = lam := hpSig
      have hkey := abs_sub_abs_le_abs_sub (infDist q K - r / 2) (infDist p K - r / 2)
      rw [hqabs, hpabs, show infDist q K - r / 2 - (infDist p K - r / 2) = infDist q K - infDist p K by ring]
        at hkey
      have hd := hdiam n hnτ.le q hqcell p hpcell
      have hlip := abs_infDist_sub_infDist_le K q p
      linarith
    exact lt_of_le_of_ne hle hne_eq
  refine ⟨fun j hj1 hjN => ?_, fun j hj1 hjN => ?_, fun j hj1 hjN => ?_⟩
  · obtain ⟨n, hn, hne⟩ := hcross (shellOffset s j) (hoff j hj1 hjN).1 (hoff j hj1 hjN).2
    exact ⟨n, hn, hne⟩
  · exact hlt_tau _ (hoff j hj1 hjN).1 (hoff j hj1 hjN).2
  · refine hstep_gen _ _ (hoff j hj1 (by omega)).1 ?_ (hoff (j + 1) (by omega) (by omega)).2
    unfold shellOffset
    push_cast
    ring

end MatedCRT.Lemma68Window
