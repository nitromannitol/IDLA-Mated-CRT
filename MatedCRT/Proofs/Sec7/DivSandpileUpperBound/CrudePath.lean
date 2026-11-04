import MatedCRT.Defs.Map
import MatedCRT.Proofs.Sec7.DivSandpileUpperBound.Iteration

/-! Deterministic boundary crossing and path length estimates for Step 3 of Proposition 7.1. -/

namespace MatedCRT.Sec7

open Set

/-- A chain of at most `n` metric jumps of size `D` travels at most `n * D`. -/
theorem dist_path_le {X : Type*} [PseudoMetricSpace X] (x : ℕ → X) (D : ℝ)
    (n : ℕ) (hstep : ∀ k < n, dist (x k) (x (k + 1)) ≤ D) :
    dist (x 0) (x n) ≤ (n : ℝ) * D := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun k hk => hstep k (by omega))
    have hlast := hstep n (by omega)
    calc
      dist (x 0) (x (n + 1)) ≤ dist (x 0) (x n) + dist (x n) (x (n + 1)) := dist_triangle _ _ _
      _ ≤ (n : ℝ) * D + D := add_le_add hprev hlast
      _ = ((n + 1 : ℕ) : ℝ) * D := by push_cast; ring

/-- An increasing path from outside a set to inside it first reaches its outer graph boundary
after at most `M / d` edges, provided the odometer is at most `M` on that boundary. -/
theorem increasing_path_hits_boundary {α : Type*} (m : α → α → ℕ) (Θ : Set α)
    (x : ℕ → α) (u : α → ℝ) (d M : ℝ) (N : ℕ)
    (hsymm : ∀ a b, m a b = m b a) (hd : 0 < d) (hu0 : 0 ≤ u (x 0))
    (hout : x 0 ∉ Θ) (hin : x N ∈ Θ)
    (hedge : ∀ k < N, m (x k) (x (k + 1)) ≠ 0)
    (hinc : ∀ k < N, u (x k) + d ≤ u (x (k + 1)))
    (hbound : ∀ a ∈ vBoundary m Θ, u a ≤ M) :
    ∃ k < N, x k ∈ vBoundary m Θ ∧ (k : ℝ) ≤ M / d := by
  classical
  let n := Nat.find (show ∃ i, x i ∈ Θ from ⟨N, hin⟩)
  have hn : x n ∈ Θ := Nat.find_spec (show ∃ i, x i ∈ Θ from ⟨N, hin⟩)
  have hnN : n ≤ N := Nat.find_min' (show ∃ i, x i ∈ Θ from ⟨N, hin⟩) hin
  have hn0 : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    exact hout (this ▸ hn)
  let k := n - 1
  have hkn : k + 1 = n := by dsimp [k]; omega
  have hkN : k < N := by omega
  have hkn' : k < n := by omega
  have hkout : x k ∉ Θ := Nat.find_min (show ∃ i, x i ∈ Θ from ⟨N, hin⟩) hkn'
  have hb : x k ∈ vBoundary m Θ := by
    refine ⟨hkout, x (k + 1), ?_, ?_⟩
    · simpa [hkn] using hn
    · rw [hsymm]; exact hedge k hkN
  have hkbound := increasing_path_length_bound (fun j => u (x j)) d hd k
    (fun j hj => hinc j (by omega))
  refine ⟨k, hkN, hb, ?_⟩
  have hbnd := hbound (x k) hb
  apply hkbound.trans
  exact div_le_div_of_nonneg_right (by linarith) hd.le

/-- The preceding crossing is within `D * M / d` when each edge of the path has
Euclidean diameter at most `D`. -/
theorem increasing_path_boundary_distance {α X : Type*} [PseudoMetricSpace X]
    (m : α → α → ℕ) (Θ : Set α) (x : ℕ → α) (f : α → X) (u : α → ℝ)
    (d M D : ℝ) (N : ℕ) (hsymm : ∀ a b, m a b = m b a) (hd : 0 < d)
    (hD : 0 ≤ D) (hu0 : 0 ≤ u (x 0)) (hout : x 0 ∉ Θ) (hin : x N ∈ Θ)
    (hedge : ∀ k < N, m (x k) (x (k + 1)) ≠ 0)
    (hinc : ∀ k < N, u (x k) + d ≤ u (x (k + 1)))
    (hdist : ∀ k < N, dist (f (x k)) (f (x (k + 1))) ≤ D)
    (hbound : ∀ a ∈ vBoundary m Θ, u a ≤ M) :
    ∃ k < N, x k ∈ vBoundary m Θ ∧ dist (f (x 0)) (f (x k)) ≤ M / d * D := by
  obtain ⟨k, hkN, hb, hk⟩ := increasing_path_hits_boundary m Θ x u d M N
    hsymm hd hu0 hout hin hedge hinc hbound
  exact ⟨k, hkN, hb, (dist_path_le (fun j => f (x j)) D k
    (fun j hj => hdist j (by omega))).trans (mul_le_mul_of_nonneg_right hk hD)⟩

/-- List-path form of the crude boundary distance estimate, matching the increasing paths of
Lemma 7.4. -/
theorem increasing_list_path_boundary_distance {α X : Type*} [PseudoMetricSpace X]
    (m : α → α → ℕ) (Θ : Set α) (p : List α) (a b : α) (f : α → X) (u : α → ℝ)
    (d M D : ℝ) (hsymm : ∀ a b, m a b = m b a) (hd : 0 < d) (hD : 0 ≤ D)
    (hu0 : 0 ≤ u a) (hout : a ∉ Θ) (hin : b ∈ Θ)
    (hhead : p.head? = some a) (hlast : p.getLast? = some b)
    (hedge : p.IsChain fun c e => m c e ≠ 0)
    (hinc : p.IsChain fun c e => u c + d ≤ u e)
    (hdist : ∀ c ∈ p, ∀ e ∈ p, m c e ≠ 0 → dist (f c) (f e) ≤ D)
    (hbound : ∀ c ∈ vBoundary m Θ, u c ≤ M) :
    ∃ c ∈ vBoundary m Θ, c ∈ p ∧ dist (f a) (f c) ≤ M / d * D := by
  classical
  have hp : 0 < p.length := by
    cases p with
    | nil => simp at hhead
    | cons c q => simp
  let N := p.length - 1
  let x : ℕ → α := fun k => (p[k]?).getD a
  have hN : N + 1 = p.length := by dsimp [N]; omega
  have hx0 : x 0 = a := by simpa [x, ← List.head?_eq_getElem?] using congrArg (fun z => z.getD a) hhead
  have hxN : x N = b := by
    have hlast' : p[N]? = some b := by simpa [N, List.getLast?_eq_getElem?] using hlast
    simp [x, hlast']
  have hxget : ∀ k (hk : k < p.length), x k = p[k] := by
    intro k hk
    simp [x, List.getElem?_eq_getElem hk]
  have hmem : ∀ k < p.length, x k ∈ p := by
    intro k hk
    rw [hxget k hk]
    exact List.getElem_mem hk
  obtain ⟨k, hk, hbd, hdist'⟩ := increasing_path_boundary_distance m Θ x f u d M D N
    hsymm hd hD (by simpa [hx0] using hu0) (by simpa [hx0] using hout) (by simpa [hxN] using hin)
    (by
      intro j hj
      have hj' : j + 1 < p.length := by omega
      simpa [hxget j (by omega), hxget (j + 1) hj'] using List.isChain_iff_getElem.mp hedge j hj')
    (by
      intro j hj
      have hj' : j + 1 < p.length := by omega
      simpa [hxget j (by omega), hxget (j + 1) hj'] using List.isChain_iff_getElem.mp hinc j hj')
    (by
      intro j hj
      apply hdist (x j) (hmem j (by omega)) (x (j + 1)) (hmem (j + 1) (by omega))
      have hj' : j + 1 < p.length := by omega
      simpa [hxget j (by omega), hxget (j + 1) hj'] using List.isChain_iff_getElem.mp hedge j hj') hbound
  exact ⟨x k, hbd, hmem k (by omega), by simpa [hx0] using hdist'⟩

end MatedCRT.Sec7
