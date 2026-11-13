import MatedCRT.FirstPass.Derived.ExitDecomposition
import MatedCRT.FirstPass.Derived.InterpolatedWalkPath

/-!
# Interpolated walks that agree after their exit times

Let `A' ⊆ A` be vertex sets and let `x, y` be two walks whose post-exit paths from `A'` agree,
`x (T_x + k) = y (T_y + k)` for all `k`, where `T_x, T_y` are the exit times from `A'`.  Then the exit
times from `A` are `τ_x = T_x + e` and `τ_y = T_y + e` with the same `e` (the exit time of the common
post-exit path), and the linearly interpolated embedded walks `t ↦ interpPathFn v m x t`, run at speed
`m > 0`, satisfy
`f ((t + T_x / m) ∧ (τ_x / m)) = g ((t + T_y / m) ∧ (τ_y / m))` for every `t ≥ 0`
(Berestycki–Gwynne (2020), (6.41)): after the time shifts `T_x / m` and `T_y / m` the two stopped paths
coincide.  This is the deterministic input to the comparison of two stopped walks in the proof of
Proposition 6.12.
-/

set_option autoImplicit false

open scoped NNReal

namespace MatedCRT
namespace ExitCouplingPath

open MatedCRT.ExitDecomposition

/-- Linear interpolation commutes with an integer shift of the argument. -/
lemma linInterp_add_nat (a : ℕ → ℂ) {s : ℝ} (hs : 0 ≤ s) (N : ℕ) :
    linInterp a (s + N) = linInterp (fun k => a (N + k)) s := by
  have hf : ⌊s + N⌋₊ = ⌊s⌋₊ + N := Nat.floor_add_natCast hs N
  unfold linInterp
  rw [hf]
  have h1 : s + N - ((⌊s⌋₊ + N : ℕ) : ℝ) = s - ⌊s⌋₊ := by push_cast; ring
  rw [h1]
  have e1 : a (N + ⌊s⌋₊) = a (⌊s⌋₊ + N) := by rw [add_comm]
  have e2 : a (N + (⌊s⌋₊ + 1)) = a (⌊s⌋₊ + N + 1) := by rw [show N + (⌊s⌋₊ + 1) = ⌊s⌋₊ + N + 1 by ring]
  simp only [e1, e2]

/-- The interpolated walk at speed `m > 0` after the time `N / m` is the interpolated shifted walk. -/
lemma interpPathFn_add_div (v : ℤ → ℂ) {m : ℝ≥0} (hm : 0 < m) (x : ℕ → ℤ) (N : ℕ) (s : ℝ≥0) :
    interpPathFn v m x (s + (N : ℝ≥0) / m) = interpPathFn v m (WalkPotential.pathShift N x) s := by
  unfold interpPathFn
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h1 : (m : ℝ) * ((s + (N : ℝ≥0) / m : ℝ≥0) : ℝ) = m * s + N := by
    push_cast
    field_simp
  rw [h1, linInterp_add_nat _ (by positivity) N]
  rfl

/-- The stopped interpolated walks coincide after the shifts when the walks agree after the shifts. -/
theorem interpPathFn_coupled_stopped (v : ℤ → ℂ) {m : ℝ≥0} (hm : 0 < m) {x y : ℕ → ℤ} {Tx Ty d : ℕ}
    (h : ∀ k, x (Tx + k) = y (Ty + k)) (t : ℝ≥0) :
    interpPathFn v m x (min (t + (Tx : ℝ≥0) / m) (((Tx + d : ℕ) : ℝ≥0) / m)) =
      interpPathFn v m y (min (t + (Ty : ℝ≥0) / m) (((Ty + d : ℕ) : ℝ≥0) / m)) := by
  have key : ∀ (N : ℕ), min (t + (N : ℝ≥0) / m) (((N + d : ℕ) : ℝ≥0) / m) =
      min t ((d : ℝ≥0) / m) + (N : ℝ≥0) / m := by
    intro N
    have : (((N + d : ℕ) : ℝ≥0) / m) = (d : ℝ≥0) / m + (N : ℝ≥0) / m := by
      push_cast; rw [add_div, add_comm]
    rw [this, min_add_add_right]
  rw [key Tx, key Ty, interpPathFn_add_div v hm, interpPathFn_add_div v hm]
  congr 1
  funext k
  exact h k

/-- A walk is in `A` before the time `T` iff its exit time from `A` is `T` plus the exit time of the shifted walk. -/
lemma vExitTime_eq_add_pathShift {A : Set ℤ} {x : ℕ → ℤ} {T : ℕ} (hT : ∀ n < T, x n ∈ A) :
    vExitTime A x = (T : ℕ∞) + vExitTime A (WalkPotential.pathShift T x) := by
  cases hs : vExitTime A (WalkPotential.pathShift T x) with
  | top =>
    have hTt : (T : ℕ∞) + ⊤ = ⊤ := by simp
    rw [hTt]
    by_contra hne
    obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
    obtain ⟨hxN, hj⟩ := (MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec A x N).1 hN.symm
    have hTN : T ≤ N := by
      by_contra hlt
      exact hxN (hT N (not_le.1 hlt))
    have h2 := (MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec A (WalkPotential.pathShift T x)
      (N - T)).2 ⟨?_, ?_⟩
    · rw [hs] at h2
      exact ENat.top_ne_natCast _ h2
    · simpa [WalkPotential.pathShift, Nat.add_sub_cancel' hTN] using hxN
    · intro j hjk
      exact hj (T + j) (by omega)
  | coe k =>
    obtain ⟨hxk, hj⟩ := (MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec A _ k).1 hs
    rw [← Nat.cast_add, MatedCRT.FirstPass36.H2.vExitTime_eq_coe_iff_spec]
    refine ⟨hxk, fun j hjk => ?_⟩
    by_cases hjT : j < T
    · exact hT j hjT
    · have := hj (j - T) (by omega)
      simpa [WalkPotential.pathShift, Nat.add_sub_cancel' (not_lt.1 hjT)] using this

/-- **(6.41), deterministic form.**  Let `A' ⊆ A`.  If two walks agree after
their exit times from `A'`, and the post-exit path leaves `A` in finite time (no finiteness of the exit times from `A'` is needed), then the interpolated walks
stopped at the exit time from `A` agree after the shifts by the exit times from `A'`. -/
theorem interpPathFn_coupled_of_postExit_eq (v : ℤ → ℂ) {m : ℝ≥0} (hm : 0 < m) {A' A : Set ℤ}
    (hA : A' ⊆ A) {x y : ℕ → ℤ}
    (hpost : postExit A' x = postExit A' y) (he : vExitTime A (postExit A' x) ≠ ⊤) (t : ℝ≥0) :
    interpPathFn v m x (min (t + ((vExitTime A' x).toNat : ℝ≥0) / m)
        (((vExitTime A x).toNat : ℝ≥0) / m)) =
      interpPathFn v m y (min (t + ((vExitTime A' y).toNat : ℝ≥0) / m)
        (((vExitTime A y).toNat : ℝ≥0) / m)) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 he
  have hxA := vExitTime_eq_add_pathShift (A := A) (x := x) (T := (vExitTime A' x).toNat)
    (fun n hn => hA (mem_of_lt_toNat hn))
  have hyA := vExitTime_eq_add_pathShift (A := A) (x := y) (T := (vExitTime A' y).toNat)
    (fun n hn => hA (mem_of_lt_toNat hn))
  have hpy : vExitTime A (WalkPotential.pathShift (vExitTime A' y).toNat y) = (d : ℕ∞) := by
    have := hpost ▸ hd.symm
    exact this
  have hpx : vExitTime A (WalkPotential.pathShift (vExitTime A' x).toNat x) = (d : ℕ∞) := hd.symm
  rw [hpx, ← Nat.cast_add] at hxA
  rw [hpy, ← Nat.cast_add] at hyA
  rw [hxA, hyA, ENat.toNat_natCast, ENat.toNat_natCast]
  exact interpPathFn_coupled_stopped v hm (d := d) (fun k => congrFun hpost k) t

end ExitCouplingPath
end MatedCRT
