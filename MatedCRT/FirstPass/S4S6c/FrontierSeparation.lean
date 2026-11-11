import MatedCRT.FirstPass.S4S6c.TraceFrom68
import MatedCRT.Proofs.Sec6.ConstantOrderLowerBound.Walk
import MatedCRT.Proofs.Infra.RandomWalk

/-!
# Frontier separation for the trace of Lemma 6.7

Printed proof of Lemma 6.7 (paper `lemma:constant-order-lower-bound`, corrected paper lines 2776-2792):
the walk from `a ∈ cl(Θ)` reaches the frontier `F = V(∂(Θ̄ + B_{r/2}))` before it exits
`V = V(Θ̄ + B_r)`, by the cell-size estimate `lemma:cell-size-estimate`. The printed
The printed proof of Lemma 6.7: connectedness of the successive cells
and the smallness of their diameters.

Notation. `cell v ⊆ ℂ` is the cell of the vertex `v ∈ ℤ`; `U1` is the open inner set `Θ̄ + B_{r/2}` and
`U2 ⊇ U1 ∪ ∂U1` the outer set `Θ̄ + B_r`. `meetVerts cell U2` is `V(U2)`, the vertices whose closed cell meets
`U2`; `frontierVerts cell U1` is `V(∂U1)`.

Deterministic core (`exists_frontierVerts_before_exit`): each cell is connected and nonempty, adjacent vertices
have intersecting closed cells, and the closed start cell lies in `U1`. Probabilistic packaging
(`srwLaw_frontier_separation`): a.s. steps are stays or edges (`srwLaw_ae_step`), a.s. start
(`srwLaw_ae_start`), and a.s. finite exit from a finite `V(U2)` (`finite_expectedExitTime`).

Inputs not proved here (named as hypotheses): the cell geometry of the environment, namely connected nonempty
cells, adjacency by intersecting closed cells, the start-cell inclusion `closure (cell a) ⊆ U1` (from the
cell-size estimate `lemma:cell-size-estimate` and `a ∈ cl Θ`), and finiteness of `V(U2)`.
-/

open MeasureTheory Set Function
open scoped ENNReal

namespace MatedCRT

namespace FrontierSeparation

/-- The set `V(U)` of vertices whose closed cell meets `U`. -/
def meetVerts (cell : ℤ → Set ℂ) (U : Set ℂ) : Set ℤ :=
  {v | (closure (cell v) ∩ U).Nonempty}

/-- The frontier set `V(∂U)` of vertices whose closed cell meets the frontier of `U`. -/
def frontierVerts (cell : ℤ → Set ℂ) (U : Set ℂ) : Set ℤ :=
  {v | (closure (cell v) ∩ frontier U).Nonempty}

/-- A connected set that meets an open set `t` and its complement meets the frontier of `t`. -/
theorem isPreconnected_inter_frontier {s t : Set ℂ} (hs : IsPreconnected s) (ht : IsOpen t)
    (hst₁ : (s ∩ t).Nonempty) (hst₂ : (s \ t).Nonempty) : (s ∩ frontier t).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hfr_of : ∀ z, z ∈ closure t → z ∉ t → z ∈ frontier t := by
    intro z h1 h2
    unfold frontier
    rw [ht.interior_eq]
    exact ⟨h1, h2⟩
  have hsub : s ⊆ t ∪ (closure t)ᶜ := by
    intro z hz
    by_cases hzt : z ∈ t
    · exact Or.inl hzt
    · refine Or.inr fun hzc => ?_
      have hzfr : z ∈ s ∩ frontier t := ⟨hz, hfr_of z hzc hzt⟩
      rw [hcon] at hzfr
      exact hzfr
  obtain ⟨w, hwS, hwt⟩ := hst₂
  have hwc : w ∈ (closure t)ᶜ := by
    intro hwcl
    have hwfr : w ∈ s ∩ frontier t := ⟨hwS, hfr_of w hwcl hwt⟩
    rw [hcon] at hwfr
    exact hwfr
  obtain ⟨z, _, hzt, hzc⟩ := hs t (closure t)ᶜ ht isClosed_closure.isOpen_compl hsub hst₁ ⟨w, hwS, hwc⟩
  exact hzc (subset_closure hzt)

/-- If the first exit time from `A` equals `N`, the path is outside `A` at time `N`. -/
theorem notMem_of_vExitTime_eq {A : Set ℤ} {x : ℕ → ℤ} {N : ℕ} (h : vExitTime A x = N) : x N ∉ A := by
  classical
  unfold vExitTime at h
  split_ifs at h with hex
  · have hfind : Nat.find hex = N := by exact_mod_cast h
    have hs := Nat.find_spec hex
    rw [hfind] at hs
    exact hs
  · exact absurd h (by simp)

/-- **Frontier separation, deterministic core of the printed Lemma 6.7.** A chain `x` that starts at `a` with
closed start cell in `U1`, whose consecutive terms are equal or adjacent, and which first leaves `V(U2)` at
time `N`, visits `V(∂U1)` at some time `n < N`. -/
theorem exists_frontierVerts_before_exit {m : ℤ → ℤ → ℕ} {cell : ℤ → Set ℂ} {U1 U2 : Set ℂ}
    (hU1 : IsOpen U1) (hU12 : U1 ⊆ U2) (hfr : frontier U1 ⊆ U2)
    (hconn : ∀ v, IsPreconnected (cell v)) (hne : ∀ v, (cell v).Nonempty)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (cell u) ∩ closure (cell v)).Nonempty)
    {a : ℤ} (hstart : closure (cell a) ⊆ U1) (x : ℕ → ℤ) (hx0 : x 0 = a)
    (hstep : ∀ n, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0) {N : ℕ}
    (hN : vExitTime (meetVerts cell U2) x = N) :
    ∃ n : ℕ, (n : ℕ∞) < vExitTime (meetVerts cell U2) x ∧ x n ∈ frontierVerts cell U1 := by
  classical
  have hNV : x N ∉ meetVerts cell U2 := notMem_of_vExitTime_eq hN
  have hPN : ¬ closure (cell (x N)) ⊆ U1 := by
    intro hsub
    obtain ⟨z, hz⟩ := hne (x N)
    exact hNV ⟨z, subset_closure hz, hU12 (hsub (subset_closure hz))⟩
  have hex : ∃ i, ¬ closure (cell (x i)) ⊆ U1 := ⟨N, hPN⟩
  obtain ⟨i, hi, hmin⟩ : ∃ i, ¬ closure (cell (x i)) ⊆ U1 ∧ ∀ j < i, closure (cell (x j)) ⊆ U1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_not.1 (Nat.find_min hex hj)⟩
  have hiN : i ≤ N := by
    by_contra h
    exact hPN (hmin N (by omega))
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [hx0] at hi
    exact hi hstart
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hjU : closure (cell (x j)) ⊆ U1 := hmin j (by omega)
  have hp : (closure (cell (x j)) ∩ closure (cell (x (j + 1)))).Nonempty := by
    rcases hstep j with heq | hm
    · rw [heq, Set.inter_self]
      exact (hne (x j)).mono subset_closure
    · exact hadj _ _ hm
  obtain ⟨p, hpj, hpj1⟩ := hp
  have hpU : p ∈ U1 := hjU hpj
  obtain ⟨z, hzS, hzU⟩ := Set.not_subset.1 hi
  obtain ⟨q, hqS, hqfr⟩ :=
    isPreconnected_inter_frontier (hconn (x (j + 1))).closure hU1 ⟨p, hpj1, hpU⟩ ⟨z, hzS, hzU⟩
  have hlt : j + 1 < N := by
    rcases Nat.lt_or_eq_of_le hiN with h | h
    · exact h
    · exfalso
      apply hNV
      rw [← h]
      exact show (closure (cell (x (j + 1))) ∩ U2).Nonempty from ⟨q, hqS, hfr hqfr⟩
  refine ⟨j + 1, ?_, ?_⟩
  · rw [hN]
    exact_mod_cast hlt
  · exact show (closure (cell (x (j + 1))) ∩ frontier U1).Nonempty from ⟨q, hqS, hqfr⟩

/-- Almost surely every step of simple random walk on the multigraph `m` is a stay or an edge. -/
theorem ae_srwStep_legal (m : ℤ → ℤ → ℕ) (a : ℤ) :
    ∀ᵐ x ∂srwLaw m a, ∀ n : ℕ, x (n + 1) = x n ∨ m (x n) (x (n + 1)) ≠ 0 := by
  refine ae_all_iff.2 fun n => ?_
  have h := WalkSteps.srwLaw_nonadjacent_null m n a
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with x hx
  exact not_not.1 hx

/-- **Frontier separation, walk-law form.** Let `hexit` be the almost-sure finiteness of the exit
time from `V(U2)` (the walk exits the finite set `W = V(U2)` almost surely; the printed Lemma 6.7).
Then the walk from `a` almost surely does not avoid `V(∂U1)` before its exit from `V(U2)`. This is the input
`hF` of `TraceFrom68.trace_bound_of_exit_bound`. The hypothesis `hexit` is discharged in the repository by
`ae_vExitTime_ne_top_of_expectedExitTime_ne_top` (OccupationGreen.lean) and
`Audit.StatementsSec3Sec5M1.finite_expectedExitTime`, which cannot be imported in the same file as
`TraceFrom68` (both chains define `MatedCRT.pathShift`). -/
theorem srwLaw_frontier_separation {m : ℤ → ℤ → ℕ} {cell : ℤ → Set ℂ} {U1 U2 : Set ℂ}
    (hU1 : IsOpen U1) (hU12 : U1 ⊆ U2) (hfr : frontier U1 ⊆ U2)
    (hconn : ∀ v, IsPreconnected (cell v)) (hne : ∀ v, (cell v).Nonempty)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (cell u) ∩ closure (cell v)).Nonempty)
    {a : ℤ} (hstart : closure (cell a) ⊆ U1)
    (hexit : ∀ᵐ x ∂srwLaw m a, vExitTime (meetVerts cell U2) x ≠ ⊤) :
    srwLaw m a {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime (meetVerts cell U2) x →
      x n ∉ frontierVerts cell U1} = 0 := by
  have hae : ∀ᵐ x ∂srwLaw m a, x ∉ {x : ℕ → ℤ | ∀ n : ℕ, (n : ℕ∞) < vExitTime (meetVerts cell U2) x →
      x n ∉ frontierVerts cell U1} := by
    filter_upwards [hexit, ae_srwStep_legal m a, srwLaw_ae_start m a] with x hx hs h0 hmem
    obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hx
    obtain ⟨n, hn, hF⟩ :=
      exists_frontierVerts_before_exit hU1 hU12 hfr hconn hne hadj hstart x h0 hs hN.symm
    exact hmem n hn hF
  exact measure_eq_zero_iff_ae_notMem.2 hae

/-- **Printed Lemma 6.7 from 6.8, with frontier separation proved (walk-law form).** The trace bound follows from the
Lemma 6.8 bound at every frontier start `b ∈ V(∂U1)`; the frontier separation is supplied by
`srwLaw_frontier_separation`. -/
theorem trace_bound_of_frontier {m : ℤ → ℤ → ℕ} {cell : ℤ → Set ℂ} {U1 U2 : Set ℂ}
    (hU1 : IsOpen U1) (hU12 : U1 ⊆ U2) (hfr : frontier U1 ⊆ U2)
    (hconn : ∀ v, IsPreconnected (cell v)) (hne : ∀ v, (cell v).Nonempty)
    (hadj : ∀ u v, m u v ≠ 0 → (closure (cell u) ∩ closure (cell v)).Nonempty)
    {a : ℤ} (hstart : closure (cell a) ⊆ U1)
    (hexit : ∀ᵐ x ∂srwLaw m a, vExitTime (meetVerts cell U2) x ≠ ⊤)
    (Θ S' : Set ℤ) {s2 : ℝ} (hs0 : 0 ≤ s2) (hs1 : s2 ≤ 1)
    (hfront : ∀ b ∈ frontierVerts cell U1,
      srwLaw m b {x | ∀ n : ℕ, (n : ℕ∞) < vExitTime (meetVerts cell U2 \ Θ) x → x n ∈ S' \ Θ} ≤
        ENNReal.ofReal (1 - s2)) :
    ENNReal.ofReal s2 ≤ srwLaw m a (TraceFrom68.traceSet (meetVerts cell U2)
      (meetVerts cell U2 \ (S' ∪ Θ))) :=
  TraceFrom68.trace_bound_of_exit_bound m a (meetVerts cell U2) Θ S' (frontierVerts cell U1) hs0 hs1
    (srwLaw_frontier_separation hU1 hU12 hfr hconn hne hadj hstart hexit) hfront

end FrontierSeparation

end MatedCRT

#print axioms MatedCRT.FrontierSeparation.trace_bound_of_frontier
