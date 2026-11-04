import MatedCRT.Proofs.Sandpile.Dirichlet
import MatedCRT.Proofs.Sandpile.Witness
import MatedCRT.Proofs.SecA.Statements

/-! Finite graph balls for the sandpile obstacle construction. -/

namespace MatedCRT.Sandpile

open Set Classical

variable {m : ℤ → ℤ → ℕ}

/-- The graph ball obtained by successively adjoining neighboring vertices. -/
def graphBall (m : ℤ → ℤ → ℕ) : ℕ → Set ℤ
  | 0 => {0}
  | n + 1 => vClosure m (graphBall m n)

theorem graphBall_step_subset (n : ℕ) : graphBall m n ⊆ graphBall m (n + 1) :=
  fun _ ha => Or.inl ha

theorem graphBall_mono {n k : ℕ} (h : n ≤ k) : graphBall m n ⊆ graphBall m k := by
  induction h with
  | refl => exact Subset.rfl
  | @step k hk ih => exact ih.trans (graphBall_step_subset k)

theorem graphBall_neighbor {n : ℕ} {a b : ℤ} (ha : a ∈ graphBall m n)
    (hab : m a b ≠ 0) : b ∈ graphBall m (n + 1) := by
  by_cases hb : b ∈ graphBall m n
  · exact Or.inl hb
  · exact Or.inr ⟨hb, a, ha, hab⟩

theorem graphBall_finite (hlf : IsLocallyFiniteMult m) (n : ℕ) : (graphBall m n).Finite := by
  induction n with
  | zero => exact Set.finite_singleton _
  | succ n ih =>
    apply ih.union
    exact (ih.biUnion fun a _ => hlf a).subset (by
      rintro b ⟨_, ⟨a, ha, hab⟩⟩
      exact mem_biUnion ha hab)

theorem graphBall_connected (hsymm : ∀ a b, m a b = m b a)
    (hloop : ∀ a, m a a = 0) (n : ℕ) : IsVConnected m (graphBall m n) := by
  induction n with
  | zero =>
    let : Nonempty (graphBall m 0) := ⟨⟨0, by simp [graphBall]⟩⟩
    refine ⟨?_⟩
    intro a b
    have ha : (a : ℤ) = 0 := by simpa [graphBall] using a.2
    have hb : (b : ℤ) = 0 := by simpa [graphBall] using b.2
    have : a = b := Subtype.ext (ha.trans hb.symm)
    subst b
    exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    let A := graphBall m n
    let B := graphBall m (n + 1)
    have hAB : A ⊆ B := graphBall_step_subset n
    let f : (adjGraph m).induce A →g (adjGraph m).induce B :=
      ((adjGraph m).induceHomOfLE hAB).toHom
    have hreach : ∀ x : B, ∃ y : A, ((adjGraph m).induce B).Reachable (f y) x := by
      intro x
      rcases x.2 with hx | ⟨hx, y, hy, hyx⟩
      · exact ⟨⟨x, hx⟩, SimpleGraph.Reachable.refl _⟩
      · refine ⟨⟨y, hy⟩, SimpleGraph.Adj.reachable ?_⟩
        rw [SimpleGraph.induce_adj, adjGraph_adj_iff hsymm]
        change y ≠ (x : ℤ) ∧ m y x ≠ 0
        exact ⟨fun e => hyx (by rw [e]; exact hloop _), hyx⟩
    let : Nonempty B := ⟨⟨0, graphBall_mono (Nat.zero_le _) (by simp [graphBall])⟩⟩
    refine ⟨?_⟩
    intro x y
    obtain ⟨x', hx⟩ := hreach x
    obtain ⟨y', hy⟩ := hreach y
    exact hx.symm.trans (((ih.1 x' y').map f).trans hy)

theorem finite_connected_boundary_nonempty (hsymm : ∀ a b, m a b = m b a)
    (hconn : IsVConnected m Set.univ) {V : Set ℤ} (hV : V.Finite) (h0 : (0 : ℤ) ∈ V) :
    (vBoundary m V).Nonempty := by
  by_contra hbd
  have hclosed : ∀ a ∈ V, ∀ b, m a b ≠ 0 → b ∈ V := by
    intro a ha b hab
    by_contra hb
    exact hbd ⟨b, hb, a, ha, hab⟩
  have hall : V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    have hr := hconn.1 ⟨0, Set.mem_univ _⟩ ⟨b, Set.mem_univ _⟩
    exact propagate_reachable hsymm (A := Set.univ) (fun x => x ∈ V)
      (fun a _ b _ hab ha => hclosed a ha b hab) hr h0
  exact Set.infinite_univ (hall ▸ hV)

/-- A walk of length `k` from a ball of radius `n` ends in the ball of
radius `n + k`. -/
theorem walk_mem_graphBall (hsymm : ∀ a b, m a b = m b a) {a b : ℤ}
    (p : (adjGraph m).Walk a b) {n : ℕ} (ha : a ∈ graphBall m n) :
    b ∈ graphBall m (n + p.length) := by
  induction p generalizing n with
  | nil => simpa using ha
  | @cons a b c hab p ih =>
    have hb : b ∈ graphBall m (n + 1) := graphBall_neighbor ha ((adjGraph_adj_iff hsymm).1 hab).2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hb

/-- A finite preconnected set containing the origin lies in the graph ball
whose radius is its cardinality. -/
theorem preconnected_subset_graphBall (hsymm : ∀ a b, m a b = m b a)
    {K : Set ℤ} (hK : K.Finite) (hconn : IsVPreconnected m K) (h0 : (0 : ℤ) ∈ K) :
    K ⊆ graphBall m K.ncard := by
  let := hK.fintype
  intro a ha
  obtain ⟨p, hp⟩ := (hconn ⟨0, h0⟩ ⟨a, ha⟩).exists_isPath
  have hlen : p.length < K.ncard := by
    rw [← Set.fintypeCard_eq_ncard]
    exact hp.length_lt
  let f : (adjGraph m).induce K →g adjGraph m := ⟨Subtype.val, fun h => h⟩
  have hf0 : f ⟨0, h0⟩ ∈ graphBall m 0 := by change (0 : ℤ) ∈ graphBall m 0; simp [graphBall]
  have hwalk := walk_mem_graphBall hsymm (p.map f) (n := 0) hf0
  change a ∈ graphBall m (0 + (p.map f).length) at hwalk
  rw [SimpleGraph.Walk.length_map, Nat.zero_add] at hwalk
  apply graphBall_mono (Nat.le_of_lt hlen)
  exact hwalk

theorem graphBall_subset_interior_succ (n : ℕ) :
    graphBall m n ⊆ vInterior m (graphBall m (n + 1)) := by
  intro a ha
  exact ⟨graphBall_step_subset n ha, fun _ hab => graphBall_neighbor ha hab⟩

/-- On an infinite connected locally finite multigraph, every finite mass
has a finite-support admissible stabilizer. -/
theorem exists_finite_stabilizer (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hconn : IsVConnected m Set.univ) (M : ℝ) :
    ∃ v : ℤ → ℝ, v ∈ admissible m M ∧ (Function.support v).Finite := by
  by_cases hsmall : M ≤ 1
  · exact ⟨0, zero_admissible hsmall, by simp⟩
  have hM : 1 < M := lt_of_not_ge hsmall
  obtain ⟨N, hN⟩ := exists_nat_gt M
  let V := graphBall m (N + 1)
  have hV : V.Finite := graphBall_finite hlf _
  have h0 : (0 : ℤ) ∈ V := graphBall_mono (Nat.zero_le _) (by simp [graphBall])
  have hbd := finite_connected_boundary_nonempty hsymm hconn hV h0
  obtain ⟨φ, hS⟩ := exists_point_source_obstacle hlf hsymm hloop hdeg hV
    (graphBall_connected hsymm hloop _) hbd h0 (by linarith : 0 < M)
  let r : ℤ → ℝ := fun a => (mdeg m a : ℝ)⁻¹
  let K := obstacleCluster m V r φ
  have hKfin : K.Finite := hS.cluster_finite
  have hKconn : IsVPreconnected m K := hS.cluster_preconnected
  have hd : (0 : ℝ) < (mdeg m 0 : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hdeg 0)
  have hK0 : (0 : ℤ) ∈ K := hS.origin_mem_cluster (by nlinarith)
  have hcard : (K.ncard : ℝ) ≤ M := by
    have h := obstacleClusterCardStep ℤ m V 0 r φ ((mdeg m 0 : ℝ)⁻¹ * M) hS
      (fun _ _ => rfl)
    have hd0 : (mdeg m 0 : ℝ) ≠ 0 := by exact_mod_cast (hdeg 0).ne'
    dsimp [K, r] at h ⊢
    calc
      _ ≤ (mdeg m 0 : ℝ)⁻¹ * M * (mdeg m 0 : ℝ) := h
      _ = M := by field_simp
  have hcardN : K.ncard ≤ N := by exact_mod_cast (le_of_lt (lt_of_le_of_lt hcard hN))
  have hsub : K ⊆ vInterior m V :=
    (preconnected_subset_graphBall hsymm hKfin hKconn hK0).trans
      ((graphBall_mono hcardN).trans (graphBall_subset_interior_succ N))
  exact finite_witness_of_obstacle_interior hS hsub

end MatedCRT.Sandpile
