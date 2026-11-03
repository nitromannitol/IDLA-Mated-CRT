import MatedCRT.Defs.Map

/-!
# Discrete potential theory on locally finite multigraphs

Infrastructure for Appendix A and the discrete results of Section 2: for a symmetric, locally finite edge
multiplicity `m : α → α → ℕ`,

* `nbrs hlf a`: the (finite) set of neighbours of `a`;
* `lapSum hlf u a = ∑_{b ∼ a} m(a,b) (u(b) - u(a))`, so that `Δu(a) · deg(a) = lapSum u a` (`mLaplacian_mul_mdeg`);
* the discrete Gauss-Green identity on a finite set `s`: `∑_{a ∈ s} lapSum u a` is the flux through the edges leaving
  `s` (`sum_lapSum_eq_flux`);
* the minimum principle on a finite connected set with nonempty boundary (`nonneg_of_lapSum_nonpos`).
-/

namespace MatedCRT

open Set Finset Classical

variable {α : Type*} {m : α → α → ℕ}

/-- The edge multiplicity is locally finite: every vertex has finitely many neighbours. -/
def IsLocallyFiniteMult (m : α → α → ℕ) : Prop :=
  ∀ a, {b | m a b ≠ 0}.Finite

section LocallyFinite

variable (hlf : IsLocallyFiniteMult m)

/-- The finite set of neighbours of `a`. -/
noncomputable def nbrs (a : α) : Finset α :=
  (hlf a).toFinset

theorem mem_nbrs {a b : α} : b ∈ nbrs hlf a ↔ m a b ≠ 0 := by
  simp [nbrs]

/-- `∑_{b ∼ a} m(a,b) (u(b) - u(a))`. -/
noncomputable def lapSum (u : α → ℝ) (a : α) : ℝ :=
  ∑ b ∈ nbrs hlf a, (m a b : ℝ) * (u b - u a)

theorem support_subset_nbrs (a : α) (F : α → ℝ) :
    Function.support (fun b => (m a b : ℝ) * F b) ⊆ ↑(nbrs hlf a) := by
  intro b hb
  rw [Finset.mem_coe, mem_nbrs]
  intro h
  apply hb
  simp [h]

theorem finsum_mul_eq_sum_nbrs (a : α) (F : α → ℝ) :
    ∑ᶠ b, (m a b : ℝ) * F b = ∑ b ∈ nbrs hlf a, (m a b : ℝ) * F b :=
  finsum_eq_sum_of_support_subset _ (support_subset_nbrs hlf a F)

theorem mdeg_eq_sum_nbrs (a : α) : mdeg m a = ∑ b ∈ nbrs hlf a, m a b := by
  unfold mdeg
  refine finsum_eq_sum_of_support_subset _ ?_
  intro b hb
  rw [Finset.mem_coe, mem_nbrs]
  exact hb

theorem mdeg_cast_eq (a : α) : (mdeg m a : ℝ) = ∑ b ∈ nbrs hlf a, (m a b : ℝ) := by
  rw [mdeg_eq_sum_nbrs hlf a]
  push_cast
  rfl

theorem nbrs_eq_empty_of_mdeg_eq_zero {a : α} (h : mdeg m a = 0) : nbrs hlf a = ∅ := by
  rw [mdeg_eq_sum_nbrs hlf a, Finset.sum_eq_zero_iff] at h
  refine Finset.eq_empty_of_forall_notMem fun b hb => ?_
  exact (mem_nbrs hlf).1 hb (h b hb)

theorem lapSum_eq_zero_of_mdeg_eq_zero {a : α} (h : mdeg m a = 0) (u : α → ℝ) : lapSum hlf u a = 0 := by
  simp [lapSum, nbrs_eq_empty_of_mdeg_eq_zero hlf h]

/-- `Δu(a) · deg(a) = ∑_{b ∼ a} m(a,b) (u(b) - u(a))`. -/
theorem mLaplacian_mul_mdeg (u : α → ℝ) (a : α) :
    mLaplacian m u a * (mdeg m a : ℝ) = lapSum hlf u a := by
  unfold mLaplacian
  rw [finsum_mul_eq_sum_nbrs hlf a (fun b => u b - u a)]
  by_cases h : mdeg m a = 0
  · have := lapSum_eq_zero_of_mdeg_eq_zero hlf h u
    simp only [lapSum] at this
    simp only [lapSum, this, h, Nat.cast_zero, mul_zero]
  · have h' : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast h
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ h', one_mul]
    rfl

theorem mLaplacian_eq_div (u : α → ℝ) (a : α) :
    mLaplacian m u a = lapSum hlf u a / (mdeg m a : ℝ) := by
  by_cases h : mdeg m a = 0
  · simp [mLaplacian, h]
  · have h' : (mdeg m a : ℝ) ≠ 0 := by exact_mod_cast h
    rw [← mLaplacian_mul_mdeg hlf u a, mul_div_cancel_right₀ _ h']

theorem mLaplacian_le_of_lapSum_le {u : α → ℝ} {a : α} {r : ℝ} (hr : 0 ≤ r)
    (h : lapSum hlf u a ≤ r * (mdeg m a : ℝ)) : mLaplacian m u a ≤ r := by
  rw [mLaplacian_eq_div hlf]
  rcases Nat.eq_zero_or_pos (mdeg m a) with h0 | h0
  · simp [h0, hr]
  · have : (0 : ℝ) < mdeg m a := by exact_mod_cast h0
    rw [div_le_iff₀ this]
    exact h

theorem lapSum_le_of_mLaplacian_le {u : α → ℝ} {a : α} {r : ℝ} (h : mLaplacian m u a ≤ r) :
    lapSum hlf u a ≤ r * (mdeg m a : ℝ) := by
  rw [← mLaplacian_mul_mdeg hlf]
  exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)

theorem lapSum_sub (u v : α → ℝ) (a : α) :
    lapSum hlf (fun b => u b - v b) a = lapSum hlf u a - lapSum hlf v a := by
  simp only [lapSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Monotonicity: if `u ≤ v` at the neighbours of `a` and `u(a) = v(a)`... in the general form
`lapSum u a - lapSum v a = ∑ m(a,b)(u b - v b) - deg(a)(u a - v a)`. -/
theorem lapSum_le_lapSum {u v : α → ℝ} {a : α} (hb : ∀ b ∈ nbrs hlf a, u b ≤ v b) (ha : v a ≤ u a) :
    lapSum hlf u a ≤ lapSum hlf v a := by
  unfold lapSum
  refine Finset.sum_le_sum fun b hbm => ?_
  exact mul_le_mul_of_nonneg_left (by linarith [hb b hbm]) (Nat.cast_nonneg _)

theorem lapSum_zero (a : α) : lapSum hlf (fun _ => (0 : ℝ)) a = 0 := by
  simp [lapSum]

/-- The neighbours of a vertex of `V` lie in `cl(V)`. -/
theorem mem_vClosure_of_mem_nbrs {V : Set α} {a b : α} (ha : a ∈ V) (hb : b ∈ nbrs hlf a) :
    b ∈ vClosure m V := by
  by_cases hbV : b ∈ V
  · exact Or.inl hbV
  · exact Or.inr ⟨hbV, a, ha, (mem_nbrs hlf).1 hb⟩

end LocallyFinite

section Symmetric

variable (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)

include hsymm in
/-- On a finite set `s`, the edges inside `s` cancel: `∑_{a ∈ s} ∑_{b ∈ s} m(a,b) (u(b) - u(a)) = 0`. -/
theorem sum_sum_inner_eq_zero (s : Finset α) (u : α → ℝ) :
    ∑ a ∈ s, ∑ b ∈ s, (m a b : ℝ) * (u b - u a) = 0 := by
  have h1 := Finset.sum_comm (s := s) (t := s) (f := fun a b => (m a b : ℝ) * (u b - u a))
  have h2 : ∑ b ∈ s, ∑ a ∈ s, (m a b : ℝ) * (u b - u a) =
      -∑ a ∈ s, ∑ b ∈ s, (m a b : ℝ) * (u b - u a) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsymm a b]
    ring
  linarith

/-- For `a` and a finite set `s`, the sum over the neighbours of `a` lying in `s` equals the sum over `s`. -/
theorem sum_nbrs_filter_mem (s : Finset α) (u : α → ℝ) (a : α) :
    ∑ b ∈ (nbrs hlf a).filter (· ∈ s), (m a b : ℝ) * (u b - u a) = ∑ b ∈ s, (m a b : ℝ) * (u b - u a) := by
  rw [Finset.filter_mem_eq_inter]
  refine Finset.sum_subset Finset.inter_subset_right fun b hbs hb => ?_
  have : m a b = 0 := by
    by_contra h
    exact hb (Finset.mem_inter.2 ⟨(mem_nbrs hlf).2 h, hbs⟩)
  simp [this]

include hsymm in
/-- **Discrete Gauss-Green identity.** On a finite set `s`, `∑_{a ∈ s} lapSum u a` equals the flux
`∑_{a ∈ s} ∑_{b ∼ a, b ∉ s} m(a,b) (u(b) - u(a))` through the edges leaving `s`. -/
theorem sum_lapSum_eq_flux (s : Finset α) (u : α → ℝ) :
    ∑ a ∈ s, lapSum hlf u a =
      ∑ a ∈ s, ∑ b ∈ (nbrs hlf a).filter (· ∉ s), (m a b : ℝ) * (u b - u a) := by
  have hsplit : ∀ a, lapSum hlf u a =
      ∑ b ∈ (nbrs hlf a).filter (· ∈ s), (m a b : ℝ) * (u b - u a) +
        ∑ b ∈ (nbrs hlf a).filter (· ∉ s), (m a b : ℝ) * (u b - u a) := by
    intro a
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  simp_rw [hsplit, Finset.sum_add_distrib, sum_nbrs_filter_mem hlf s u,
    sum_sum_inner_eq_zero hsymm s u, zero_add]

end Symmetric

section MinimumPrinciple

variable (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)

include hsymm in
/-- Adjacency in `adjGraph m` for a symmetric multiplicity. -/
theorem adjGraph_adj_iff {a b : α} : (adjGraph m).Adj a b ↔ a ≠ b ∧ m a b ≠ 0 := by
  unfold adjGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1, by rwa [hsymm]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inl h2⟩

include hsymm in
/-- A property of vertices of `A` which passes to every neighbour in `A` holds on the whole connected component, i.e.
at every vertex reachable in the induced subgraph. -/
theorem propagate_reachable {A : Set α} (Q : α → Prop)
    (hstep : ∀ x ∈ A, ∀ y ∈ A, m x y ≠ 0 → Q x → Q y) {x y : A}
    (hr : ((adjGraph m).induce A).Reachable x y) (hx : Q x) : Q y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact hx
  | tail _ hadj ih =>
    rw [SimpleGraph.induce_adj, adjGraph_adj_iff hsymm] at hadj
    exact hstep _ (Subtype.prop _) _ (Subtype.prop _) hadj.2 ih

include hsymm in
/-- **Minimum principle.** Let `V` be a finite connected vertex set with nonempty boundary and `v` superharmonic on `V`
(`lapSum v ≤ 0`) with `v ≥ 0` on `∂V`. Then `v ≥ 0` on `V`. -/
theorem nonneg_of_lapSum_nonpos {V : Set α} (hV : V.Finite) (hconn : IsVConnected m V)
    (hbd : (vBoundary m V).Nonempty) {v : α → ℝ} (hsup : ∀ a ∈ V, lapSum hlf v a ≤ 0)
    (hb : ∀ b ∈ vBoundary m V, 0 ≤ v b) : ∀ a ∈ V, 0 ≤ v a := by
  by_contra hneg
  push Not at hneg
  obtain ⟨a₁, ha₁V, ha₁⟩ := hneg
  obtain ⟨a₀, ha₀, hmin⟩ := hV.toFinset.exists_min_image v ⟨a₁, hV.mem_toFinset.2 ha₁V⟩
  rw [Set.Finite.mem_toFinset] at ha₀
  have hmin' : ∀ x ∈ V, v a₀ ≤ v x := fun x hx => hmin x (hV.mem_toFinset.2 hx)
  have hneg0 : v a₀ < 0 := lt_of_le_of_lt (hmin' a₁ ha₁V) ha₁
  -- a minimizer has all its neighbours in `V`, with the same value
  have hstep : ∀ x ∈ V, v x = v a₀ → ∀ y, m x y ≠ 0 → y ∈ V ∧ v y = v a₀ := by
    intro x hx hxv y hy
    have hterm : ∀ b ∈ nbrs hlf x, 0 ≤ (m x b : ℝ) * (v b - v x) := by
      intro b hbm
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      rcases mem_vClosure_of_mem_nbrs hlf hx hbm with hbV | hbB
      · linarith [hmin' b hbV]
      · linarith [hb b hbB]
    have hsum0 : ∑ b ∈ nbrs hlf x, (m x b : ℝ) * (v b - v x) = 0 :=
      le_antisymm (hsup x hx) (Finset.sum_nonneg hterm)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hsum0 y ((mem_nbrs hlf).2 hy)
    have hmpos : (m x y : ℝ) ≠ 0 := by exact_mod_cast hy
    have hvy : v y = v x := by
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h hmpos
      · linarith
    refine ⟨?_, by rw [hvy, hxv]⟩
    by_contra hyV
    have := hb y ⟨hyV, x, hx, hy⟩
    linarith
  -- every vertex of `V` is a minimizer, and `V` is closed under adjacency
  have hall : ∀ c ∈ V, v c = v a₀ := by
    intro c hc
    have hr := hconn.preconnected ⟨a₀, ha₀⟩ ⟨c, hc⟩
    exact propagate_reachable hsymm (A := V) (fun z => v z = v a₀)
      (fun x hx y _ hxy hQ => (hstep x hx hQ y hxy).2) hr rfl
  obtain ⟨b, hbV, x, hx, hxb⟩ := hbd
  exact hbV (hstep x hx (hall x hx) b hxb).1

end MinimumPrinciple

end MatedCRT
