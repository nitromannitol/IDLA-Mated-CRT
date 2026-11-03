import MatedCRT.Proofs.WalkPotential.MaximumPrinciple

/-!
# Greedy increasing paths (proof of Lemma 7.4, lines 3073-3085)

Deterministic part of the proof of Lemma 7.4 (Levine-Peres 2009, Lemma 4.2), on any multigraph `m : α → α → ℕ`:

* `exists_nbr_add_inv_le`: if `Δu(a) = deg(a)⁻¹` and `a` has a neighbour, a neighbour `b` maximizing `u` satisfies
  `u(b) ≥ u(a) + deg(a)⁻¹` (`u(b) ≥ deg(a)⁻¹ ∑_{c ∼ a} m(a,c) u(c) = u(a) + Δu(a)`, lines 3080-3082);
* `exists_vPath_chain`: on a finite set `Λ ∋ o`, if from every `a ∈ Λ \ {o}` some neighbour `b ∈ Λ` has
  `u(b) ≥ u(a) + δ`, `δ > 0`, then every `a ∈ Λ` is joined to `o` by a path in `Λ` along which `u` increases by at
  least `δ` at each step (the increasing chain cannot cycle in the finite set `Λ`, so it reaches `o`, line 3085).
-/

namespace MatedCRT

open Set

variable {α : Type*} {m : α → α → ℕ}

/-- **The greedy step** (lines 3080-3082). -/
theorem exists_nbr_add_inv_le (hlf : IsLocallyFiniteMult m) {u : α → ℝ} {a b₀ : α} (hab₀ : m a b₀ ≠ 0)
    (hL : mLaplacian m u a = ((mdeg m a : ℕ) : ℝ)⁻¹) :
    ∃ b, m a b ≠ 0 ∧ u a + ((mdeg m a : ℕ) : ℝ)⁻¹ ≤ u b := by
  have hD : (0 : ℝ) < (mdeg m a : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mdeg_ne_zero_of_ne_zero hlf hab₀)
  obtain ⟨b, hb, hbmax⟩ := Finset.exists_max_image (nbrs hlf a) u ⟨b₀, (mem_nbrs hlf).2 hab₀⟩
  have h1 := mLaplacian_mul_mdeg hlf u a
  rw [hL, inv_mul_cancel₀ hD.ne'] at h1
  unfold lapSum at h1
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← mdeg_cast_eq hlf a] at h1
  have hle : ∑ d ∈ nbrs hlf a, (m a d : ℝ) * u d ≤ (mdeg m a : ℝ) * u b := by
    rw [mdeg_cast_eq hlf a, Finset.sum_mul]
    exact Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_left (hbmax d hd) (Nat.cast_nonneg _)
  refine ⟨b, (mem_nbrs hlf).1 hb, ?_⟩
  have key : (mdeg m a : ℝ) * (u a + ((mdeg m a : ℕ) : ℝ)⁻¹) ≤ (mdeg m a : ℝ) * u b := by
    rw [mul_add, mul_inv_cancel₀ hD.ne']
    linarith
  exact le_of_mul_le_mul_left key hD

/-- **Increasing paths to `o`** (line 3085): the greedy chain terminates at `o` in the finite set `Λ`. -/
theorem exists_vPath_chain {Λ : Set α} (hΛ : Λ.Finite) {u : α → ℝ} {δ : ℝ} (hδ : 0 < δ) {o : α}
    (hstep : ∀ a ∈ Λ, a ≠ o → ∃ b ∈ Λ, m a b ≠ 0 ∧ u a + δ ≤ u b) :
    ∀ a ∈ Λ, ∃ p : List α, IsVPathIn m Λ p a o ∧ p.IsChain fun c d => u c + δ ≤ u d := by
  classical
  have hbase : ∀ {a}, a ∈ Λ → ∃ p : List α, IsVPathIn m Λ p a a ∧ p.IsChain fun c d => u c + δ ≤ u d :=
    fun {a} ha => ⟨[a], ⟨rfl, rfl, by simpa using ha, List.isChain_singleton _⟩, List.isChain_singleton _⟩
  have key : ∀ n : ℕ, ∀ a ∈ Λ, (hΛ.toFinset.filter fun c => u a < u c).card ≤ n →
      ∃ p : List α, IsVPathIn m Λ p a o ∧ p.IsChain fun c d => u c + δ ≤ u d := by
    intro n
    induction n with
    | zero =>
      intro a ha hcard
      by_cases hao : a = o
      · rw [hao] at ha ⊢
        exact hbase ha
      · exfalso
        obtain ⟨b, hb, -, hab⟩ := hstep a ha hao
        have hbin : b ∈ hΛ.toFinset.filter fun c => u a < u c :=
          Finset.mem_filter.2 ⟨hΛ.mem_toFinset.2 hb, by linarith⟩
        have := Finset.card_pos.2 ⟨b, hbin⟩
        omega
    | succ n ih =>
      intro a ha hcard
      by_cases hao : a = o
      · rw [hao] at ha ⊢
        exact hbase ha
      · obtain ⟨b, hb, hmab, hab⟩ := hstep a ha hao
        have hsub : (hΛ.toFinset.filter fun c => u b < u c) ⊆ hΛ.toFinset.filter fun c => u a < u c := by
          intro c hc
          rw [Finset.mem_filter] at hc ⊢
          exact ⟨hc.1, by linarith [hc.2]⟩
        have hbin : b ∈ hΛ.toFinset.filter fun c => u a < u c :=
          Finset.mem_filter.2 ⟨hΛ.mem_toFinset.2 hb, by linarith⟩
        have hbout : b ∉ hΛ.toFinset.filter fun c => u b < u c := by simp
        have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h => hbout (h ▸ hbin)⟩)
        obtain ⟨p, ⟨hph, hpl, hpΛ, hpm⟩, hpc⟩ := ih b hb (by omega)
        obtain ⟨p', rfl⟩ : ∃ p', p = b :: p' := by
          cases p with
          | nil => simp at hph
          | cons c p' =>
            simp only [List.head?_cons, Option.some.injEq] at hph
            exact ⟨p', by rw [hph]⟩
        refine ⟨a :: b :: p', ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
        · simpa using hpl
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact ha
          · exact hpΛ c hc
        · exact List.isChain_cons_cons.2 ⟨hmab, hpm⟩
        · exact List.isChain_cons_cons.2 ⟨hab, hpc⟩
  intro a ha
  exact key _ a ha le_rfl

end MatedCRT
