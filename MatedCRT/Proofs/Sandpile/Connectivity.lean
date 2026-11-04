import MatedCRT.Proofs.Sandpile.Consequences

/-! Connectivity of the positive odometer set and the final sandpile cluster. -/

namespace MatedCRT.Sandpile

open Set Finset Classical

variable {m : ℤ → ℤ → ℕ} {M : ℝ}

/-- The set of vertices which emit mass is preconnected. The component
removal argument follows Leo's proof for obstacle clusters in
`MatedCRT/Proofs/SecA/DiscreteObstacle.lean`. -/
theorem odometer_support_preconnected (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hne : (admissible m M).Nonempty) :
    IsVPreconnected m (Function.support (sandpileNormOdometer m M)) := by
  let u := sandpileNormOdometer m M
  let K := Function.support u
  have hu := normOdometer_mem_admissible hlf hne
  change ((adjGraph m).induce K).Preconnected
  intro x y
  by_contra hxy
  obtain ⟨a₀, hno⟩ : ∃ a₀ : K, ∀ ho : (0 : ℤ) ∈ K,
      ¬ ((adjGraph m).induce K).Reachable ⟨0, ho⟩ a₀ := by
    by_cases hx : ∀ ho : (0 : ℤ) ∈ K, ¬ ((adjGraph m).induce K).Reachable ⟨0, ho⟩ x
    · exact ⟨x, hx⟩
    · push Not at hx
      obtain ⟨ho, hox⟩ := hx
      refine ⟨y, fun ho' hoy => hxy ?_⟩
      exact hox.symm.trans hoy
  let C : Set ℤ := {c | ∃ hc : c ∈ K, ((adjGraph m).induce K).Reachable a₀ ⟨c, hc⟩}
  have hoC : (0 : ℤ) ∉ C := fun ⟨ho, hr⟩ => hno ho hr.symm
  have hclosed : ∀ b ∈ C, ∀ c ∈ K, m b c ≠ 0 → c ∈ C := by
    rintro b ⟨hb, hrb⟩ c hc hbc
    have hne' : b ≠ c := fun e => hbc (by rw [← e]; exact hloop b)
    refine ⟨hc, hrb.trans (SimpleGraph.Adj.reachable ?_)⟩
    rw [SimpleGraph.induce_adj, adjGraph_adj_iff hsymm]
    exact ⟨hne', hbc⟩
  let v : ℤ → ℝ := fun b => if b ∈ C then 0 else u b
  have hvle : ∀ b, v b ≤ u b := by
    intro b
    simp only [v]
    split_ifs
    · exact normOdometer_nonneg hne b
    · exact le_rfl
  have hv : v ∈ admissible m M := by
    refine ⟨fun b => ?_, fun b => ?_⟩
    · simp only [v]
      split_ifs
      · exact le_rfl
      · exact normOdometer_nonneg hne b
    · by_cases hb : b ∈ C
      · have hb0 : b ≠ 0 := fun h => hoC (h ▸ hb)
        have hz : lapSum hlf v b = 0 := by
          unfold lapSum
          apply Finset.sum_eq_zero
          intro c hc
          have hvc : v c = 0 := by
            by_cases hcK : c ∈ K
            · simp [v, hclosed b hb c hcK ((mem_nbrs hlf).1 hc)]
            · have hcu : u c = 0 := by simpa [K, Function.mem_support] using hcK
              simp [v, hcu]
          simp [v, hb, hvc]
        have hΔ : mLaplacian m v b = 0 := by
          rw [mLaplacian_eq_div hlf, hz, zero_div]
        simp only [hΔ, diracZero, ite_eq_right hb0, mul_zero, add_zero]
        exact inv_nonneg.2 (Nat.cast_nonneg _)
      · have hle : lapSum hlf v b ≤ lapSum hlf u b := by
          apply lapSum_le_lapSum hlf (fun c _ => hvle c)
          simp [v, hb]
        have hΔ : mLaplacian m v b ≤ mLaplacian m u b := by
          simp only [mLaplacian_eq_div hlf]
          exact div_le_div_of_nonneg_right hle (Nat.cast_nonneg _)
        have hu' := hu.2 b
        change mLaplacian m u b + (mdeg m 0 : ℝ)⁻¹ * M * diracZero b ≤
          (mdeg m b : ℝ)⁻¹ at hu'
        linarith
  have ha₀C : (a₀ : ℤ) ∈ C := ⟨a₀.2, SimpleGraph.Reachable.refl _⟩
  have hmin := normOdometer_le v hv a₀
  have ha₀u : u a₀ ≠ 0 := a₀.2
  simp only [v, ite_eq_left ha₀C] at hmin
  exact ha₀u (le_antisymm hmin (normOdometer_nonneg hne a₀))

/-- For positive initial mass, the cluster is the closure of the positive
odometer set together with the origin. -/
theorem cluster_eq_insert_closure (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hne : (admissible m M).Nonempty) (hM : 0 < M) :
    sandpileCluster m M = insert 0 (vClosure m (Function.support (sandpileNormOdometer m M))) := by
  let u := sandpileNormOdometer m M
  let K := Function.support u
  have hsub : K ⊆ sandpileCluster m M := by
    intro a ha
    have hpos : 0 < u a := lt_of_le_of_ne (normOdometer_nonneg hne a) (Ne.symm ha)
    change 0 < sandpileFinal m M a
    rw [final_eq_one_of_normOdometer_pos hlf hloop hdeg hne hpos]
    norm_num
  have h0 : (0 : ℤ) ∈ sandpileCluster m M := by
    by_cases hsmall : M ≤ 1
    · rw [cluster_of_mass_le_one hM hsmall]
      simp
    · exact origin_mem_cluster hlf hloop hdeg hne (lt_of_not_ge hsmall)
  apply Set.Subset.antisymm
  · intro a ha
    apply final_support_subset hlf hsymm
    exact ne_of_gt ha
  · intro b hb
    rcases hb with hb | hb
    · simpa only [Set.mem_singleton_iff] using hb ▸ h0
    rcases hb with hbK | hbB
    · exact hsub hbK
    · rcases hbB with ⟨hbK, a, haK, hab⟩
      have hub : u b = 0 := by simpa [K, Function.mem_support] using hbK
      have hua : 0 < u a := lt_of_le_of_ne (normOdometer_nonneg hne a) (Ne.symm haK)
      have hba : m b a ≠ 0 := by rw [hsymm]; exact hab
      have hsum : 0 < lapSum hlf u b := by
        unfold lapSum
        apply Finset.sum_pos'
        · intro c hc
          rw [hub, sub_zero]
          exact mul_nonneg (Nat.cast_nonneg _) (normOdometer_nonneg hne c)
        · refine ⟨a, (mem_nbrs hlf).2 hba, ?_⟩
          rw [hub, sub_zero]
          exact mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hba)) hua
      have hdir : 0 ≤ M * diracZero b := by
        apply mul_nonneg hM.le
        simp [diracZero]; split_ifs <;> norm_num
      change 0 < sandpileFinal m M b
      unfold sandpileFinal
      change 0 < M * diracZero b + (mdeg m b : ℝ) * mLaplacian m u b
      rw [mul_comm (mdeg m b : ℝ), mLaplacian_mul_mdeg hlf]
      linarith

theorem origin_mem_odometer_support (hlf : IsLocallyFiniteMult m)
    (hne : (admissible m M).Nonempty) (hdeg0 : 0 < mdeg m 0) (hM : 1 < M) :
    (0 : ℤ) ∈ Function.support (sandpileNormOdometer m M) := by
  change sandpileNormOdometer m M 0 ≠ 0
  intro hz
  have hsum : 0 ≤ lapSum hlf (sandpileNormOdometer m M) 0 := by
    unfold lapSum
    apply Finset.sum_nonneg
    intro b hb
    rw [hz, sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (normOdometer_nonneg hne b)
  have hlap : 0 ≤ mLaplacian m (sandpileNormOdometer m M) 0 := by
    rw [mLaplacian_eq_div hlf]
    exact div_nonneg hsum (Nat.cast_nonneg _)
  have hf := final_le_one hlf hne hdeg0 0
  simp only [sandpileFinal, diracZero, ite_true, mul_one] at hf
  have hmul := mul_nonneg (Nat.cast_nonneg (mdeg m 0)) hlap
  linarith

/-- For initial mass greater than one, the final cluster is connected. -/
theorem cluster_connected (hlf : IsLocallyFiniteMult m)
    (hsymm : ∀ a b, m a b = m b a) (hloop : ∀ a, m a a = 0)
    (hdeg : ∀ a, 0 < mdeg m a) (hne : (admissible m M).Nonempty) (hM : 1 < M) :
    IsVConnected m (sandpileCluster m M) := by
  let K := Function.support (sandpileNormOdometer m M)
  let D := sandpileCluster m M
  have h0K : (0 : ℤ) ∈ K := origin_mem_odometer_support hlf hne (hdeg 0) hM
  have heq : D = vClosure m K := by
    change sandpileCluster m M = vClosure m K
    rw [cluster_eq_insert_closure hlf hsymm hloop hdeg hne (by linarith : 0 < M)]
    exact Set.insert_eq_of_mem (Or.inl h0K)
  have hKD : K ⊆ D := fun a ha => heq.symm ▸ Or.inl ha
  have hKP := odometer_support_preconnected hlf hsymm hloop hne
  have hnear : ∀ x : D, ∃ a : K, ((adjGraph m).induce D).Reachable x ⟨a, hKD a.2⟩ := by
    intro x
    have hx : (x : ℤ) ∈ vClosure m K := heq ▸ x.2
    rcases hx with hxK | hxB
    · exact ⟨⟨x, hxK⟩, SimpleGraph.Reachable.refl _⟩
    · rcases hxB with ⟨hxK, a, haK, hax⟩
      have hxa : m (x : ℤ) a ≠ 0 := by rw [hsymm]; exact hax
      have hne' : (x : ℤ) ≠ a := fun e => hxK (e ▸ haK)
      refine ⟨⟨a, haK⟩, SimpleGraph.Adj.reachable ?_⟩
      rw [SimpleGraph.induce_adj, adjGraph_adj_iff hsymm]
      exact ⟨hne', hxa⟩
  change ((adjGraph m).induce D).Connected
  let : Nonempty D := ⟨⟨0, hKD h0K⟩⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨a, hxa⟩ := hnear x
  obtain ⟨b, hyb⟩ := hnear y
  have hab := (hKP a b).map ((adjGraph m).induceHomOfLE hKD).toHom
  exact hxa.trans (hab.trans hyb.symm)

end MatedCRT.Sandpile
